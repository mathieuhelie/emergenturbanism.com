/*
 * The Complex Grid — an embeddable SVG simulation.
 *
 * Implements the growth procedure from "The complex grid" (Emergent Urbanism,
 * 16 Feb 2009):
 *
 *   Private rule   — you may build on any available part of the network so long
 *                    as you replace the part you used up by extending the network
 *                    around your new block. Each block is placed where it adds
 *                    the fewest new street segments (the lowest private cost).
 *
 *   Community rule — any time a part of the network becomes too complicated
 *                    (it takes more than N steps to get out of a sector), extend
 *                    the boundary of that part with a higher capacity road.
 *
 * The grid stays gridlike at every scale. Growth proceeds as one compact
 * cluster at a time; when it becomes too complicated it is ringed by a
 * boulevard around its bounding rectangle, and that sector then acts as a
 * single block in the next scale up, where the same two rules make ring
 * roads, then parkways. Every road is a rectangle that cuts through no block
 * and joins the roads of its own level. Streets may not grow too long without
 * interruption, so clusters stay roughly square. Land left unbuilt inside a
 * ring is open space.
 *
 * Block sizes are drawn from the Fibonacci sequence, standing in for a random
 * growth process, and grow in scale as the settlement climbs the hierarchy
 * (village -> town -> city -> metropolis).
 *
 * Usage:
 *   <div class="complex-grid" data-seed="7" data-blocks="200" data-steps="3"></div>
 *   <script src="/complex-grid/complex-grid.js"></script>
 *
 * Options (data-* attributes, all optional):
 *   data-seed      random seed (integer)                         default: random
 *   data-blocks    number of blocks to grow                      default: 200
 *   data-steps     max steps to get out of a sector; lower means default: 3
 *                  smaller sectors and an earlier ring road
 *   data-speed     milliseconds between blocks                   default: 100
 *   data-autoplay  "false" to show the finished city instead      default: true
 *   data-controls  "false" to hide the control bar               default: true
 *
 * Or programmatically: ComplexGrid.mount(element, options)
 * The simulation alone is exposed as ComplexGrid.Simulation for reuse.
 */
(function (global) {
  'use strict';

  var SVGNS = 'http://www.w3.org/2000/svg';
  var FIB = [1, 2, 3, 5, 8, 13];
  var MAX_LEVEL = 4;
  var STAGES = ['Village', 'Town', 'City', 'Metropolis', 'Region'];
  var ROAD_NAMES = ['Lane', 'Boulevard', 'Ring road', 'Parkway', 'Highway'];

  // Small, fast, seedable PRNG (mulberry32).
  function rng(seed) {
    var a = seed >>> 0;
    return function () {
      a = (a + 0x6D2B79F5) >>> 0;
      var t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function cellKey(x, y) { return x + ',' + y; }
  // Unit street segments: horizontal edge from (x,y) to (x+1,y), vertical from (x,y) to (x,y+1).
  function hKey(x, y) { return 'h' + x + ',' + y; }
  function vKey(x, y) { return 'v' + x + ',' + y; }

  /* ------------------------------------------------------------------ */
  /* Simulation                                                          */
  /* ------------------------------------------------------------------ */

  function Simulation(opts) {
    opts = opts || {};
    this.seed = opts.seed != null ? opts.seed : Math.floor(Math.random() * 1e9);
    this.steps = opts.steps || 3;
    this.random = rng(this.seed);
    this.blocks = [];      // {id, x, y, w, h}
    this.cells = {};       // "x,y" -> block id
    this.edges = {};       // edge key -> road level (0 = lane)
    this.enclosures = [];  // {x0, y0, x1, y1, level}: sectors ringed by a road
    this.level = 0;        // highest road level built so far
    this.events = [];      // community-rule enclosures, for the log
    this.bbox = { x0: 0, y0: 0, x1: 0, y1: 0 };
  }

  function rect(x, y, w, h) { return { x0: x, y0: y, x1: x + w, y1: y + h }; }
  function meets(a, b) { return a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1; }
  function within(a, b) { return a.x0 >= b.x0 && a.x1 <= b.x1 && a.y0 >= b.y0 && a.y1 <= b.y1; }
  function union(a, b) {
    if (!a) return { x0: b.x0, y0: b.y0, x1: b.x1, y1: b.y1 };
    return { x0: Math.min(a.x0, b.x0), y0: Math.min(a.y0, b.y0), x1: Math.max(a.x1, b.x1), y1: Math.max(a.y1, b.y1) };
  }
  // Rectangles sharing a stretch of boundary (not just a corner).
  function abut(a, b) {
    var ox = Math.min(a.x1, b.x1) - Math.max(a.x0, b.x0), oy = Math.min(a.y1, b.y1) - Math.max(a.y0, b.y0);
    return ((a.x1 === b.x0 || b.x1 === a.x0) && oy > 0) || ((a.y1 === b.y0 || b.y1 === a.y0) && ox > 0);
  }
  function blockRect(B) { return rect(B.x, B.y, B.w, B.h); }

  // Perimeter unit edges of a rectangle, each with the outside neighbour cell.
  function perimeter(r) {
    var out = [], i, w = r.x1 - r.x0, h = r.y1 - r.y0;
    for (i = 0; i < w; i++) {
      out.push({ k: hKey(r.x0 + i, r.y0), nx: r.x0 + i, ny: r.y0 - 1 });
      out.push({ k: hKey(r.x0 + i, r.y1), nx: r.x0 + i, ny: r.y1 });
    }
    for (i = 0; i < h; i++) {
      out.push({ k: vKey(r.x0, r.y0 + i), nx: r.x0 - 1, ny: r.y0 + i });
      out.push({ k: vKey(r.x1, r.y0 + i), nx: r.x1, ny: r.y0 + i });
    }
    return out;
  }

  // The next block size in the growth sequence. Larger Fibonacci sizes
  // become available as the settlement climbs the road hierarchy.
  Simulation.prototype.nextSize = function () {
    var r = this.random;
    var top = Math.min(FIB.length - 1, 1 + this.level);
    function pick() {
      // Small sizes are always most common; large ones are rare.
      var i = 0;
      while (i < top && r() < 0.42) i++;
      return FIB[i];
    }
    var a = pick(), b = pick();
    // Keep blocks from being absurdly elongated.
    while (Math.max(a, b) > 3 * Math.min(a, b)) {
      if (a > b) b = FIB[FIB.indexOf(b) + 1]; else a = FIB[FIB.indexOf(a) + 1];
    }
    return { w: a, h: b };
  };

  // Is r inside a sector ringed by a road of level >= L?
  Simulation.prototype.enclosed = function (r, L) {
    for (var i = 0; i < this.enclosures.length; i++) {
      var E = this.enclosures[i];
      if (E.level >= L && within(r, E)) return true;
    }
    return false;
  };

  // The part of the city still growing at level L: every block not yet inside
  // a sector of level >= L. It forms one compact cluster whose bounding
  // rectangle is where the next level-L road will go.
  Simulation.prototype.openBox = function (L) {
    var box = null;
    for (var b = 0; b < this.blocks.length; b++) {
      var r = blockRect(this.blocks[b]);
      if (!this.enclosed(r, L)) box = union(box, r);
    }
    return box;
  };

  // Streets must not grow too long without interruption: a growing cluster
  // may not become much longer than it is wide.
  function elongated(r) {
    var a = r.x1 - r.x0, b = r.y1 - r.y0;
    return Math.max(a, b) > 2 * Math.min(a, b) + 3;
  }

  // Private rule: find the placement of a w x h block that adds the fewest
  // new street segments while fronting the existing network. Growth at every
  // level stays one compact rectangular cluster: a block may not stretch a
  // growing cluster over a sector that is already ringed at that level, so
  // every future road can be a rectangle that cuts through nothing.
  Simulation.prototype.bestPlacement = function (w, h, loose) {
    var bb = this.bbox, best = null, bestScore = Infinity, L, i;
    var cx = (bb.x0 + bb.x1) / 2, cy = (bb.y0 + bb.y1) / 2;
    var boxes = [];
    for (L = 1; L <= this.level; L++) boxes[L] = this.openBox(L);
    var orientations = w === h ? [[w, h]] : [[w, h], [h, w]];
    for (var o = 0; o < orientations.length; o++) {
      var W = orientations[o][0], H = orientations[o][1];
      for (var y = bb.y0 - H; y <= bb.y1; y++) {
        for (var x = bb.x0 - W; x <= bb.x1; x++) {
          var r = rect(x, y, W, H);
          if (this.overlaps(r)) continue;
          var per = perimeter(r), shared = 0;
          for (i = 0; i < per.length; i++) if (this.edges[per[i].k] !== undefined) shared++;
          if (shared === 0) continue; // must front the existing network
          var cost = per.length - shared;
          // Tie-break toward the centre with a little noise.
          var dx = x + W / 2 - cx, dy = y + H / 2 - cy;
          var score = cost + 0.03 * Math.sqrt(dx * dx + dy * dy) + 1.2 * this.random();
          if (score >= bestScore) continue;
          var ok = true;
          for (L = 1; L <= this.level && ok; L++) {
            var grown = union(boxes[L], r);
            if (!loose && boxes[L] && elongated(grown) && !elongated(boxes[L])) ok = false;
            for (i = 0; i < this.enclosures.length && ok; i++) {
              var E = this.enclosures[i];
              if (E.level >= L && meets(grown, E)) ok = false;
            }
          }
          if (ok) { bestScore = score; best = r; }
        }
      }
    }
    return best;
  };

  // Blocks may not overlap each other, nor be built inside a ringed sector:
  // land left inside a boulevard stays open space.
  Simulation.prototype.overlaps = function (r) {
    for (var i = 0; i < this.enclosures.length; i++) if (meets(r, this.enclosures[i])) return true;
    for (var y = r.y0; y < r.y1; y++)
      for (var x = r.x0; x < r.x1; x++)
        if (this.cells[cellKey(x, y)] !== undefined) return true;
    return false;
  };

  Simulation.prototype.grow = function (r) {
    var bb = this.bbox;
    bb.x0 = Math.min(bb.x0, r.x0); bb.y0 = Math.min(bb.y0, r.y0);
    bb.x1 = Math.max(bb.x1, r.x1); bb.y1 = Math.max(bb.y1, r.y1);
  };

  Simulation.prototype.addBlock = function (r) {
    var id = this.blocks.length, x, y, i;
    var B = { id: id, x: r.x0, y: r.y0, w: r.x1 - r.x0, h: r.y1 - r.y0 };
    this.blocks.push(B);
    for (y = r.y0; y < r.y1; y++) for (x = r.x0; x < r.x1; x++) this.cells[cellKey(x, y)] = id;
    var per = perimeter(r);
    for (i = 0; i < per.length; i++) if (this.edges[per[i].k] === undefined) this.edges[per[i].k] = 0;
    if (id === 0) this.bbox = union(null, r); else this.grow(r);
    return B;
  };

  // One step of growth: private development, then community development.
  Simulation.prototype.step = function () {
    var size = this.nextSize();
    var made = [], r = rect(0, 0, size.w, size.h);
    if (this.blocks.length) {
      r = this.bestPlacement(size.w, size.h);
      // Nowhere left to grow a cluster: ring it as it stands, from the
      // smallest scale up, until there is room again.
      for (var L = 1; !r && L <= MAX_LEVEL; L++) {
        var R = this.openBox(L);
        if (R && !this.enclosed(R, L)) {
          made.push(this.commit(L, R));
          made = made.concat(this.community(L + 1));
        }
        r = this.bestPlacement(size.w, size.h);
      }
      if (!r) r = this.bestPlacement(size.w, size.h, true);
    }
    var block = this.addBlock(r);
    return { block: block, enclosures: made.concat(this.community()) };
  };

  // Community rule, applied at every scale. At level L the pieces are the
  // sectors of level L-1 (plain blocks when L = 1) that are still growing
  // outside any level-L road. A step is a move from one piece to a
  // neighbouring one; a piece fronting a road of level >= L is one step from
  // getting out, and while the cluster has no such road (the first village,
  // the first town) so is a piece on its outer edge. When some piece is more
  // than `limit(L)` steps from getting out, the whole cluster is ringed with
  // a level-L road around its bounding rectangle. That sector becomes a piece
  // of the next level up, so the same test is then run there.
  Simulation.prototype.community = function (from) {
    var made = [];
    for (var L = from || 1; L <= MAX_LEVEL; L++) {
      var R = this.tooComplicated(L);
      if (!R) break;
      made.push(this.commit(L, R));
    }
    return made;
  };

  Simulation.prototype.pieces = function (L) {
    var list = [], i;
    if (L === 1) {
      for (i = 0; i < this.blocks.length; i++) {
        var r = blockRect(this.blocks[i]);
        if (!this.enclosed(r, 1)) list.push(r);
      }
    } else {
      for (i = 0; i < this.enclosures.length; i++) {
        var E = this.enclosures[i];
        if (E.level === L - 1 && !this.enclosed(E, L)) list.push(E);
      }
    }
    return list;
  };

  Simulation.prototype.tooComplicated = function (L) {
    var P = this.pieces(L), n = P.length, i, j, k;
    if (n < 2) return null;
    var adj = [], road = [], rim = [], anyRoad = false;
    for (i = 0; i < n; i++) {
      adj.push([]);
      for (j = 0; j < n; j++) if (i !== j && abut(P[i], P[j])) adj[i].push(j);
      var per = perimeter(P[i]);
      road[i] = false; rim[i] = false;
      for (k = 0; k < per.length; k++) {
        if (this.edges[per[k].k] >= L) road[i] = true;
        // Outer edge: the land beyond is not another piece of this cluster.
        var cx = per[k].nx, cy = per[k].ny, inside = false;
        for (j = 0; j < n && !inside; j++) {
          var Q = P[j];
          if (cx >= Q.x0 && cx < Q.x1 && cy >= Q.y0 && cy < Q.y1) inside = true;
        }
        if (!inside) rim[i] = true;
      }
      if (road[i]) anyRoad = true;
    }
    var depth = new Array(n).fill(Infinity), queue = [];
    for (i = 0; i < n; i++) if (anyRoad ? road[i] : rim[i]) { depth[i] = 1; queue.push(i); }
    for (var q = 0; q < queue.length; q++) {
      i = queue[q];
      for (k = 0; k < adj[i].length; k++) {
        j = adj[i][k];
        if (depth[j] === Infinity) { depth[j] = depth[i] + 1; queue.push(j); }
      }
    }
    var worst = 0;
    for (i = 0; i < n; i++) if (depth[i] !== Infinity && depth[i] > worst) worst = depth[i];
    if (worst <= this.limit(L)) return null;
    var R = null;
    for (i = 0; i < n; i++) R = union(R, P[i]);
    return R;
  };

  Simulation.prototype.commit = function (L, R) {
    var per = perimeter(R);
    for (var i = 0; i < per.length; i++) if (!(this.edges[per[i].k] >= L)) this.edges[per[i].k] = L;
    this.enclosures.push({ x0: R.x0, y0: R.y0, x1: R.x1, y1: R.y1, level: L });
    this.grow(R);
    if (L > this.level) this.level = L;
    var ev = { level: L, at: this.blocks.length, rect: R };
    this.events.push(ev);
    return ev;
  };

  // Max steps allowed at level L. At level 1 a step crosses a block; above
  // that it crosses a whole neighbourhood, so a cluster of neighbourhoods is
  // ringed as soon as one of them is surrounded by the others.
  Simulation.prototype.limit = function (L) {
    return L === 1 ? this.steps : Math.max(1, Math.floor(this.steps / 4));
  };

  Simulation.prototype.stage = function () { return STAGES[this.level]; };

  // Street network as merged straight runs of equal level, for drawing.
  Simulation.prototype.segments = function () {
    var runs = [], seen = {}, e = this.edges;
    for (var k in e) {
      if (seen[k]) continue;
      var dir = k[0], parts = k.slice(1).split(','), x = +parts[0], y = +parts[1], lvl = e[k];
      var mk = dir === 'h' ? hKey : vKey, dx = dir === 'h' ? 1 : 0, dy = 1 - dx;
      var sx = x, sy = y;
      while (e[mk(sx - dx, sy - dy)] === lvl && !seen[mk(sx - dx, sy - dy)]) { sx -= dx; sy -= dy; }
      var ex = sx, ey = sy;
      while (e[mk(ex, ey)] === lvl && !seen[mk(ex, ey)]) { seen[mk(ex, ey)] = true; ex += dx; ey += dy; }
      runs.push({ x1: sx, y1: sy, x2: ex, y2: ey, level: lvl });
    }
    runs.sort(function (a, b) { return a.level - b.level; });
    return runs;
  };

  /* ------------------------------------------------------------------ */
  /* Rendering                                                           */
  /* ------------------------------------------------------------------ */

  var CSS =
    '.cg{--cg-ink:#1a1a1a;--cg-paper:#fbfaf6;--cg-block:#ece7da;--cg-new:#d9b36c;--cg-park:#dfe8d2;--cg-muted:#6b665c;' +
    'font:14px/1.4 Georgia,"Times New Roman",serif;color:var(--cg-ink);max-width:640px;margin:1.5em 0}' +
    '.cg-stage{background:var(--cg-paper);border:1px solid #d8d3c6;position:relative}' +
    '.cg svg{display:block;width:100%;height:auto}' +
    '.cg-block{fill:var(--cg-block);transition:fill 1.2s}' +
    '.cg-park{fill:var(--cg-park)}' +
    '.cg-block.cg-fresh{fill:var(--cg-new);transition:none}' +
    '.cg-road{stroke:var(--cg-ink);stroke-linecap:square;fill:none;vector-effect:non-scaling-stroke}' +
    '.cg-badge{margin-top:6px;font-style:italic;color:var(--cg-muted)}' +
    '.cg-badge b{font-style:normal;color:var(--cg-ink)}' +
    '.cg-bar{display:flex;flex-wrap:wrap;gap:6px 10px;align-items:center;margin-top:8px;font-size:13px}' +
    '.cg-bar button{font:inherit;padding:3px 10px;border:1px solid #bdb6a6;background:#fff;border-radius:3px;cursor:pointer;color:var(--cg-ink)}' +
    '.cg-bar button:hover{background:#f3efe5}' +
    '.cg-bar label{display:inline-flex;gap:4px;align-items:center;color:var(--cg-muted)}' +
    '.cg-bar input[type=number]{width:5em;font:inherit;padding:2px 4px;border:1px solid #bdb6a6;background:#fff;color:var(--cg-ink);border-radius:3px}' +
    '.cg-legend{display:flex;flex-wrap:wrap;gap:4px 14px;margin-top:6px;font-size:12px;color:var(--cg-muted)}' +
    '.cg-legend span{display:inline-flex;align-items:center;gap:5px}' +
    '.cg-legend i{display:inline-block;width:22px;background:var(--cg-ink)}';

  function injectCSS() {
    if (document.getElementById('cg-style')) return;
    var s = document.createElement('style');
    s.id = 'cg-style';
    s.textContent = CSS;
    document.head.appendChild(s);
  }

  function el(tag, attrs, parent, ns) {
    var n = ns ? document.createElementNS(SVGNS, tag) : document.createElement(tag);
    for (var k in attrs) n.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(n);
    return n;
  }

  // Road widths in screen pixels, independent of zoom.
  var WIDTHS = [0.8, 2.2, 4.5, 7, 9];

  function mount(root, options) {
    injectCSS();
    var d = root.dataset || {};
    var o = options || {};
    var cfg = {
      seed: o.seed != null ? o.seed : (d.seed ? parseInt(d.seed, 10) : null),
      blocks: o.blocks || parseInt(d.blocks || '200', 10),
      steps: o.steps || parseInt(d.steps || '3', 10),
      speed: o.speed || parseInt(d.speed || '100', 10),
      autoplay: o.autoplay != null ? o.autoplay : d.autoplay !== 'false',
      controls: o.controls != null ? o.controls : d.controls !== 'false'
    };

    root.classList.add('cg');
    root.innerHTML = '';
    var stage = el('div', { 'class': 'cg-stage' }, root);
    var svg = el('svg', { role: 'img', 'aria-label': 'Simulated growth of a complex grid street network' }, stage, true);
    var gParks = el('g', {}, svg, true), gBlocks = el('g', {}, svg, true), gRoads = el('g', {}, svg, true);
    var badge = el('div', { 'class': 'cg-badge', 'aria-live': 'polite' }, root);

    var bar, seedInput, stepsInput, playBtn;
    if (cfg.controls) {
      bar = el('div', { 'class': 'cg-bar' }, root);
      playBtn = el('button', { type: 'button' }, bar);
      var stepBtn = el('button', { type: 'button' }, bar); stepBtn.textContent = 'Step';
      var resetBtn = el('button', { type: 'button' }, bar); resetBtn.textContent = 'New city';
      var l1 = el('label', {}, bar); l1.appendChild(document.createTextNode('Seed'));
      seedInput = el('input', { type: 'number', min: '0' }, l1);
      var l2 = el('label', { title: 'A sector is ringed by a higher road when it takes more than this many steps to get out of it' }, bar);
      l2.appendChild(document.createTextNode('Max steps'));
      stepsInput = el('input', { type: 'number', min: '2', max: '8' }, l2);
      var legend = el('div', { 'class': 'cg-legend' }, root);
      for (var i = 0; i < 4; i++) {
        var sp = el('span', {}, legend), sw = el('i', {}, sp);
        sw.style.height = WIDTHS[i] + 'px';
        sp.appendChild(document.createTextNode(ROAD_NAMES[i]));
      }
      playBtn.addEventListener('click', function () { playing ? pause() : play(); });
      stepBtn.addEventListener('click', function () { pause(); advance(); });
      resetBtn.addEventListener('click', function () { reset(Math.floor(Math.random() * 1e6)); play(); });
      seedInput.addEventListener('change', function () { reset(parseInt(seedInput.value, 10) || 0); play(); });
      stepsInput.addEventListener('change', function () {
        cfg.steps = Math.max(2, Math.min(8, parseInt(stepsInput.value, 10) || 3));
        reset(sim.seed); play();
      });
    }

    var sim, timer = null, playing = false, view = null;

    function reset(seed) {
      pause();
      sim = new Simulation({ seed: seed != null ? seed : Math.floor(Math.random() * 1e6), steps: cfg.steps });
      gParks.innerHTML = ''; gBlocks.innerHTML = ''; gRoads.innerHTML = ''; view = null;
      if (seedInput) { seedInput.value = sim.seed; stepsInput.value = cfg.steps; }
      render();
    }

    function drawBlock(B, fresh) {
      var r = el('rect', { x: B.x, y: B.y, width: B.w, height: B.h, 'class': fresh ? 'cg-block cg-fresh' : 'cg-block' }, gBlocks, true);
      if (fresh) setTimeout(function () { r.classList.remove('cg-fresh'); }, 30);
    }

    function advance() {
      if (sim.blocks.length >= cfg.blocks) { pause(); return false; }
      drawBlock(sim.step().block, true);
      render();
      return true;
    }

    function render() {
      var bb = sim.bbox, pad = 3;
      var w = Math.max(12, bb.x1 - bb.x0 + 2 * pad), h = Math.max(10, bb.y1 - bb.y0 + 2 * pad);
      // Keep a steady 6:5 frame, only ever zooming out, so the view doesn't jitter.
      var size = Math.max(w, h * 1.2);
      var cx = (bb.x0 + bb.x1) / 2, cy = (bb.y0 + bb.y1) / 2;
      if (!view || size > view.size || Math.abs(cx - view.cx) > view.size * 0.1 || Math.abs(cy - view.cy) > view.size * 0.1)
        view = { size: Math.max(size, view ? view.size : 0), cx: cx, cy: cy };
      var vw = view.size, vh = view.size / 1.2;
      svg.setAttribute('viewBox', (view.cx - vw / 2) + ' ' + (view.cy - vh / 2) + ' ' + vw + ' ' + vh);

      // Land inside a ring that no one has built on is open space.
      gParks.innerHTML = '';
      for (var p = 0; p < sim.enclosures.length; p++) {
        var E = sim.enclosures[p];
        el('rect', { x: E.x0, y: E.y0, width: E.x1 - E.x0, height: E.y1 - E.y0, 'class': 'cg-park' }, gParks, true);
      }
      // Thinner roads on small screens.
      var k = Math.max(0.55, Math.min(1, (svg.clientWidth || 480) / 480));
      gRoads.innerHTML = '';
      var segs = sim.segments();
      for (var i = 0; i < segs.length; i++) {
        var s = segs[i];
        el('line', { x1: s.x1, y1: s.y1, x2: s.x2, y2: s.y2, 'class': 'cg-road', 'stroke-width': Math.max(0.8, WIDTHS[s.level] * k) }, gRoads, true);
      }
      badge.innerHTML = '<b>' + sim.stage() + '</b> &middot; ' + sim.blocks.length + ' blocks';
      if (playBtn) playBtn.textContent = playing ? 'Pause' : (sim.blocks.length >= cfg.blocks ? 'Replay' : 'Play');
    }

    function play() {
      if (sim.blocks.length >= cfg.blocks) reset(sim.seed);
      playing = true; render();
      (function tick() {
        if (!playing) return;
        if (advance()) timer = setTimeout(tick, cfg.speed); else { playing = false; render(); }
      })();
    }

    function pause() { playing = false; clearTimeout(timer); if (sim) render(); }

    reset(cfg.seed);
    if (cfg.autoplay) {
      // Start when scrolled into view.
      if ('IntersectionObserver' in global) {
        var io = new IntersectionObserver(function (entries) {
          if (entries[0].isIntersecting) { io.disconnect(); play(); }
        });
        io.observe(root);
      } else play();
    } else {
      // Show the finished city when not animating.
      while (sim.blocks.length < cfg.blocks) sim.step();
      for (var b = 0; b < sim.blocks.length; b++) drawBlock(sim.blocks[b], false);
      render();
    }

    return { play: play, pause: pause, reset: reset, step: advance, simulation: function () { return sim; } };
  }

  var api = { Simulation: Simulation, mount: mount };
  global.ComplexGrid = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;

  if (typeof document !== 'undefined') {
    var init = function () {
      var nodes = document.querySelectorAll('.complex-grid');
      for (var i = 0; i < nodes.length; i++) if (!nodes[i].__cg) nodes[i].__cg = mount(nodes[i]);
    };
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
  }
})(typeof window !== 'undefined' ? window : this);
