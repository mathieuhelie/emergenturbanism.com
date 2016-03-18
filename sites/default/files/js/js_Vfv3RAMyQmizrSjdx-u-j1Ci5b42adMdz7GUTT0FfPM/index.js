(function ($) {
  Drupal.behaviors.emurtao = {
    attach: function (context) {
      $(".field-name-body a.photoswipe", context).photoSwipe();
    }
  };
}) (jQuery);;
