/* ============================================================
   CSC210 — Week 1 SPA Shared Navigation Component
   ============================================================
   Provides in-page section navigation (scroll-spy) and
   optional section-level sidebar links.  Vanilla JS — no
   dependencies.

   NOTE: Cross-SPA navigation is intentionally not provided
   by this script. SPA-to-SPA links are handled by the LMS
   or platform navigation, not intra-SPA JavaScript.
   ============================================================ */

(function () {
  'use strict';

  /* ---------- Public API ---------- */
  window.SPANav = {
    /**
     * Initialise in-page section navigation.
     * @param {string} [sectionIds]  Comma-separated list of section ids for
     *                               intra-SPA sidebar links (optional).
     */
    init: function (sectionIds) {
      if (sectionIds) {
        this.buildSectionLinks(sectionIds);
      }
      this.setupScrollSpy();
    },

    /* Build section-level links from a comma-separated id list. */
    buildSectionLinks: function (sectionIds) {
      var container = document.querySelector('.sp-sidebar__sections');
      if (!container) return;
      var ids = sectionIds.split(',');
      var frag = document.createDocumentFragment();
      for (var i = 0; i < ids.length; i++) {
        var id = ids[i].trim();
        var el = document.getElementById(id);
        if (!el) continue;
        var a = document.createElement('a');
        a.href = '#' + id;
        a.textContent = el.textContent.trim().replace(/^.*?—\s*/, '');
        a.className = 'sp-sidebar__nav-link';
        frag.appendChild(a);
      }
      container.appendChild(frag);
    },

    /* Simple scroll-spy for section links. */
    setupScrollSpy: function () {
      var links = document.querySelectorAll('.sp-sidebar__sections a');
      if (!links.length) return;
      var sections = [];
      for (var i = 0; i < links.length; i++) {
        var target = document.querySelector(links[i].getAttribute('href'));
        if (target) sections.push({ el: target, link: links[i] });
      }
      window.addEventListener('scroll', function () {
        var scrollY = window.pageYOffset || document.documentElement.scrollTop;
        for (var j = sections.length - 1; j >= 0; j--) {
          if (sections[j].el.offsetTop - 100 <= scrollY) {
            for (var k = 0; k < sections.length; k++) sections[k].link.classList.remove('active');
            sections[j].link.classList.add('active');
            break;
          }
        }
      }, { passive: true });
    }
  };

  /* ---------- Auto-initialise if data attribute present ---------- */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', autoInit);
  } else {
    autoInit();
  }

  function autoInit() {
    var sectionIds = document.documentElement.getAttribute('data-section-ids');
    SPANav.init(sectionIds);
  }

})();
