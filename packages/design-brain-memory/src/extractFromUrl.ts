import path from 'node:path';
import fs from 'fs-extra';
import { runAgentBrowserJson } from './agentBrowser.js';
import type {
  AnimationToken,
  DesignAnalysis,
  MotionToken,
  ResponsiveSnapshot,
  StateStyleToken,
  JourneyStep,
} from './types.js';
import { classifyMotionIntent, detectPhysics, detectAnimationGroups, classifyGsapEasing } from './classify.js';

const DEFAULT_VIEWPORTS: Array<{ label: string; width: number; height: number }> = [
  { label: 'desktop', width: 1440, height: 1200 },
  { label: 'tablet', width: 1024, height: 1366 },
  { label: 'mobile', width: 390, height: 844 },
];

// ---------------------------------------------------------------------------
// UNIFIED_SCRIPT: single eval that extracts design tokens, scrolls the page
// to trigger lazy-loaded animations, observes animations, and returns
// everything in one shot. This replaces 3 separate scripts + a scroll loop
// that used to spawn 40-70 child processes.
// ---------------------------------------------------------------------------
const UNIFIED_SCRIPT = String.raw`(async () => {
  /* ── Shared helpers ── */
  function buildSelector(el) {
    if (!el || !el.tagName) return 'unknown';
    var tag = el.tagName.toLowerCase();
    if (el.id) return tag + '#' + el.id;
    if (typeof el.className === 'string' && el.className.trim()) {
      var firstClass = el.className.trim().split(/\s+/).slice(0, 2).join('.');
      if (firstClass) return tag + '.' + firstClass;
    }
    return tag;
  }

  function parseCssColor(input) {
    if (!input) return null;
    var value = input.toString().trim().toLowerCase();
    if (value.startsWith('#')) {
      if (value.length === 4) return '#' + value[1]+value[1]+value[2]+value[2]+value[3]+value[3];
      if (value.length === 7) return value;
      return null;
    }
    var m = value.match(/rgba?\(([^)]+)\)/);
    if (m) {
      var parts = m[1].split(',').map(function(p){return p.trim();});
      var r = Number(parts[0]), g = Number(parts[1]), b = Number(parts[2]);
      if ([r,g,b].some(isNaN)) return null;
      var h = function(n){return Math.max(0,Math.min(255,n)).toString(16).padStart(2,'0');};
      return '#'+h(r)+h(g)+h(b);
    }
    return null;
  }

  function normalizeWhitespace(text) {
    return (text || '').replace(/\s+/g, ' ').trim();
  }

  function inferComponentKind(el) {
    var tag = el.tagName.toLowerCase();
    var cn = typeof el.className === 'string' ? el.className.toLowerCase() : '';
    if (tag === 'button' || cn.includes('btn')) return 'button';
    if (tag === 'a') return 'link';
    if (tag === 'input' || tag === 'textarea' || tag === 'select') return 'form-control';
    if (tag === 'nav' || cn.includes('nav')) return 'navigation';
    if (cn.includes('card')) return 'card';
    if (tag === 'header') return 'header';
    if (tag === 'footer') return 'footer';
    if (cn.includes('hero')) return 'hero';
    return tag;
  }

  /* ═══════════════════════════════════════════════
     PHASE 1: Design token extraction
     ═══════════════════════════════════════════════ */
  var maxNodes = 2000;
  var nodes = Array.from(document.querySelectorAll('body *')).slice(0, maxNodes);

  var colorMap = new Map();
  var typographyMap = new Map();
  var componentList = [];
  var motionList = [];
  var layoutList = [];
  var variableMap = {};
  var stateStyleList = [];

  var componentTags = new Set(['button','a','input','select','textarea','nav','header','footer','form']);
  var maxComponents = 220, maxMotion = 220, maxStateStyles = 260, maxRulesPerSheet = 5000;

  function pushColor(value, sample) {
    if (!value || value === 'transparent' || value === 'rgba(0, 0, 0, 0)') return;
    var parsed = parseCssColor(value);
    if (!parsed) return;
    var key = parsed.toUpperCase();
    var entry = colorMap.get(key) || { hex: key, count: 0, samples: [] };
    entry.count += 1;
    if (sample && entry.samples.length < 5 && !entry.samples.includes(sample)) entry.samples.push(sample);
    colorMap.set(key, entry);
  }

  nodes.forEach(function(el) {
    var style = window.getComputedStyle(el);
    if (style.display === 'none' || style.visibility === 'hidden' || Number(style.opacity) === 0) return;

    var selector = buildSelector(el);
    pushColor(style.color, selector + ':color');
    pushColor(style.backgroundColor, selector + ':background');
    if (style.borderColor && style.borderColor !== 'rgba(0, 0, 0, 0)') pushColor(style.borderColor, selector + ':border');

    if (normalizeWhitespace(el.textContent || '').length > 0) {
      var tKey = [style.fontFamily, style.fontSize, style.fontWeight, style.lineHeight].join('|');
      var existing = typographyMap.get(tKey) || { fontFamily: style.fontFamily, fontSize: style.fontSize, fontWeight: style.fontWeight, lineHeight: style.lineHeight, count: 0 };
      existing.count += 1;
      typographyMap.set(tKey, existing);
    }

    var tag = el.tagName.toLowerCase();
    var cn = typeof el.className === 'string' ? el.className.toLowerCase() : '';
    var isComponent = componentTags.has(tag) || cn.includes('btn') || cn.includes('button') || cn.includes('card') || cn.includes('hero') || el.getAttribute('role') === 'button' || el.getAttribute('role') === 'navigation' || selector.startsWith('section.') || selector.startsWith('div.card');
    if (isComponent && componentList.length < maxComponents) {
      componentList.push({
        kind: inferComponentKind(el), tag: tag, selector: selector,
        text: normalizeWhitespace(el.textContent || '').slice(0, 90),
        className: typeof el.className === 'string' ? normalizeWhitespace(el.className) : '',
        styles: { color: style.color, backgroundColor: style.backgroundColor, borderRadius: style.borderRadius, border: style.border, padding: style.padding, margin: style.margin, fontSize: style.fontSize, fontWeight: style.fontWeight, boxShadow: style.boxShadow },
      });
    }

    var hasTransition = style.transitionDuration && style.transitionDuration !== '0s';
    var hasAnimation = style.animationName && style.animationName !== 'none';
    var hasTransform = style.transform && style.transform !== 'none';
    if ((hasTransition || hasAnimation || hasTransform) && motionList.length < maxMotion) {
      motionList.push({ selector: selector, transition: style.transition, animation: style.animation, transform: style.transform });
    }
  });

  Array.from(document.querySelectorAll('header, nav, main, section, article, aside, footer')).slice(0, 160).forEach(function(el) {
    layoutList.push({ tag: el.tagName.toLowerCase(), selector: buildSelector(el), role: el.getAttribute('role') || '', children: el.children.length });
  });

  [document.documentElement, document.body].forEach(function(root) {
    if (!root) return;
    var style = window.getComputedStyle(root);
    for (var prop of style) {
      if (!prop.startsWith('--')) continue;
      var val = style.getPropertyValue(prop).trim();
      if (val) variableMap[prop] = val;
    }
  });

  // Pseudo-state styles from stylesheets
  try {
    var stateKinds = [':hover', ':focus', ':active'];
    for (var sheet of Array.from(document.styleSheets)) {
      var rules;
      try { rules = sheet.cssRules; } catch(e) { continue; }
      if (!rules) continue;
      var rc = Math.min(rules.length, maxRulesPerSheet);
      for (var ri = 0; ri < rc; ri++) {
        var rule = rules[ri];
        var st = 'selectorText' in rule ? String(rule.selectorText || '') : '';
        var rs = 'style' in rule ? rule.style : undefined;
        if (!st || !rs) continue;
        for (var sk of stateKinds) {
          if (!st.includes(sk)) continue;
          var decl = {};
          for (var dp of ['color','background-color','border-color','box-shadow','transform','transition','opacity']) {
            var dv = rs.getPropertyValue(dp);
            if (dv) decl[dp] = dv;
          }
          if (Object.keys(decl).length === 0) continue;
          stateStyleList.push({ selector: st.split(sk).join('').trim() || st, state: sk.slice(1), declarations: decl });
          if (stateStyleList.length >= maxStateStyles) break;
        }
        if (stateStyleList.length >= maxStateStyles) break;
      }
      if (stateStyleList.length >= maxStateStyles) break;
    }
  } catch(e) {}

  var designTokens = {
    pageTitle: document.title,
    pageUrl: window.location.href,
    viewport: { width: window.innerWidth, height: window.innerHeight },
    colors: Array.from(colorMap.values()).sort(function(a,b){return b.count-a.count;}).slice(0, 70),
    typography: Array.from(typographyMap.values()).sort(function(a,b){return b.count-a.count;}).slice(0, 90),
    components: componentList,
    motion: motionList,
    layout: layoutList,
    cssVariables: variableMap,
    stateStyles: stateStyleList,
  };

  /* ═══════════════════════════════════════════════
     PHASE 2: Scroll through the page (in-browser)
     Triggers lazy-loaded GSAP, ScrollTrigger, etc.
     ═══════════════════════════════════════════════ */
  try {
    var height = Math.max(document.body.scrollHeight, document.documentElement.scrollHeight);
    var vh = window.innerHeight;
    var scrollSteps = Math.min(Math.ceil(height / vh), 12);
    var stepSize = Math.ceil(height / scrollSteps);
    for (var si = 1; si <= scrollSteps; si++) {
      window.scrollTo({ top: si * stepSize, behavior: 'instant' });
      await new Promise(function(r) { setTimeout(r, 150); });
    }
    window.scrollTo({ top: 0, behavior: 'instant' });
    await new Promise(function(r) { setTimeout(r, 800); });
  } catch(e) {}

  /* ═══════════════════════════════════════════════
     PHASE 3: Animation observation (post-scroll)
     ═══════════════════════════════════════════════ */
  var animResult = {
    libraries: [],
    webAnimations: [],
    gsapTweens: [],
    lottiePlayers: [],
    scrollBindings: { hasScrollTrigger: false, hasIntersectionObserver: false, scrollTriggers: [], hasScrollSnap: false, hasScrollTimeline: false },
  };
  var maxAnims = 200;

  try {
    if (typeof gsap !== 'undefined') animResult.libraries.push({ name: 'gsap', version: typeof gsap.version === 'string' ? gsap.version : 'unknown' });
    if (typeof ScrollTrigger !== 'undefined') { animResult.libraries.push({ name: 'scrolltrigger', version: 'detected' }); animResult.scrollBindings.hasScrollTrigger = true; }
    if (typeof lottie !== 'undefined' || typeof bodymovin !== 'undefined') animResult.libraries.push({ name: 'lottie', version: 'detected' });
    if (document.querySelector('lottie-player, dotlottie-player') && !animResult.libraries.some(function(l){return l.name==='lottie';})) animResult.libraries.push({ name: 'lottie', version: 'web-component' });
    if (document.querySelector('[data-framer-name], [data-framer-component-type]')) animResult.libraries.push({ name: 'framer-motion', version: 'detected' });
  } catch(e) {}

  try {
    var anims = document.getAnimations();
    for (var ai = 0; ai < Math.min(anims.length, maxAnims); ai++) {
      var anim = anims[ai];
      var effect = anim.effect;
      if (!effect || !effect.target) continue;
      var sel = buildSelector(effect.target);
      var kfs = []; try { kfs = effect.getKeyframes(); } catch(e) {}
      var ct = {}; try { ct = effect.getComputedTiming(); } catch(e) {}
      var tlt = 'document';
      try { if (anim.timeline && anim.timeline.constructor) { var tn = anim.timeline.constructor.name; if (tn === 'ScrollTimeline') tlt = 'scroll'; else if (tn === 'ViewTimeline') tlt = 'view'; } } catch(e) {}
      if (tlt !== 'document') animResult.scrollBindings.hasScrollTimeline = true;
      animResult.webAnimations.push({
        selector: sel, playState: anim.playState, animationName: anim.animationName || anim.id || '',
        keyframes: kfs.map(function(kf) {
          var props = {};
          for (var k in kf) { if (k !== 'offset' && k !== 'computedOffset' && k !== 'easing' && k !== 'composite') props[k] = String(kf[k]); }
          return { offset: kf.computedOffset != null ? kf.computedOffset : (kf.offset || 0), properties: props, easing: kf.easing || 'linear' };
        }),
        timing: { duration: typeof ct.duration === 'number' ? ct.duration : 0, delay: ct.delay || 0, easing: ct.easing || 'linear', iterations: ct.iterations != null ? ct.iterations : 1, direction: ct.direction || 'normal', fillMode: ct.fill || 'none' },
        timelineType: tlt,
      });
    }
  } catch(e) {}

  try {
    if (typeof gsap !== 'undefined' && gsap.globalTimeline) {
      var children = gsap.globalTimeline.getChildren(true, true, false);
      for (var gi = 0; gi < Math.min(children.length, maxAnims); gi++) {
        var tw = children[gi];
        var targets = tw.targets ? tw.targets() : [];
        if (targets.length === 0) continue;
        var vars = {};
        if (tw.vars) { for (var vk in tw.vars) { var vv = tw.vars[vk]; if (typeof vv === 'number' || typeof vv === 'string') vars[vk] = vv; } }
        animResult.gsapTweens.push({
          selector: buildSelector(targets[0]),
          duration: typeof tw.duration === 'function' ? tw.duration() : 0,
          delay: typeof tw.delay === 'function' ? tw.delay() : 0,
          ease: tw.vars && tw.vars.ease ? tw.vars.ease : 'power1.out',
          vars: vars,
          startTime: typeof tw.startTime === 'function' ? tw.startTime() : 0,
        });
      }
    }
  } catch(e) {}

  try {
    var lr = (typeof lottie !== 'undefined') ? lottie : ((typeof bodymovin !== 'undefined') ? bodymovin : null);
    if (lr && typeof lr.getRegisteredAnimations === 'function') {
      var regs = lr.getRegisteredAnimations();
      for (var li = 0; li < Math.min(regs.length, 20); li++) {
        var la = regs[li]; var c = la.wrapper || la.container;
        animResult.lottiePlayers.push({ selector: c ? buildSelector(c) : 'lottie-unknown', frameRate: la.frameRate || (la.animationData && la.animationData.fr) || 0, totalFrames: la.totalFrames || (la.animationData && la.animationData.op) || 0, duration: typeof la.getDuration === 'function' ? la.getDuration(false) : 0 });
      }
    }
    var ps = document.querySelectorAll('lottie-player, dotlottie-player');
    for (var pi = 0; pi < Math.min(ps.length, 20); pi++) {
      var pSel = buildSelector(ps[pi]);
      if (!animResult.lottiePlayers.some(function(l){return l.selector === pSel;})) animResult.lottiePlayers.push({ selector: pSel, frameRate: 0, totalFrames: 0, duration: 0 });
    }
  } catch(e) {}

  try {
    if (typeof ScrollTrigger !== 'undefined' && typeof ScrollTrigger.getAll === 'function') {
      var trigs = ScrollTrigger.getAll();
      for (var ti = 0; ti < Math.min(trigs.length, 50); ti++) {
        var tr = trigs[ti];
        animResult.scrollBindings.scrollTriggers.push({ triggerSelector: tr.trigger ? buildSelector(tr.trigger) : '', isActive: !!tr.isActive });
      }
    }
  } catch(e) {}

  try {
    var snap = window.getComputedStyle(document.documentElement).scrollSnapType;
    if (snap && snap !== 'none') animResult.scrollBindings.hasScrollSnap = true;
  } catch(e) {}

  /* ═══════════════════════════════════════════════
     PHASE 4: Page summary (for journey context)
     ═══════════════════════════════════════════════ */
  var h1 = ''; try { h1 = (document.querySelector('h1') || {}).textContent || ''; h1 = h1.trim(); } catch(e) {}
  var navCount = 0; try { navCount = document.querySelectorAll('nav a, header a').length; } catch(e) {}
  var ctaCount = 0; try { ctaCount = document.querySelectorAll('button, a[role="button"], .btn, .button').length; } catch(e) {}

  return {
    designTokens: designTokens,
    animations: animResult,
    pageSummary: { title: document.title, url: window.location.href, summary: [h1, 'nav-links:' + navCount, 'ctas:' + ctaCount].filter(Boolean).join(' | ') },
  };
})()`;

/* ─── Animation observer result types ─── */

interface RawAnimObserverResult {
  libraries: Array<{ name: string; version: string }>;
  webAnimations: Array<{
    selector: string;
    playState: string;
    animationName: string;
    keyframes: Array<{ offset: number; properties: Record<string, string>; easing?: string }>;
    timing: {
      duration: number;
      delay: number;
      easing: string;
      iterations: number;
      direction: string;
      fillMode: string;
    };
    timelineType: string;
  }>;
  gsapTweens: Array<{
    selector: string;
    duration: number;
    delay: number;
    ease: string;
    vars: Record<string, unknown>;
    startTime: number;
  }>;
  lottiePlayers: Array<{
    selector: string;
    frameRate: number;
    totalFrames: number;
    duration: number;
  }>;
  scrollBindings: {
    hasScrollTrigger: boolean;
    hasIntersectionObserver: boolean;
    scrollTriggers: Array<{ triggerSelector: string; isActive: boolean }>;
    hasScrollSnap: boolean;
    hasScrollTimeline: boolean;
  };
}

interface UnifiedResult {
  designTokens: Record<string, unknown>;
  animations: RawAnimObserverResult;
  pageSummary: { title: string; url: string; summary: string };
}

function convertObserverResult(raw: RawAnimObserverResult): AnimationToken[] {
  const tokens: AnimationToken[] = [];
  const libraryNames = new Set(raw.libraries.map((l) => l.name));

  for (const wa of raw.webAnimations) {
    const intent = classifyMotionIntent(wa.keyframes);
    let library: AnimationToken['library'] = 'css';
    if (libraryNames.has('framer-motion')) {
      library = 'framer-motion';
    }

    const token: AnimationToken = {
      selector: wa.selector,
      library,
      motionIntent: intent,
      timing: {
        duration: wa.timing.duration,
        delay: wa.timing.delay,
        easing: wa.timing.easing,
        iterations: wa.timing.iterations === Infinity ? Infinity : wa.timing.iterations,
        direction: wa.timing.direction as AnimationToken['timing'] extends undefined ? never : NonNullable<AnimationToken['timing']>['direction'],
        fillMode: wa.timing.fillMode as AnimationToken['timing'] extends undefined ? never : NonNullable<AnimationToken['timing']>['fillMode'],
      },
      keyframes: wa.keyframes,
      trigger: wa.timelineType === 'scroll' || wa.timelineType === 'view' ? 'scroll' : 'load',
    };

    if (wa.timelineType !== 'document') {
      token.scrollBinding = {
        hasScrollTrigger: false,
        hasIntersectionObserver: false,
        scrollTimelineAxis: 'block',
      };
    }

    const allProps = new Set<string>();
    for (const kf of wa.keyframes) {
      for (const prop of Object.keys(kf.properties)) allProps.add(prop);
    }

    if (allProps.has('transform')) {
      for (const fnName of ['translateX', 'translateY', 'scale', 'rotate']) {
        const physics = detectPhysics(wa.keyframes, fnName);
        if (physics) {
          token.physics = physics;
          token.motionIntent = physics.type === 'spring' ? 'spring' : 'bounce';
          break;
        }
      }
    }

    tokens.push(token);
  }

  for (const tween of raw.gsapTweens) {
    const token: AnimationToken = {
      selector: tween.selector,
      library: 'gsap',
      motionIntent: 'complex',
      timing: {
        duration: tween.duration * 1000,
        delay: tween.delay * 1000,
        easing: tween.ease || 'power1.out',
        iterations: 1,
        direction: 'normal',
        fillMode: 'none',
      },
      trigger: 'load',
      gsapVars: tween.vars,
    };

    const physics = classifyGsapEasing(tween.ease);
    if (physics) {
      token.physics = physics;
      token.motionIntent = physics.type === 'spring' ? 'spring' : 'bounce';
    } else {
      const varKeys = Object.keys(tween.vars);
      if (varKeys.some((k) => ['x', 'y', 'xPercent', 'yPercent'].includes(k))) {
        token.motionIntent = 'slide';
      } else if (varKeys.some((k) => ['scale', 'scaleX', 'scaleY'].includes(k))) {
        token.motionIntent = 'scale';
      } else if (varKeys.some((k) => ['rotation', 'rotationX', 'rotationY'].includes(k))) {
        token.motionIntent = 'rotate';
      } else if (varKeys.includes('opacity')) {
        token.motionIntent = 'fade';
      }
    }

    if (raw.scrollBindings.hasScrollTrigger) {
      const matchingTrigger = raw.scrollBindings.scrollTriggers.find(
        (st) => st.triggerSelector === tween.selector
      );
      if (matchingTrigger) {
        token.trigger = 'scroll';
        token.scrollBinding = {
          triggerSelector: matchingTrigger.triggerSelector,
          hasScrollTrigger: true,
          hasIntersectionObserver: false,
        };
      }
    }

    tokens.push(token);
  }

  for (const lp of raw.lottiePlayers) {
    tokens.push({
      selector: lp.selector,
      library: 'lottie',
      motionIntent: 'complex',
      trigger: 'load',
      lottieMetadata: {
        frameRate: lp.frameRate,
        totalFrames: lp.totalFrames,
        duration: lp.duration,
      },
    });
  }

  return tokens;
}

function normalizeResult(result: Record<string, unknown>): DesignAnalysis {
  return {
    pageTitle: (result.pageTitle as string | undefined) ?? undefined,
    pageUrl: (result.pageUrl as string | undefined) ?? undefined,
    viewport: (result.viewport as { width: number; height: number } | undefined) ?? undefined,
    colors: (result.colors as DesignAnalysis['colors']) ?? [],
    typography: (result.typography as DesignAnalysis['typography']) ?? [],
    components: (result.components as DesignAnalysis['components']) ?? [],
    motion: (result.motion as DesignAnalysis['motion']) ?? [],
    layout: (result.layout as DesignAnalysis['layout']) ?? [],
    cssVariables: (result.cssVariables as DesignAnalysis['cssVariables']) ?? {},
    stateStyles: (result.stateStyles as DesignAnalysis['stateStyles']) ?? [],
  };
}

function mergeAnalysis(all: DesignAnalysis[]): DesignAnalysis {
  const first = all[0] ?? {
    colors: [],
    typography: [],
    components: [],
    motion: [],
    layout: [],
    cssVariables: {},
  };

  const colorMap = new Map<string, { hex: string; count: number; samples: string[] }>();
  for (const entry of all) {
    for (const color of entry.colors) {
      const existing = colorMap.get(color.hex) ?? { hex: color.hex, count: 0, samples: [] };
      existing.count += color.count;
      for (const sample of color.samples) {
        if (existing.samples.length < 8 && !existing.samples.includes(sample)) {
          existing.samples.push(sample);
        }
      }
      colorMap.set(color.hex, existing);
    }
  }

  const typographyMap = new Map<string, DesignAnalysis['typography'][number]>();
  for (const entry of all) {
    for (const token of entry.typography) {
      const key = `${token.fontFamily}|${token.fontSize}|${token.fontWeight}|${token.lineHeight}`;
      const existing = typographyMap.get(key) ?? { ...token, count: 0 };
      existing.count += token.count;
      typographyMap.set(key, existing);
    }
  }

  const componentMap = new Map<string, DesignAnalysis['components'][number]>();
  const motionMap = new Map<string, DesignAnalysis['motion'][number]>();
  const layoutMap = new Map<string, DesignAnalysis['layout'][number]>();
  const stateMap = new Map<string, StateStyleToken>();
  const cssVariables: Record<string, string> = {};

  for (const entry of all) {
    Object.assign(cssVariables, entry.cssVariables);

    for (const component of entry.components) {
      const key = `${component.kind}|${component.selector}|${component.text}`;
      if (!componentMap.has(key)) {
        componentMap.set(key, component);
      }
    }

    for (const motion of entry.motion) {
      const key = ('library' in motion && 'motionIntent' in motion)
        ? `${motion.selector}|${(motion as { library: string }).library}|${(motion as { motionIntent: string }).motionIntent}`
        : `${motion.selector}|${(motion as { transition: string }).transition}|${(motion as { animation: string }).animation}|${(motion as { transform: string }).transform}`;
      if (!motionMap.has(key)) {
        motionMap.set(key, motion);
      }
    }

    for (const layout of entry.layout) {
      const key = `${layout.tag}|${layout.selector}|${layout.role}`;
      if (!layoutMap.has(key)) {
        layoutMap.set(key, layout);
      }
    }

    for (const state of entry.stateStyles ?? []) {
      const key = `${state.selector}|${state.state}|${JSON.stringify(state.declarations)}`;
      if (!stateMap.has(key)) {
        stateMap.set(key, state);
      }
    }
  }

  return {
    pageTitle: first.pageTitle,
    pageUrl: first.pageUrl,
    viewport: first.viewport,
    colors: [...colorMap.values()].sort((a, b) => b.count - a.count).slice(0, 90),
    typography: [...typographyMap.values()].sort((a, b) => b.count - a.count).slice(0, 120),
    components: [...componentMap.values()].slice(0, 260),
    motion: [...motionMap.values()].slice(0, 260),
    layout: [...layoutMap.values()].slice(0, 220),
    cssVariables,
    stateStyles: [...stateMap.values()].slice(0, 300),
  };
}

function toResponsiveSnapshot(label: string, analysis: DesignAnalysis): ResponsiveSnapshot {
  return {
    label,
    viewport: analysis.viewport ?? { width: 0, height: 0 },
    url: analysis.pageUrl,
    title: analysis.pageTitle,
    colorCount: analysis.colors.length,
    componentCount: analysis.components.length,
    typographyCount: analysis.typography.length,
  };
}

// ---------------------------------------------------------------------------
// captureDesignFromUrl — the main entry point.
//
// Old version: 70-90 child process spawns per URL.
// New version: ~7 spawns: open, wait, set viewport, eval, snapshot, screenshot, close.
// ---------------------------------------------------------------------------
export async function captureDesignFromUrl(params: {
  url: string;
  sessionName: string;
  screenshotPath: string;
  workingDir: string;
  journeySteps?: number;
  responsiveViewports?: Array<{ label: string; width: number; height: number }>;
}): Promise<DesignAnalysis> {
  const {
    url,
    sessionName,
    screenshotPath,
    workingDir,
    responsiveViewports = DEFAULT_VIEWPORTS,
  } = params;

  await fs.ensureDir(path.dirname(screenshotPath));

  // 1. Open the URL
  await runAgentBrowserJson(['open', url], { session: sessionName, cwd: workingDir });

  // 2. Wait for page to fully load (networkidle = no requests for 500ms).
  //    Falls back gracefully if the site has persistent connections (analytics, chat, etc.)
  await runAgentBrowserJson(['wait', '--load', 'networkidle'], {
    session: sessionName,
    cwd: workingDir,
    timeoutMs: 30_000,
  }).catch(() => {});

  try {
    const captures: DesignAnalysis[] = [];
    const responsiveSnapshots: ResponsiveSnapshot[] = [];
    let animationTokens: AnimationToken[] = [];

    // 3. For each viewport: set size → run unified extraction (tokens + scroll + animations)
    for (const viewport of responsiveViewports) {
      await runAgentBrowserJson(
        ['set', 'viewport', String(viewport.width), String(viewport.height)],
        { session: sessionName, cwd: workingDir },
      );

      const result = await runAgentBrowserJson(['eval', UNIFIED_SCRIPT], {
        session: sessionName,
        cwd: workingDir,
        timeoutMs: 45_000,
      });

      if (!result.success) {
        throw new Error(`Extraction failed: ${result.error ?? 'Unknown error'}`);
      }

      const unified = result.data.result as UnifiedResult | undefined;
      if (!unified) {
        throw new Error('Extraction returned empty result');
      }

      const normalized = normalizeResult(unified.designTokens);
      captures.push(normalized);
      responsiveSnapshots.push(toResponsiveSnapshot(viewport.label, normalized));

      // Only process animations from the first (desktop) viewport
      if (animationTokens.length === 0 && unified.animations) {
        try {
          animationTokens = convertObserverResult(unified.animations);
          animationTokens = detectAnimationGroups(animationTokens);
        } catch {
          // Animation conversion is best-effort
        }
      }
    }

    // 4. Get accessibility snapshot
    const snapshotResult = await runAgentBrowserJson(['snapshot', '-c', '-d', '3'], {
      session: sessionName,
      cwd: workingDir,
    });

    // 5. Take full-page screenshot
    await runAgentBrowserJson(['screenshot', screenshotPath, '--full'], {
      session: sessionName,
      cwd: workingDir,
    });

    // 6. Merge results
    const merged = mergeAnalysis(captures);

    const mergedMotion: (MotionToken | AnimationToken)[] = [
      ...animationTokens,
      ...merged.motion.filter((legacyToken) =>
        !animationTokens.some((at) => at.selector === legacyToken.selector)
      ),
    ];

    return {
      ...merged,
      motion: mergedMotion,
      accessibilitySnapshot: (snapshotResult.data.snapshot as string | undefined) ?? undefined,
      responsiveSnapshots,
      stateStyles: merged.stateStyles ?? [],
    };
  } finally {
    // 7. Always close the browser session
    await runAgentBrowserJson(['close'], { session: sessionName, cwd: workingDir }).catch(() => {});
  }
}
