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

const EXTRACTION_SCRIPT = String.raw`(() => {
  const maxNodes = 2000;
  const nodes = Array.from(document.querySelectorAll('body *')).slice(0, maxNodes);

  const colorMap = new Map();
  const typographyMap = new Map();
  const componentList = [];
  const motionList = [];
  const layoutList = [];
  const variableMap = {};
  const stateStyleList = [];

  const componentTags = new Set(['button', 'a', 'input', 'select', 'textarea', 'nav', 'header', 'footer', 'form']);
  const maxComponents = 220;
  const maxMotion = 220;
  const maxStateStyles = 260;

  function normalizeWhitespace(text) {
    return (text || '').replace(/\s+/g, ' ').trim();
  }

  function pushColor(value, sample) {
    if (!value || value === 'transparent' || value === 'rgba(0, 0, 0, 0)') {
      return;
    }

    const parsed = parseCssColor(value);
    if (!parsed) {
      return;
    }

    const key = parsed.toUpperCase();
    const entry = colorMap.get(key) || { hex: key, count: 0, samples: [] };
    entry.count += 1;
    if (sample && entry.samples.length < 5 && !entry.samples.includes(sample)) {
      entry.samples.push(sample);
    }
    colorMap.set(key, entry);
  }

  function parseCssColor(input) {
    if (!input) {
      return null;
    }

    const value = input.toString().trim().toLowerCase();

    if (value.startsWith('#')) {
      if (value.length === 4) {
        return ('#' + value[1] + value[1] + value[2] + value[2] + value[3] + value[3]);
      }
      if (value.length === 7) {
        return value;
      }
      return null;
    }

    const rgbMatch = value.match(/rgba?\(([^)]+)\)/);
    if (rgbMatch) {
      const parts = rgbMatch[1].split(',').map((part) => part.trim());
      const r = Number(parts[0]);
      const g = Number(parts[1]);
      const b = Number(parts[2]);
      if ([r, g, b].some((n) => Number.isNaN(n))) {
        return null;
      }
      const toHex = (n) => Math.max(0, Math.min(255, n)).toString(16).padStart(2, '0');
      return '#' + toHex(r) + toHex(g) + toHex(b);
    }

    return null;
  }

  function buildSelector(el) {
    const tag = el.tagName.toLowerCase();
    if (el.id) {
      return tag + '#' + el.id;
    }

    if (typeof el.className === 'string' && el.className.trim()) {
      const firstClass = el.className.trim().split(/\s+/).slice(0, 2).join('.');
      if (firstClass) {
        return tag + '.' + firstClass;
      }
    }

    return tag;
  }

  function addTypography(style) {
    const key = [style.fontFamily, style.fontSize, style.fontWeight, style.lineHeight].join('|');
    const existing = typographyMap.get(key) || {
      fontFamily: style.fontFamily,
      fontSize: style.fontSize,
      fontWeight: style.fontWeight,
      lineHeight: style.lineHeight,
      count: 0,
    };
    existing.count += 1;
    typographyMap.set(key, existing);
  }

  function shouldCaptureAsComponent(el, selector) {
    const tag = el.tagName.toLowerCase();
    if (componentTags.has(tag)) {
      return true;
    }

    const className = typeof el.className === 'string' ? el.className.toLowerCase() : '';
    if (className.includes('btn') || className.includes('button') || className.includes('card') || className.includes('hero')) {
      return true;
    }

    if (el.getAttribute('role') === 'button' || el.getAttribute('role') === 'navigation') {
      return true;
    }

    return selector.startsWith('section.') || selector.startsWith('div.card');
  }

  function addPseudoStateStyles() {
    const stateKinds = [':hover', ':focus', ':active'];

    for (const sheet of Array.from(document.styleSheets)) {
      let rules;
      try {
        rules = sheet.cssRules;
      } catch {
        continue;
      }

      if (!rules) {
        continue;
      }

      for (const rule of Array.from(rules)) {
        const selectorText = 'selectorText' in rule ? String(rule.selectorText || '') : '';
        const style = 'style' in rule ? rule.style : undefined;
        if (!selectorText || !style) {
          continue;
        }

        for (const stateKind of stateKinds) {
          if (!selectorText.includes(stateKind)) {
            continue;
          }

          const declarations = {};
          for (const prop of ['color', 'background-color', 'border-color', 'box-shadow', 'transform', 'transition', 'opacity']) {
            const value = style.getPropertyValue(prop);
            if (value) {
              declarations[prop] = value;
            }
          }

          if (Object.keys(declarations).length === 0) {
            continue;
          }

          const cleanSelector = selectorText.split(stateKind).join('').trim();
          stateStyleList.push({
            selector: cleanSelector || selectorText,
            state: stateKind.slice(1),
            declarations,
          });

          if (stateStyleList.length >= maxStateStyles) {
            return;
          }
        }
      }
    }
  }

  nodes.forEach((el) => {
    const style = window.getComputedStyle(el);

    if (style.display === 'none' || style.visibility === 'hidden' || Number(style.opacity) === 0) {
      return;
    }

    const selector = buildSelector(el);
    pushColor(style.color, selector + ':color');
    pushColor(style.backgroundColor, selector + ':background');

    if (style.borderColor && style.borderColor !== 'rgba(0, 0, 0, 0)') {
      pushColor(style.borderColor, selector + ':border');
    }

    const hasText = normalizeWhitespace(el.textContent || '').length > 0;
    if (hasText) {
      addTypography(style);
    }

    if (shouldCaptureAsComponent(el, selector) && componentList.length < maxComponents) {
      componentList.push({
        kind: inferComponentKind(el),
        tag: el.tagName.toLowerCase(),
        selector,
        text: normalizeWhitespace(el.textContent || '').slice(0, 90),
        className: typeof el.className === 'string' ? normalizeWhitespace(el.className) : '',
        styles: {
          color: style.color,
          backgroundColor: style.backgroundColor,
          borderRadius: style.borderRadius,
          border: style.border,
          padding: style.padding,
          margin: style.margin,
          fontSize: style.fontSize,
          fontWeight: style.fontWeight,
          boxShadow: style.boxShadow,
        },
      });
    }

    const hasTransition = style.transitionDuration && style.transitionDuration !== '0s';
    const hasAnimation = style.animationName && style.animationName !== 'none';
    const hasTransform = style.transform && style.transform !== 'none';

    if ((hasTransition || hasAnimation || hasTransform) && motionList.length < maxMotion) {
      motionList.push({
        selector,
        transition: style.transition,
        animation: style.animation,
        transform: style.transform,
      });
    }
  });

  const layoutSelectors = Array.from(document.querySelectorAll('header, nav, main, section, article, aside, footer')).slice(0, 160);

  layoutSelectors.forEach((el) => {
    layoutList.push({
      tag: el.tagName.toLowerCase(),
      selector: buildSelector(el),
      role: el.getAttribute('role') || '',
      children: el.children.length,
    });
  });

  [document.documentElement, document.body].forEach((root) => {
    if (!root) {
      return;
    }

    const style = window.getComputedStyle(root);
    for (const propertyName of style) {
      if (!propertyName.startsWith('--')) {
        continue;
      }
      const value = style.getPropertyValue(propertyName).trim();
      if (value) {
        variableMap[propertyName] = value;
      }
    }
  });

  function inferComponentKind(el) {
    const tag = el.tagName.toLowerCase();
    const className = typeof el.className === 'string' ? el.className.toLowerCase() : '';
    if (tag === 'button' || className.includes('btn')) {
      return 'button';
    }
    if (tag === 'a') {
      return 'link';
    }
    if (tag === 'input' || tag === 'textarea' || tag === 'select') {
      return 'form-control';
    }
    if (tag === 'nav' || className.includes('nav')) {
      return 'navigation';
    }
    if (className.includes('card')) {
      return 'card';
    }
    if (tag === 'header') {
      return 'header';
    }
    if (tag === 'footer') {
      return 'footer';
    }
    if (className.includes('hero')) {
      return 'hero';
    }
    return tag;
  }

  addPseudoStateStyles();

  const colors = Array.from(colorMap.values()).sort((a, b) => b.count - a.count).slice(0, 70);
  const typography = Array.from(typographyMap.values()).sort((a, b) => b.count - a.count).slice(0, 90);

  return {
    pageTitle: document.title,
    pageUrl: window.location.href,
    viewport: {
      width: window.innerWidth,
      height: window.innerHeight,
    },
    colors,
    typography,
    components: componentList,
    motion: motionList,
    layout: layoutList,
    cssVariables: variableMap,
    stateStyles: stateStyleList,
  };
})();`;

const PAGE_SUMMARY_SCRIPT = String.raw`(() => {
  const h1 = document.querySelector('h1')?.textContent?.trim() || '';
  const navCount = document.querySelectorAll('nav a, header a').length;
  const ctaCount = document.querySelectorAll('button, a[role="button"], .btn, .button').length;
  return {
    title: document.title,
    url: window.location.href,
    summary: [h1, 'nav-links:' + navCount, 'ctas:' + ctaCount].filter(Boolean).join(' | '),
  };
})();`;

const ANIMATION_OBSERVER_SCRIPT = String.raw`(() => {
  const maxAnimations = 200;
  const result = {
    libraries: [],
    webAnimations: [],
    gsapTweens: [],
    lottiePlayers: [],
    scrollBindings: {
      hasScrollTrigger: false,
      hasIntersectionObserver: false,
      scrollTriggers: [],
      hasScrollSnap: false,
      hasScrollTimeline: false,
    },
  };

  function buildSelector(el) {
    if (!el || !el.tagName) return 'unknown';
    const tag = el.tagName.toLowerCase();
    if (el.id) return tag + '#' + el.id;
    if (typeof el.className === 'string' && el.className.trim()) {
      const firstClass = el.className.trim().split(/\s+/).slice(0, 2).join('.');
      if (firstClass) return tag + '.' + firstClass;
    }
    return tag;
  }

  /* Layer 1: Library Detection */
  try {
    if (typeof gsap !== 'undefined') {
      result.libraries.push({ name: 'gsap', version: typeof gsap.version === 'string' ? gsap.version : 'unknown' });
    }
    if (typeof ScrollTrigger !== 'undefined') {
      result.libraries.push({ name: 'scrolltrigger', version: 'detected' });
      result.scrollBindings.hasScrollTrigger = true;
    }
    if (typeof lottie !== 'undefined' || typeof bodymovin !== 'undefined') {
      result.libraries.push({ name: 'lottie', version: 'detected' });
    }
    if (document.querySelector('lottie-player, dotlottie-player')) {
      if (!result.libraries.some(function(l) { return l.name === 'lottie'; })) {
        result.libraries.push({ name: 'lottie', version: 'web-component' });
      }
    }
    if (document.querySelector('[data-framer-name], [data-framer-component-type]')) {
      result.libraries.push({ name: 'framer-motion', version: 'detected' });
    }
  } catch(e) {}

  /* Layer 2: Web Animations API */
  try {
    var animations = document.getAnimations();
    for (var ai = 0; ai < Math.min(animations.length, maxAnimations); ai++) {
      var anim = animations[ai];
      var effect = anim.effect;
      if (!effect || !effect.target) continue;

      var target = effect.target;
      var selector = buildSelector(target);

      var keyframes = [];
      try { keyframes = effect.getKeyframes(); } catch(e) {}

      var computedTiming = {};
      try { computedTiming = effect.getComputedTiming(); } catch(e) {}

      var timelineType = 'document';
      try {
        if (anim.timeline && anim.timeline.constructor) {
          var tlName = anim.timeline.constructor.name;
          if (tlName === 'ScrollTimeline') timelineType = 'scroll';
          else if (tlName === 'ViewTimeline') timelineType = 'view';
        }
      } catch(e) {}

      if (timelineType !== 'document') {
        result.scrollBindings.hasScrollTimeline = true;
      }

      result.webAnimations.push({
        selector: selector,
        playState: anim.playState,
        animationName: anim.animationName || anim.id || '',
        keyframes: keyframes.map(function(kf) {
          var props = {};
          for (var k in kf) {
            if (k !== 'offset' && k !== 'computedOffset' && k !== 'easing' && k !== 'composite') {
              props[k] = String(kf[k]);
            }
          }
          return {
            offset: kf.computedOffset != null ? kf.computedOffset : (kf.offset || 0),
            properties: props,
            easing: kf.easing || 'linear',
          };
        }),
        timing: {
          duration: typeof computedTiming.duration === 'number' ? computedTiming.duration : 0,
          delay: computedTiming.delay || 0,
          easing: computedTiming.easing || 'linear',
          iterations: computedTiming.iterations != null ? computedTiming.iterations : 1,
          direction: computedTiming.direction || 'normal',
          fillMode: computedTiming.fill || 'none',
        },
        timelineType: timelineType,
      });
    }
  } catch(e) {}

  /* Layer 3: GSAP Introspection */
  try {
    if (typeof gsap !== 'undefined' && gsap.globalTimeline) {
      var children = gsap.globalTimeline.getChildren(true, true, false);
      for (var gi = 0; gi < Math.min(children.length, maxAnimations); gi++) {
        var tween = children[gi];
        var targets = tween.targets ? tween.targets() : [];
        if (targets.length === 0) continue;

        var gsSelector = buildSelector(targets[0]);
        var vars = {};
        if (tween.vars) {
          for (var vk in tween.vars) {
            var vv = tween.vars[vk];
            if (typeof vv === 'number' || typeof vv === 'string') {
              vars[vk] = vv;
            }
          }
        }

        result.gsapTweens.push({
          selector: gsSelector,
          duration: typeof tween.duration === 'function' ? tween.duration() : 0,
          delay: typeof tween.delay === 'function' ? tween.delay() : 0,
          ease: tween.vars && tween.vars.ease ? tween.vars.ease : 'power1.out',
          vars: vars,
          startTime: typeof tween.startTime === 'function' ? tween.startTime() : 0,
        });
      }
    }
  } catch(e) {}

  /* Layer 4: Lottie Extraction */
  try {
    var lottieRef = (typeof lottie !== 'undefined') ? lottie : ((typeof bodymovin !== 'undefined') ? bodymovin : null);
    if (lottieRef && typeof lottieRef.getRegisteredAnimations === 'function') {
      var registered = lottieRef.getRegisteredAnimations();
      for (var li = 0; li < Math.min(registered.length, 20); li++) {
        var la = registered[li];
        var container = la.wrapper || la.container;
        result.lottiePlayers.push({
          selector: container ? buildSelector(container) : 'lottie-unknown',
          frameRate: la.frameRate || (la.animationData && la.animationData.fr) || 0,
          totalFrames: la.totalFrames || (la.animationData && la.animationData.op) || 0,
          duration: typeof la.getDuration === 'function' ? la.getDuration(false) : 0,
        });
      }
    }

    var players = document.querySelectorAll('lottie-player, dotlottie-player');
    for (var pi = 0; pi < Math.min(players.length, 20); pi++) {
      var pSelector = buildSelector(players[pi]);
      if (!result.lottiePlayers.some(function(l) { return l.selector === pSelector; })) {
        result.lottiePlayers.push({ selector: pSelector, frameRate: 0, totalFrames: 0, duration: 0 });
      }
    }
  } catch(e) {}

  /* Layer 5: Passive Scroll Detection */
  try {
    if (typeof ScrollTrigger !== 'undefined' && typeof ScrollTrigger.getAll === 'function') {
      var triggers = ScrollTrigger.getAll();
      for (var si = 0; si < Math.min(triggers.length, 50); si++) {
        var st = triggers[si];
        result.scrollBindings.scrollTriggers.push({
          triggerSelector: st.trigger ? buildSelector(st.trigger) : '',
          isActive: !!st.isActive,
        });
      }
    }
  } catch(e) {}

  try {
    var scrollSnap = window.getComputedStyle(document.documentElement).scrollSnapType;
    if (scrollSnap && scrollSnap !== 'none') {
      result.scrollBindings.hasScrollSnap = true;
    }
  } catch(e) {}

  return result;
})();`;

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

function convertObserverResult(raw: RawAnimObserverResult): AnimationToken[] {
  const tokens: AnimationToken[] = [];
  const libraryNames = new Set(raw.libraries.map((l) => l.name));

  // Convert Web Animations API results
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

    // Detect physics from keyframes
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

  // Convert GSAP tweens
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

  // Convert Lottie players
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

function parseStylesFromGetStyles(data: unknown): Record<string, string> {
  const payload = data as { elements?: Array<{ styles?: Record<string, string | null> }> };
  const first = payload.elements?.[0];
  const styles = first?.styles ?? {};
  const out: Record<string, string> = {};

  for (const [key, value] of Object.entries(styles)) {
    if (typeof value === 'string' && value.trim()) {
      out[key] = value;
    }
  }

  return out;
}

async function collectInteractiveStateStyles(params: {
  sessionName: string;
  workingDir: string;
}): Promise<StateStyleToken[]> {
  const states: StateStyleToken[] = [];
  const snapshot = await runAgentBrowserJson(['snapshot', '-i', '-d', '2'], {
    session: params.sessionName,
    cwd: params.workingDir,
  });

  const refs = ((snapshot.data.refs as Record<string, unknown>) ?? {});
  const refIds = Object.keys(refs).slice(0, 8);

  for (const refId of refIds) {
    const ref = `@${refId}`;

    await runAgentBrowserJson(['hover', ref], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);
    const hoverStyles = await runAgentBrowserJson(['get', 'styles', ref], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);
    if (hoverStyles?.success) {
      const declarations = parseStylesFromGetStyles(hoverStyles.data);
      if (Object.keys(declarations).length > 0) {
        states.push({ selector: ref, state: 'hover', declarations });
      }
    }

    await runAgentBrowserJson(['focus', ref], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);
    const focusStyles = await runAgentBrowserJson(['get', 'styles', ref], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);
    if (focusStyles?.success) {
      const declarations = parseStylesFromGetStyles(focusStyles.data);
      if (Object.keys(declarations).length > 0) {
        states.push({ selector: ref, state: 'focus', declarations });
      }
    }
  }

  return states;
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

async function getCurrentUrl(params: { sessionName: string; workingDir: string }): Promise<string | undefined> {
  const response = await runAgentBrowserJson(['get', 'url'], {
    session: params.sessionName,
    cwd: params.workingDir,
  }).catch(() => undefined);

  return response?.success ? (response.data.url as string | undefined) : undefined;
}

async function collectJourney(params: {
  sessionName: string;
  workingDir: string;
  maxSteps: number;
}): Promise<JourneyStep[]> {
  const steps: JourneyStep[] = [];

  if (params.maxSteps <= 0) {
    return steps;
  }

  const snapshot = await runAgentBrowserJson(['snapshot', '-i', '-d', '2'], {
    session: params.sessionName,
    cwd: params.workingDir,
  });

  const refs = ((snapshot.data.refs as Record<string, { role?: string }>) ?? {});
  const clickable = Object.entries(refs)
    .filter(([, value]) => ['link', 'button', 'menuitem', 'tab'].includes(String(value?.role ?? '')))
    .slice(0, params.maxSteps);

  for (let i = 0; i < clickable.length; i += 1) {
    const [refId] = clickable[i];
    const ref = `@${refId}`;
    const fromUrl = await getCurrentUrl(params);

    const clickResult = await runAgentBrowserJson(['click', ref], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);

    if (!clickResult?.success) {
      continue;
    }

    await runAgentBrowserJson(['wait', '1200'], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);

    const summaryResult = await runAgentBrowserJson(['eval', PAGE_SUMMARY_SCRIPT], {
      session: params.sessionName,
      cwd: params.workingDir,
    }).catch(() => undefined);

    const summaryData = (summaryResult?.data.result as Record<string, unknown> | undefined) ?? {};
    const toUrl = (summaryData.url as string | undefined) ?? (await getCurrentUrl(params));

    if (toUrl && fromUrl && toUrl !== fromUrl) {
      steps.push({
        step: i + 1,
        action: `click ${ref}`,
        fromUrl,
        toUrl,
        title: summaryData.title as string | undefined,
        summary: summaryData.summary as string | undefined,
      });

      await runAgentBrowserJson(['back'], {
        session: params.sessionName,
        cwd: params.workingDir,
      }).catch(() => undefined);
      await runAgentBrowserJson(['wait', '900'], {
        session: params.sessionName,
        cwd: params.workingDir,
      }).catch(() => undefined);
    }
  }

  return steps;
}

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
    journeySteps = 3,
    responsiveViewports = DEFAULT_VIEWPORTS,
  } = params;

  await fs.ensureDir(path.dirname(screenshotPath));

  await runAgentBrowserJson(['open', url], { session: sessionName, cwd: workingDir });
  try {
    const captures: DesignAnalysis[] = [];
    const responsiveSnapshots: ResponsiveSnapshot[] = [];

    for (const viewport of responsiveViewports) {
      await runAgentBrowserJson(['set', 'viewport', String(viewport.width), String(viewport.height)], {
        session: sessionName,
        cwd: workingDir,
      });
      await runAgentBrowserJson(['wait', '900'], {
        session: sessionName,
        cwd: workingDir,
      });

      const extraction = await runAgentBrowserJson(['eval', EXTRACTION_SCRIPT], {
        session: sessionName,
        cwd: workingDir,
      });

      if (!extraction.success) {
        throw new Error(`Extraction failed: ${extraction.error ?? 'Unknown error'}`);
      }

      const normalized = normalizeResult((extraction.data.result as Record<string, unknown>) ?? {});
      captures.push(normalized);
      responsiveSnapshots.push(toResponsiveSnapshot(viewport.label, normalized));
    }

    await runAgentBrowserJson(['set', 'viewport', '1440', '1200'], {
      session: sessionName,
      cwd: workingDir,
    }).catch(() => undefined);

    // Scroll through the page to trigger lazy-loaded animation libraries (GSAP, ScrollTrigger, etc.)
    try {
      const pageInfo = await runAgentBrowserJson(['eval',
        `({ height: Math.max(document.body.scrollHeight, document.documentElement.scrollHeight), vh: window.innerHeight })`
      ], { session: sessionName, cwd: workingDir });
      const { height = 5000, vh = 800 } = (pageInfo.data.result as { height?: number; vh?: number }) ?? {};
      const scrollSteps = Math.min(Math.ceil(height / vh), 15);
      const stepSize = Math.ceil(height / scrollSteps);
      for (let i = 1; i <= scrollSteps; i++) {
        await runAgentBrowserJson(['eval', `window.scrollTo({top:${i * stepSize},behavior:"instant"});true`],
          { session: sessionName, cwd: workingDir });
        await runAgentBrowserJson(['wait', '200'], { session: sessionName, cwd: workingDir });
      }
      await runAgentBrowserJson(['eval', 'window.scrollTo({top:0,behavior:"instant"});true'],
        { session: sessionName, cwd: workingDir });
      await runAgentBrowserJson(['wait', '1500'], { session: sessionName, cwd: workingDir });
    } catch {
      // Scroll is best-effort; continue to animation capture
    }

    // Run animation observer script (once, at desktop viewport)
    let animationTokens: AnimationToken[] = [];
    try {
      const animResult = await runAgentBrowserJson(['eval', ANIMATION_OBSERVER_SCRIPT], {
        session: sessionName,
        cwd: workingDir,
      });
      if (animResult.success && animResult.data.result) {
        const rawAnimData = animResult.data.result as RawAnimObserverResult;
        animationTokens = convertObserverResult(rawAnimData);
        animationTokens = detectAnimationGroups(animationTokens);
      }
    } catch {
      // Animation capture is best-effort; don't fail the whole extraction
    }

    const snapshotResult = await runAgentBrowserJson(['snapshot', '-c', '-d', '3'], {
      session: sessionName,
      cwd: workingDir,
    });

    const interactiveStates = await collectInteractiveStateStyles({
      sessionName,
      workingDir,
    });

    const journey = await collectJourney({
      sessionName,
      workingDir,
      maxSteps: journeySteps,
    });

    await runAgentBrowserJson(['screenshot', screenshotPath, '--full'], {
      session: sessionName,
      cwd: workingDir,
    });

    const merged = mergeAnalysis(captures);
    const stateStyles = [...(merged.stateStyles ?? []), ...interactiveStates].slice(0, 400);

    // Merge: prefer new AnimationTokens, fall back to legacy MotionTokens
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
      stateStyles,
      journey,
    };
  } finally {
    await runAgentBrowserJson(['close'], { session: sessionName, cwd: workingDir }).catch(() => undefined);
  }
}
