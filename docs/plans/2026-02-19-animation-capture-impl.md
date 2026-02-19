# Animation Capture System Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the shallow MotionToken (4 raw CSS strings) with a rich AnimationToken system that detects animation libraries (GSAP, Lottie, Framer Motion), extracts keyframes via Web Animations API, classifies motion intent, detects physics-based animations, and groups staggered sequences.

**Architecture:** A new `ANIMATION_OBSERVER_SCRIPT` is injected into the page via Agent Browser `eval` alongside the existing extraction. It runs 5 detection layers (library detection, WAAPI, GSAP introspection, Lottie extraction, passive scroll detection). Results are post-processed in Node by a new `classify.ts` module that handles motion intent classification, physics detection, and animation grouping. The render layer outputs rich grouped markdown sections.

**Tech Stack:** TypeScript (strict, ESM, NodeNext), Node.js 20+, node:test for testing, Agent Browser CLI for browser automation.

**Project root:** `/Users/arnavdas/packages/design-brain-memory`

**Build:** `npm run build` (tsc)
**Test:** `npm run build && node --test tests/*.test.mjs`

---

### Task 1: Add AnimationToken types

**Files:**
- Modify: `src/types.ts`

**Step 1: Write the new types**

Replace `MotionToken` (lines 26-31) and add all supporting types. Keep `MotionToken` as a deprecated alias for backward compatibility.

In `src/types.ts`, replace lines 26-31:

```typescript
// OLD:
export interface MotionToken {
  selector: string;
  transition: string;
  animation: string;
  transform: string;
}
```

With:

```typescript
/* ─── Animation capture types ─── */

export type AnimationLibrary = 'css' | 'gsap' | 'lottie' | 'framer-motion' | 'react-spring' | 'motion-one' | 'unknown';
export type MotionIntent = 'fade' | 'slide' | 'scale' | 'rotate' | 'color-shift' | 'spring' | 'bounce' | 'morph' | 'reveal' | 'parallax' | 'complex';
export type TriggerEvent = 'load' | 'hover' | 'focus' | 'click' | 'scroll' | 'viewport-enter' | 'media-query' | 'unknown';

export interface KeyframeStop {
  offset: number;
  properties: Record<string, string>;
  easing?: string;
}

export interface AnimationTiming {
  duration: number;
  delay: number;
  easing: string;
  iterations: number;
  direction: 'normal' | 'reverse' | 'alternate' | 'alternate-reverse';
  fillMode: 'none' | 'forwards' | 'backwards' | 'both';
}

export interface ScrollBinding {
  triggerSelector?: string;
  hasScrollTrigger: boolean;
  hasIntersectionObserver: boolean;
  scrollTimelineAxis?: 'block' | 'inline';
}

export interface PhysicsParams {
  type: 'spring' | 'bounce' | 'inertia';
  mass?: number;
  stiffness?: number;
  damping?: number;
  oscillationCount?: number;
  overshootPercent?: number;
}

export interface AnimationGroup {
  groupId: string;
  role: 'lead' | 'follower';
  staggerDelay?: number;
}

export interface AnimationToken {
  selector: string;
  library: AnimationLibrary;
  motionIntent: MotionIntent;
  timing?: AnimationTiming;
  keyframes?: KeyframeStop[];
  trigger: TriggerEvent;
  scrollBinding?: ScrollBinding;
  physics?: PhysicsParams;
  group?: AnimationGroup;
  gsapVars?: Record<string, unknown>;
  lottieMetadata?: { frameRate: number; totalFrames: number; duration: number };
  rawTransition?: string;
  rawAnimation?: string;
  rawTransform?: string;
}

/** @deprecated Use AnimationToken instead */
export interface MotionToken {
  selector: string;
  transition: string;
  animation: string;
  transform: string;
}
```

**Step 2: Update DesignAnalysis**

Change the `motion` field in `DesignAnalysis` (line 78) to support both old and new tokens:

```typescript
// In DesignAnalysis, change line 78:
motion: (MotionToken | AnimationToken)[];
```

**Step 3: Build to verify types compile**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build`

Expected: Type errors in files that reference MotionToken fields directly. This is expected — we'll fix them in subsequent tasks.

**Step 4: Commit**

```bash
git add src/types.ts
git commit -m "feat(types): add AnimationToken with library detection, physics, and grouping"
```

---

### Task 2: Create classify.ts with tests (TDD)

**Files:**
- Create: `src/classify.ts`
- Create: `tests/classify.test.mjs`

**Step 1: Write the failing tests**

Create `tests/classify.test.mjs`:

```javascript
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  classifyMotionIntent,
  detectPhysics,
  detectAnimationGroups,
  classifyGsapEasing,
} from '../dist/classify.js';

/* ─── classifyMotionIntent ─── */

test('classifyMotionIntent: opacity-only → fade', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { opacity: '0' } },
    { offset: 1, properties: { opacity: '1' } },
  ]);
  assert.equal(result, 'fade');
});

test('classifyMotionIntent: translateX → slide', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'translateX(-100px)' } },
    { offset: 1, properties: { transform: 'translateX(0px)' } },
  ]);
  assert.equal(result, 'slide');
});

test('classifyMotionIntent: translateY → slide', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'translateY(50px)' } },
    { offset: 1, properties: { transform: 'translateY(0px)' } },
  ]);
  assert.equal(result, 'slide');
});

test('classifyMotionIntent: scale → scale', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'scale(0)' } },
    { offset: 1, properties: { transform: 'scale(1)' } },
  ]);
  assert.equal(result, 'scale');
});

test('classifyMotionIntent: rotate → rotate', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'rotate(0deg)' } },
    { offset: 1, properties: { transform: 'rotate(360deg)' } },
  ]);
  assert.equal(result, 'rotate');
});

test('classifyMotionIntent: backgroundColor → color-shift', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { backgroundColor: 'rgb(255,0,0)' } },
    { offset: 1, properties: { backgroundColor: 'rgb(0,0,255)' } },
  ]);
  assert.equal(result, 'color-shift');
});

test('classifyMotionIntent: clip-path → reveal', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { clipPath: 'inset(0 100% 0 0)' } },
    { offset: 1, properties: { clipPath: 'inset(0 0 0 0)' } },
  ]);
  assert.equal(result, 'reveal');
});

test('classifyMotionIntent: opacity + translate → complex', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { opacity: '0', transform: 'translateY(20px)' } },
    { offset: 1, properties: { opacity: '1', transform: 'translateY(0px)' } },
  ]);
  assert.equal(result, 'complex');
});

test('classifyMotionIntent: empty keyframes → complex', () => {
  const result = classifyMotionIntent([]);
  assert.equal(result, 'complex');
});

/* ─── detectPhysics ─── */

test('detectPhysics: spring oscillation detected', () => {
  // Values: 0 → 1.15 → 0.95 → 1.02 → 1.0 (overshoot + oscillation)
  const keyframes = [
    { offset: 0, properties: { transform: 'translateX(0px)' } },
    { offset: 0.3, properties: { transform: 'translateX(115px)' } },
    { offset: 0.5, properties: { transform: 'translateX(95px)' } },
    { offset: 0.7, properties: { transform: 'translateX(102px)' } },
    { offset: 1, properties: { transform: 'translateX(100px)' } },
  ];
  const result = detectPhysics(keyframes, 'translateX');
  assert.ok(result);
  assert.equal(result.type, 'spring');
  assert.ok(result.oscillationCount >= 2);
  assert.ok(result.overshootPercent > 0);
});

test('detectPhysics: bounce detected (single overshoot)', () => {
  const keyframes = [
    { offset: 0, properties: { transform: 'translateY(0px)' } },
    { offset: 0.5, properties: { transform: 'translateY(110px)' } },
    { offset: 1, properties: { transform: 'translateY(100px)' } },
  ];
  const result = detectPhysics(keyframes, 'translateY');
  assert.ok(result);
  assert.equal(result.type, 'bounce');
});

test('detectPhysics: linear motion returns null', () => {
  const keyframes = [
    { offset: 0, properties: { transform: 'translateX(0px)' } },
    { offset: 0.5, properties: { transform: 'translateX(50px)' } },
    { offset: 1, properties: { transform: 'translateX(100px)' } },
  ];
  const result = detectPhysics(keyframes, 'translateX');
  assert.equal(result, null);
});

/* ─── classifyGsapEasing ─── */

test('classifyGsapEasing: elastic → spring', () => {
  const result = classifyGsapEasing('elastic.out(1, 0.3)');
  assert.ok(result);
  assert.equal(result.type, 'spring');
});

test('classifyGsapEasing: bounce → bounce', () => {
  const result = classifyGsapEasing('bounce.out');
  assert.ok(result);
  assert.equal(result.type, 'bounce');
});

test('classifyGsapEasing: back → spring', () => {
  const result = classifyGsapEasing('back.out(1.7)');
  assert.ok(result);
  assert.equal(result.type, 'spring');
});

test('classifyGsapEasing: power1 → null (not physics)', () => {
  const result = classifyGsapEasing('power1.out');
  assert.equal(result, null);
});

/* ─── detectAnimationGroups ─── */

test('detectAnimationGroups: staggered elements grouped', () => {
  const tokens = [
    {
      selector: '.item-1', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 0, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
    {
      selector: '.item-2', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 100, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
    {
      selector: '.item-3', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 200, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
  ];

  const result = detectAnimationGroups(tokens);
  assert.equal(result.length, 3);
  assert.equal(result[0].group.role, 'lead');
  assert.equal(result[1].group.role, 'follower');
  assert.equal(result[1].group.staggerDelay, 100);
  assert.equal(result[2].group.role, 'follower');
  assert.equal(result[2].group.staggerDelay, 200);
  // All share same groupId
  assert.equal(result[0].group.groupId, result[1].group.groupId);
});

test('detectAnimationGroups: unrelated animations not grouped', () => {
  const tokens = [
    {
      selector: '.a', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 0, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
    {
      selector: '.b', library: 'gsap', motionIntent: 'slide', trigger: 'hover',
      timing: { duration: 600, delay: 0, easing: 'ease-in', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { transform: 'translateX(0)' } }, { offset: 1, properties: { transform: 'translateX(100px)' } }],
    },
  ];

  const result = detectAnimationGroups(tokens);
  assert.equal(result.length, 2);
  assert.equal(result[0].group, undefined);
  assert.equal(result[1].group, undefined);
});
```

**Step 2: Run tests to verify they fail**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build && node --test tests/classify.test.mjs`

Expected: FAIL — `../dist/classify.js` does not exist.

**Step 3: Write the classify.ts implementation**

Create `src/classify.ts`:

```typescript
import type { AnimationToken, KeyframeStop, PhysicsParams, AnimationGroup } from './types.js';

/**
 * Classify the motion intent of an animation based on its keyframe properties.
 */
export function classifyMotionIntent(keyframes: KeyframeStop[]): AnimationToken['motionIntent'] {
  if (keyframes.length === 0) return 'complex';

  const allProps = new Set<string>();
  for (const kf of keyframes) {
    for (const prop of Object.keys(kf.properties)) {
      allProps.add(prop);
    }
  }

  const hasOpacity = allProps.has('opacity');
  const hasTransform = allProps.has('transform');
  const hasColor = allProps.has('backgroundColor') || allProps.has('color') || allProps.has('borderColor');
  const hasClipPath = allProps.has('clipPath');
  const hasWidthHeight = allProps.has('width') || allProps.has('height');

  // Count distinct categories
  const categories: string[] = [];
  if (hasOpacity) categories.push('opacity');
  if (hasTransform) categories.push('transform');
  if (hasColor) categories.push('color');
  if (hasClipPath || hasWidthHeight) categories.push('reveal');

  if (categories.length > 1) return 'complex';
  if (categories.length === 0) return 'complex';

  if (hasOpacity && !hasTransform) return 'fade';
  if (hasColor) return 'color-shift';
  if (hasClipPath || hasWidthHeight) return 'reveal';

  if (hasTransform) {
    return classifyTransformIntent(keyframes);
  }

  return 'complex';
}

function classifyTransformIntent(keyframes: KeyframeStop[]): AnimationToken['motionIntent'] {
  const transforms = keyframes
    .map((kf) => kf.properties.transform ?? '')
    .filter(Boolean);

  const hasTranslate = transforms.some((t) => /translate[XY]?\s*\(/.test(t));
  const hasScale = transforms.some((t) => /scale[XY]?\s*\(/.test(t));
  const hasRotate = transforms.some((t) => /rotate[XYZ]?\s*\(/.test(t));

  const count = [hasTranslate, hasScale, hasRotate].filter(Boolean).length;
  if (count > 1) return 'complex';

  if (hasTranslate) return 'slide';
  if (hasScale) return 'scale';
  if (hasRotate) return 'rotate';

  return 'complex';
}

/**
 * Extract a numeric value from a transform function at a specific keyframe.
 * e.g., "translateX(100px)" → 100
 */
function extractNumericFromTransform(transformStr: string, fnName: string): number | null {
  const re = new RegExp(`${fnName}\\s*\\(\\s*(-?[\\d.]+)`);
  const match = transformStr.match(re);
  return match ? parseFloat(match[1]) : null;
}

/**
 * Detect physics-based motion (spring/bounce) from keyframe value progressions.
 * Looks for overshoot and oscillation around the final value.
 */
export function detectPhysics(
  keyframes: KeyframeStop[],
  trackProperty: string,
): PhysicsParams | null {
  if (keyframes.length < 3) return null;

  const values: number[] = [];
  for (const kf of keyframes) {
    const transformStr = kf.properties.transform ?? kf.properties[trackProperty] ?? '';
    const numericVal = extractNumericFromTransform(transformStr, trackProperty)
      ?? parseFloat(transformStr);
    if (Number.isNaN(numericVal)) return null;
    values.push(numericVal);
  }

  if (values.length < 3) return null;

  const finalValue = values[values.length - 1];
  const startValue = values[0];
  const range = Math.abs(finalValue - startValue);
  if (range === 0) return null;

  // Count zero-crossings relative to final value
  let crossings = 0;
  let maxOvershoot = 0;
  for (let i = 1; i < values.length - 1; i++) {
    const prevDelta = values[i - 1] - finalValue;
    const currDelta = values[i] - finalValue;
    if (prevDelta * currDelta < 0) {
      crossings++;
    }
    const overshoot = Math.abs(currDelta);
    if (overshoot > maxOvershoot) {
      maxOvershoot = overshoot;
    }
  }

  // Check if any intermediate value overshoots the final value
  const overshoots = values.some((v, i) => {
    if (i === 0 || i === values.length - 1) return false;
    if (finalValue > startValue) return v > finalValue;
    return v < finalValue;
  });

  if (!overshoots) return null;

  const overshootPercent = Math.round((maxOvershoot / range) * 100);

  if (crossings >= 2) {
    return {
      type: 'spring',
      oscillationCount: crossings,
      overshootPercent,
    };
  }

  return {
    type: 'bounce',
    oscillationCount: crossings || 1,
    overshootPercent,
  };
}

/**
 * Map GSAP easing string to physics params when applicable.
 */
export function classifyGsapEasing(easeString: string): PhysicsParams | null {
  const lower = easeString.toLowerCase();

  if (lower.includes('elastic')) {
    return { type: 'spring', oscillationCount: 3 };
  }
  if (lower.includes('bounce')) {
    return { type: 'bounce', oscillationCount: 4 };
  }
  if (lower.includes('back')) {
    return { type: 'spring', oscillationCount: 1, overshootPercent: 10 };
  }

  return null;
}

/**
 * Detect animation groups (staggered sequences) by matching tokens
 * with the same motionIntent, library, duration, and easing but different delays.
 */
export function detectAnimationGroups<T extends Pick<AnimationToken, 'selector' | 'motionIntent' | 'library' | 'timing' | 'keyframes' | 'trigger'>>(
  tokens: T[],
): Array<T & { group?: AnimationGroup }> {
  if (tokens.length < 2) {
    return tokens.map((t) => ({ ...t }));
  }

  // Group candidates by signature (same intent, library, duration, easing)
  const buckets = new Map<string, Array<{ index: number; delay: number }>>();

  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (!t.timing) continue;

    const sig = `${t.motionIntent}|${t.library}|${t.timing.duration}|${t.timing.easing}|${keyframeSignature(t.keyframes)}`;
    const bucket = buckets.get(sig) ?? [];
    bucket.push({ index: i, delay: t.timing.delay });
    buckets.set(sig, bucket);
  }

  const result: Array<T & { group?: AnimationGroup }> = tokens.map((t) => ({ ...t }));

  let groupCounter = 0;
  for (const [, bucket] of buckets) {
    if (bucket.length < 2) continue;

    // Sort by delay
    bucket.sort((a, b) => a.delay - b.delay);

    // Check if delays form a stagger pattern (roughly equal increments)
    const deltas: number[] = [];
    for (let i = 1; i < bucket.length; i++) {
      deltas.push(bucket[i].delay - bucket[i - 1].delay);
    }

    const avgDelta = deltas.reduce((sum, d) => sum + d, 0) / deltas.length;
    const isStagger = avgDelta > 0 && deltas.every((d) => Math.abs(d - avgDelta) <= avgDelta * 0.5);

    if (!isStagger) continue;

    groupCounter++;
    const groupId = `group-${groupCounter}`;
    const leadDelay = bucket[0].delay;

    for (let i = 0; i < bucket.length; i++) {
      const entry = bucket[i];
      result[entry.index] = {
        ...result[entry.index],
        group: {
          groupId,
          role: i === 0 ? 'lead' : 'follower',
          staggerDelay: i === 0 ? 0 : entry.delay - leadDelay,
        },
      };
    }
  }

  return result;
}

function keyframeSignature(keyframes?: KeyframeStop[]): string {
  if (!keyframes || keyframes.length === 0) return '';
  return keyframes.map((kf) => Object.keys(kf.properties).sort().join(',')).join('|');
}
```

**Step 4: Build and run tests**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build && node --test tests/classify.test.mjs`

Expected: All tests PASS.

**Step 5: Commit**

```bash
git add src/classify.ts tests/classify.test.mjs
git commit -m "feat: add motion classification, physics detection, animation grouping"
```

---

### Task 3: Write ANIMATION_OBSERVER_SCRIPT

**Files:**
- Modify: `src/extractFromUrl.ts`

This is the core browser-injected script. It runs inside the page via Agent Browser `eval` and returns raw animation data that the Node-side classify.ts will process.

**Step 1: Add the script constant after EXTRACTION_SCRIPT**

Add this after `EXTRACTION_SCRIPT` (after line 324) in `src/extractFromUrl.ts`:

```typescript
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

  /* ─── Layer 1: Library Detection ─── */

  if (typeof gsap !== 'undefined') {
    result.libraries.push({
      name: 'gsap',
      version: typeof gsap.version === 'string' ? gsap.version : 'unknown',
    });
  }

  if (typeof ScrollTrigger !== 'undefined') {
    result.libraries.push({ name: 'scrolltrigger', version: 'detected' });
    result.scrollBindings.hasScrollTrigger = true;
  }

  if (typeof lottie !== 'undefined' || typeof bodymovin !== 'undefined') {
    result.libraries.push({ name: 'lottie', version: 'detected' });
  }

  if (document.querySelector('lottie-player, dotlottie-player')) {
    if (!result.libraries.some(l => l.name === 'lottie')) {
      result.libraries.push({ name: 'lottie', version: 'web-component' });
    }
  }

  // Framer Motion heuristic: data-framer-* attributes
  if (document.querySelector('[data-framer-name], [data-framer-component-type]')) {
    result.libraries.push({ name: 'framer-motion', version: 'detected' });
  }

  /* ─── Layer 2: Web Animations API ─── */

  try {
    const animations = document.getAnimations();
    for (const anim of animations.slice(0, maxAnimations)) {
      const effect = anim.effect;
      if (!effect || !effect.target) continue;

      const target = effect.target;
      const selector = buildSelector(target);

      let keyframes = [];
      try { keyframes = effect.getKeyframes(); } catch {}

      let computedTiming = {};
      try { computedTiming = effect.getComputedTiming(); } catch {}

      let timelineType = 'document';
      try {
        if (anim.timeline && anim.timeline.constructor) {
          const name = anim.timeline.constructor.name;
          if (name === 'ScrollTimeline') timelineType = 'scroll';
          else if (name === 'ViewTimeline') timelineType = 'view';
        }
      } catch {}

      if (timelineType !== 'document') {
        result.scrollBindings.hasScrollTimeline = true;
      }

      result.webAnimations.push({
        selector,
        playState: anim.playState,
        animationName: anim.animationName || anim.id || '',
        keyframes: keyframes.map(kf => {
          const props = {};
          for (const [k, v] of Object.entries(kf)) {
            if (k !== 'offset' && k !== 'computedOffset' && k !== 'easing' && k !== 'composite') {
              props[k] = String(v);
            }
          }
          return {
            offset: kf.computedOffset ?? kf.offset ?? 0,
            properties: props,
            easing: kf.easing || 'linear',
          };
        }),
        timing: {
          duration: typeof computedTiming.duration === 'number' ? computedTiming.duration : 0,
          delay: computedTiming.delay || 0,
          easing: computedTiming.easing || 'linear',
          iterations: computedTiming.iterations ?? 1,
          direction: computedTiming.direction || 'normal',
          fillMode: computedTiming.fill || 'none',
        },
        timelineType,
      });
    }
  } catch {}

  /* ─── Layer 3: GSAP Introspection ─── */

  try {
    if (typeof gsap !== 'undefined' && gsap.globalTimeline) {
      const children = gsap.globalTimeline.getChildren(true, true, false);
      for (const tween of children.slice(0, maxAnimations)) {
        const targets = tween.targets ? tween.targets() : [];
        if (targets.length === 0) continue;

        const selector = buildSelector(targets[0]);
        const vars = {};
        if (tween.vars) {
          for (const [k, v] of Object.entries(tween.vars)) {
            if (typeof v === 'number' || typeof v === 'string') {
              vars[k] = v;
            }
          }
        }

        result.gsapTweens.push({
          selector,
          duration: typeof tween.duration === 'function' ? tween.duration() : 0,
          delay: typeof tween.delay === 'function' ? tween.delay() : 0,
          ease: tween.vars?.ease || 'power1.out',
          vars,
          startTime: typeof tween.startTime === 'function' ? tween.startTime() : 0,
        });
      }
    }
  } catch {}

  /* ─── Layer 4: Lottie Extraction ─── */

  try {
    const lottieRef = typeof lottie !== 'undefined' ? lottie : (typeof bodymovin !== 'undefined' ? bodymovin : null);
    if (lottieRef && typeof lottieRef.getRegisteredAnimations === 'function') {
      const registered = lottieRef.getRegisteredAnimations();
      for (const anim of registered.slice(0, 20)) {
        const container = anim.wrapper || anim.container;
        result.lottiePlayers.push({
          selector: container ? buildSelector(container) : 'lottie-unknown',
          frameRate: anim.frameRate || anim.animationData?.fr || 0,
          totalFrames: anim.totalFrames || anim.animationData?.op || 0,
          duration: typeof anim.getDuration === 'function' ? anim.getDuration(false) : 0,
        });
      }
    }

    // Web component detection
    const players = document.querySelectorAll('lottie-player, dotlottie-player');
    for (const player of Array.from(players).slice(0, 20)) {
      const selector = buildSelector(player);
      if (result.lottiePlayers.some(l => l.selector === selector)) continue;
      result.lottiePlayers.push({
        selector,
        frameRate: 0,
        totalFrames: 0,
        duration: 0,
      });
    }
  } catch {}

  /* ─── Layer 5: Passive Scroll Detection ─── */

  try {
    if (typeof ScrollTrigger !== 'undefined' && typeof ScrollTrigger.getAll === 'function') {
      const triggers = ScrollTrigger.getAll();
      for (const st of triggers.slice(0, 50)) {
        result.scrollBindings.scrollTriggers.push({
          triggerSelector: st.trigger ? buildSelector(st.trigger) : '',
          isActive: !!st.isActive,
        });
      }
    }
  } catch {}

  try {
    const scrollSnap = window.getComputedStyle(document.documentElement).scrollSnapType;
    if (scrollSnap && scrollSnap !== 'none') {
      result.scrollBindings.hasScrollSnap = true;
    }
  } catch {}

  /* ─── Helper ─── */

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

  return result;
})();`;
```

**Step 2: Build to verify the script string compiles**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build`

Expected: Compiles (the script is just a string constant).

**Step 3: Commit**

```bash
git add src/extractFromUrl.ts
git commit -m "feat: add ANIMATION_OBSERVER_SCRIPT with 5-layer detection"
```

---

### Task 4: Wire the animation observer into the extraction pipeline

**Files:**
- Modify: `src/extractFromUrl.ts`

**Step 1: Add imports for classify.ts and AnimationToken**

At top of `src/extractFromUrl.ts`, update imports:

```typescript
import type {
  AnimationToken,
  DesignAnalysis,
  MotionToken,
  ResponsiveSnapshot,
  StateStyleToken,
  JourneyStep,
} from './types.js';
import { classifyMotionIntent, detectPhysics, detectAnimationGroups, classifyGsapEasing } from './classify.js';
```

**Step 2: Add the raw-to-AnimationToken conversion function**

After `ANIMATION_OBSERVER_SCRIPT`, add:

```typescript
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
    const isCssAnim = wa.animationName && wa.animationName !== '';
    let library: AnimationToken['library'] = 'css';
    if (libraryNames.has('framer-motion')) {
      // Heuristic: Framer Motion uses WAAPI internally
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
        easing: tween.ease,
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
      // Infer intent from vars
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

    // Check if this tween is scroll-bound
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
```

**Step 3: Integrate into captureDesignFromUrl**

In `captureDesignFromUrl`, after the viewport loop but before interactive state capture (around line 653), add the animation observer call:

```typescript
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
```

Then in the return block (around line 673), merge animation tokens with the legacy motion array:

```typescript
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
```

**Step 4: Build**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build`

Expected: Compiles. Some type errors may arise in other files referencing `motion` — handle in Task 6.

**Step 5: Commit**

```bash
git add src/extractFromUrl.ts
git commit -m "feat: integrate animation observer into extraction pipeline"
```

---

### Task 5: Update render.ts for rich motion sections

**Files:**
- Modify: `src/render.ts`

**Step 1: Add AnimationToken import and type guard**

Update imports at top:

```typescript
import type {
  AnimationToken,
  ColorToken,
  ComponentToken,
  DesignBrainDatabase,
  InspirationRecord,
  MotionToken,
  ProjectRecord,
  TypographyToken,
} from './types.js';
```

Add a type guard function:

```typescript
function isAnimationToken(token: MotionToken | AnimationToken): token is AnimationToken {
  return 'library' in token && 'motionIntent' in token;
}
```

**Step 2: Replace aggregateMotion with new grouped rendering**

Replace the `aggregateMotion` function (lines 71-84) with:

```typescript
function aggregateMotion(records: InspirationRecord[]): Array<(MotionToken | AnimationToken) & { count: number }> {
  const map = new Map<string, (MotionToken | AnimationToken) & { count: number }>();

  for (const record of records) {
    for (const token of record.analysis.motion) {
      const key = isAnimationToken(token)
        ? `${token.selector}|${token.library}|${token.motionIntent}`
        : `${token.selector}|${token.transition}|${token.animation}|${token.transform}`;
      const existing = map.get(key) ?? { ...token, count: 0 };
      existing.count += 1;
      map.set(key, existing);
    }
  }

  return [...map.values()].sort((a, b) => b.count - a.count).slice(0, 140);
}
```

**Step 3: Add renderRichMotionSection helper**

```typescript
function renderRichMotionSection(tokens: Array<(MotionToken | AnimationToken) & { count: number }>): string {
  const animTokens = tokens.filter(isAnimationToken);
  const legacyTokens = tokens.filter((t) => !isAnimationToken(t)) as Array<MotionToken & { count: number }>;

  if (animTokens.length === 0 && legacyTokens.length > 0) {
    // All legacy — fall back to old format
    const rows = legacyTokens.map((t) => [
      truncate(t.transition || 'none'),
      truncate(t.animation || 'none'),
      `\`${t.selector}\``,
      `${t.count}`,
    ]);
    return mdTable(['Transition', 'Animation', 'Selector', 'Occurrences'], rows);
  }

  const sections: string[] = [];

  // Libraries
  const libraries = new Set<string>();
  for (const t of animTokens) {
    if (t.library !== 'css' && t.library !== 'unknown') {
      libraries.add(t.library);
    }
  }
  if (libraries.size > 0) {
    sections.push('### Libraries Detected\n' + [...libraries].map((l) => `- **${l}**`).join('\n'));
  }

  // Group by motionIntent
  const groups = new Map<string, Array<AnimationToken & { count: number }>>();
  for (const t of animTokens) {
    const intent = t.motionIntent;
    const group = groups.get(intent) ?? [];
    group.push(t as AnimationToken & { count: number });
    groups.set(intent, group);
  }

  const intentOrder = ['fade', 'slide', 'scale', 'rotate', 'spring', 'bounce', 'color-shift', 'reveal', 'morph', 'parallax', 'complex'];

  for (const intent of intentOrder) {
    const group = groups.get(intent);
    if (!group || group.length === 0) continue;

    const label = intent.charAt(0).toUpperCase() + intent.slice(1);

    if (intent === 'spring' || intent === 'bounce') {
      const rows = group.map((t) => [
        `\`${t.selector}\``,
        t.timing ? `${t.timing.duration}ms` : '-',
        t.physics?.overshootPercent != null ? `${t.physics.overshootPercent}%` : '-',
        t.physics?.oscillationCount != null ? `${t.physics.oscillationCount}` : '-',
        t.library,
      ]);
      sections.push(`### ${label} Animations (${group.length})\n\n` + mdTable(['Element', 'Duration', 'Overshoot', 'Oscillations', 'Library'], rows));
    } else {
      const rows = group.map((t) => [
        `\`${t.selector}\``,
        t.timing ? `${t.timing.duration}ms` : '-',
        t.timing?.easing ?? '-',
        t.trigger,
        t.library,
      ]);
      sections.push(`### ${label} Animations (${group.length})\n\n` + mdTable(['Element', 'Duration', 'Easing', 'Trigger', 'Library'], rows));
    }
  }

  // Lottie
  const lotties = animTokens.filter((t) => t.lottieMetadata);
  if (lotties.length > 0) {
    const rows = lotties.map((t) => [
      `\`${t.selector}\``,
      t.lottieMetadata ? `${t.lottieMetadata.frameRate}fps` : '-',
      t.lottieMetadata ? `${t.lottieMetadata.duration.toFixed(1)}s` : '-',
      t.lottieMetadata ? `${t.lottieMetadata.totalFrames}` : '-',
    ]);
    sections.push('### Lottie Animations\n\n' + mdTable(['Container', 'Frame Rate', 'Duration', 'Frames'], rows));
  }

  // Scroll-bound
  const scrollBound = animTokens.filter((t) => t.trigger === 'scroll' || t.scrollBinding);
  if (scrollBound.length > 0) {
    const rows = scrollBound.map((t) => [
      `\`${t.selector}\``,
      t.scrollBinding?.hasScrollTrigger ? 'ScrollTrigger' : 'CSS ScrollTimeline',
      t.library,
    ]);
    sections.push('### Scroll-Bound (passive)\n\n' + mdTable(['Element', 'Type', 'Library'], rows));
  }

  // Animation sequences
  const groupedTokens = animTokens.filter((t) => t.group);
  const sequenceMap = new Map<string, Array<AnimationToken & { count: number }>>();
  for (const t of groupedTokens) {
    const gid = t.group!.groupId;
    const seq = sequenceMap.get(gid) ?? [];
    seq.push(t as AnimationToken & { count: number });
    sequenceMap.set(gid, seq);
  }
  if (sequenceMap.size > 0) {
    const seqLines: string[] = [];
    for (const [gid, seq] of sequenceMap) {
      const sorted = seq.sort((a, b) => (a.group?.staggerDelay ?? 0) - (b.group?.staggerDelay ?? 0));
      const parts = sorted.map((t) => {
        const delay = t.group?.staggerDelay ?? 0;
        return t.group?.role === 'lead'
          ? `\`${t.selector}\` (lead)`
          : `\`${t.selector}\` (+${delay}ms)`;
      });
      seqLines.push(`- **${gid}**: ${parts.join(' → ')}`);
    }
    sections.push('### Animation Sequences\n\n' + seqLines.join('\n'));
  }

  // Legacy tokens at the end
  if (legacyTokens.length > 0) {
    const rows = legacyTokens.map((t) => [
      truncate(t.transition || 'none'),
      truncate(t.animation || 'none'),
      `\`${t.selector}\``,
      `${t.count}`,
    ]);
    sections.push('### CSS Transitions (legacy)\n\n' + mdTable(['Transition', 'Animation', 'Selector', 'Occurrences'], rows));
  }

  return sections.join('\n\n');
}
```

**Step 4: Update renderTokens to use the new function**

In `renderTokens` (around line 261), replace the motion rendering:

```typescript
// OLD:
const motionRows = motion.map((token) => [truncate(token.transition || 'none'), truncate(token.animation || 'none'), `\`${token.selector}\``, `${token.count}`]);

// ... and later:
motion:
  `# ${project.name} Motion Brain\n\n` + mdTable(['Transition', 'Animation', 'Selector', 'Occurrences'], motionRows) + '\n',
```

Replace with:

```typescript
motion:
  `# ${project.name} Motion Brain\n\n` + renderRichMotionSection(motion) + '\n',
```

(Remove the `motionRows` variable.)

**Step 5: Update renderInspiration to handle AnimationToken**

In `renderInspiration` (around lines 135-140), replace:

```typescript
  const motionRows = record.analysis.motion.slice(0, 80).map((motion) => [
    `\`${motion.selector}\``,
    truncate(motion.transition || 'none'),
    truncate(motion.animation || 'none'),
    truncate(motion.transform || 'none'),
  ]);
```

With:

```typescript
  const motionContent = renderRichMotionSection(
    record.analysis.motion.slice(0, 80).map((t) => ({ ...t, count: 1 }))
  );
```

And replace the Motion table output (around line 202):

```typescript
// OLD:
+ `## Motion\n\n${mdTable(['Selector', 'Transition', 'Animation', 'Transform'], motionRows)}\n\n`

// NEW:
+ `## Motion\n\n${motionContent}\n\n`
```

**Step 6: Build**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build`

Expected: Compiles.

**Step 7: Commit**

```bash
git add src/render.ts
git commit -m "feat: rich grouped markdown rendering for animation tokens"
```

---

### Task 6: Update supporting files (scan, llm, query, commands)

**Files:**
- Modify: `src/scan.ts`
- Modify: `src/llm.ts`
- Modify: `src/query.ts`
- Modify: `src/commands.ts`

**Step 1: Update scan.ts — add @keyframes regex and animation library detection**

In `src/scan.ts`, add new regex patterns after line 60:

```typescript
const KEYFRAME_RE = /@keyframes\s+([\w-]+)/g;
const GSAP_IMPORT_RE = /(?:from\s+['"]gsap|require\s*\(\s*['"]gsap)/g;
const FRAMER_IMPORT_RE = /(?:from\s+['"]framer-motion|from\s+['"]motion)/g;
const LOTTIE_IMPORT_RE = /(?:from\s+['"]lottie-web|from\s+['"]@lottiefiles)/g;
```

Update `scanCssContent` to track keyframe names (add to the function before the return):

```typescript
  // Keyframe definitions
  const keyframeNames: string[] = [];
  for (const m of css.matchAll(KEYFRAME_RE)) {
    keyframeNames.push(m[1].trim());
  }
  // Include keyframe names in transitions array for scoring
  for (const name of keyframeNames) {
    transitions.push(`@keyframes:${name}`);
  }
```

Update `designAnalysisToScanTokens` (lines 314-327) to handle both token types:

```typescript
export function designAnalysisToScanTokens(analysis: DesignAnalysis): ScanTokens {
  const transitionValues: string[] = [];
  for (const m of analysis.motion) {
    if ('library' in m && 'motionIntent' in m) {
      // AnimationToken
      const at = m as AnimationToken;
      if (at.timing) {
        transitionValues.push(`${at.motionIntent} ${at.timing.duration}ms ${at.timing.easing}`);
      }
    } else {
      // Legacy MotionToken
      const mt = m as MotionToken;
      if (mt.transition && mt.transition !== 'all 0s ease 0s') {
        transitionValues.push(mt.transition);
      }
    }
  }

  return {
    colors: analysis.colors.map(c => c.hex),
    fontFamilies: [...new Set(analysis.typography.map(t => t.fontFamily.toLowerCase()))],
    fontSizes: [...new Set(analysis.typography.map(t => t.fontSize))],
    transitions: transitionValues,
    spacingValues: analysis.components
      .flatMap(c => [c.styles.padding, c.styles.margin].filter(Boolean) as string[]),
    cssVariableCount: Object.keys(analysis.cssVariables).length,
    framework: null,
  };
}
```

Add the `AnimationToken` and `MotionToken` imports at the top of scan.ts.

**Step 2: Update llm.ts — richer motion context in prompt**

In `src/llm.ts`, update the `buildPrompt` function's motion line (line 175):

```typescript
// OLD:
const motionList = input.analysis.motion.slice(0, 12).map((motion) => `${motion.selector}:${motion.transition || motion.animation || motion.transform}`).join(', ');

// NEW:
const motionList = input.analysis.motion.slice(0, 12).map((m) => {
  if ('library' in m && 'motionIntent' in m) {
    const at = m as AnimationToken;
    const dur = at.timing ? `${at.timing.duration}ms` : '';
    return `${at.selector}:${at.motionIntent}(${at.library}${dur ? ' ' + dur : ''})`;
  }
  const mt = m as MotionToken;
  return `${mt.selector}:${mt.transition || mt.animation || mt.transform}`;
}).join(', ');
```

Add `AnimationToken` import.

Also update `enrichImageWithLlmVision` (line 327) — the motion construction from vision should return MotionToken (legacy), which is fine since images can't detect runtime animations.

**Step 3: Update query.ts — search new token fields**

In `src/query.ts`, update the inspiration text builder (line 102):

```typescript
// OLD:
inspiration.analysis.motion.map((motion) => `${motion.transition} ${motion.animation}`).join(' '),

// NEW:
inspiration.analysis.motion.map((m) => {
  if ('library' in m && 'motionIntent' in m) {
    const at = m as { library: string; motionIntent: string; selector: string; trigger: string };
    return `${at.motionIntent} ${at.library} ${at.selector} ${at.trigger}`;
  }
  const mt = m as { transition: string; animation: string };
  return `${mt.transition} ${mt.animation}`;
}).join(' '),
```

**Step 4: Update commands.ts — fingerprint handles both types**

In `src/commands.ts`, update the `computeFingerprint` function (line 34):

```typescript
// OLD:
motion: input.analysis.motion.slice(0, 20).map((motion) => `${motion.transition}|${motion.animation}`),

// NEW:
motion: input.analysis.motion.slice(0, 20).map((m) => {
  if ('library' in m && 'motionIntent' in m) {
    const at = m as { library: string; motionIntent: string; selector: string };
    return `${at.library}|${at.motionIntent}|${at.selector}`;
  }
  const mt = m as { transition: string; animation: string };
  return `${mt.transition}|${mt.animation}`;
}),
```

**Step 5: Build and run all tests**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build && node --test tests/*.test.mjs`

Expected: All existing tests pass. The `designAnalysisToScanTokens` test should still pass since it uses MotionToken format and the code handles both.

**Step 6: Commit**

```bash
git add src/scan.ts src/llm.ts src/query.ts src/commands.ts
git commit -m "feat: update scan, llm, query, commands for AnimationToken support"
```

---

### Task 7: Update existing scan test for backward compatibility

**Files:**
- Modify: `tests/scan.test.mjs`

**Step 1: Verify the existing designAnalysisToScanTokens test still works**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build && node --test tests/scan.test.mjs`

Expected: PASS — the test uses legacy MotionToken format which is still supported.

**Step 2: Add a test for AnimationToken conversion**

Add to `tests/scan.test.mjs`:

```javascript
test('designAnalysisToScanTokens handles AnimationToken format', () => {
  const mockAnalysis = {
    colors: [{ hex: '#FF0000', count: 5, samples: [] }],
    typography: [{ fontFamily: 'Inter', fontSize: '16px', fontWeight: '400', lineHeight: '1.5', count: 10 }],
    components: [],
    motion: [
      {
        selector: '.hero',
        library: 'css',
        motionIntent: 'fade',
        trigger: 'load',
        timing: { duration: 600, delay: 0, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
        keyframes: [],
      },
      {
        selector: '.card',
        library: 'gsap',
        motionIntent: 'slide',
        trigger: 'scroll',
        timing: { duration: 400, delay: 100, easing: 'power2.out', iterations: 1, direction: 'normal', fillMode: 'none' },
      },
    ],
    layout: [],
    cssVariables: {},
  };

  const tokens = designAnalysisToScanTokens(mockAnalysis);
  assert.equal(tokens.transitions.length, 2);
  assert.ok(tokens.transitions[0].includes('fade'));
  assert.ok(tokens.transitions[0].includes('600ms'));
  assert.ok(tokens.transitions[1].includes('slide'));
});
```

**Step 3: Run tests**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build && node --test tests/scan.test.mjs`

Expected: All PASS.

**Step 4: Commit**

```bash
git add tests/scan.test.mjs
git commit -m "test: add AnimationToken backward-compatibility test for scan"
```

---

### Task 8: Final build, full test suite, and verification

**Files:** None new

**Step 1: Full build**

Run: `cd /Users/arnavdas/packages/design-brain-memory && npm run build`

Expected: No errors.

**Step 2: Run full test suite**

Run: `cd /Users/arnavdas/packages/design-brain-memory && node --test tests/*.test.mjs`

Expected: All tests pass (util, query, persona, scan, classify).

**Step 3: Verify exported types**

Run: `cd /Users/arnavdas/packages/design-brain-memory && grep -r "AnimationToken" dist/types.d.ts`

Expected: `AnimationToken` is exported in the declaration file.

**Step 4: Commit**

If any fixes were needed, commit them:

```bash
git add -A
git commit -m "fix: resolve any remaining type/build issues from animation capture"
```
