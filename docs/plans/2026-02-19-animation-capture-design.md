# Animation Capture System for design-brain-memory

**Date:** 2026-02-19
**Status:** Approved
**Scope:** Full runtime observation with passive scroll detection

## Problem

The current motion capture in design-brain-memory stores raw CSS property strings (`transition: all 0.3s ease-in-out`) with no semantic understanding. It cannot detect GSAP, Lottie, Framer Motion, scroll-triggered effects, physics-based motion, animation sequencing, or keyframe data.

## Decision Record

- **Scope**: Full runtime observation (library detection, Web Animations API, rAF sampling, passive scroll detection)
- **Scroll handling**: Passive detection only (detect ScrollTrigger/IntersectionObserver usage, don't simulate scrolling)
- **Output format**: Rich markdown sections grouped by motion intent
- **Additional features**: Physics parameter detection, animation grouping/stagger detection

## Data Model

### Core Types

```typescript
type AnimationLibrary = 'css' | 'gsap' | 'lottie' | 'framer-motion' | 'react-spring' | 'motion-one' | 'unknown';
type MotionIntent = 'fade' | 'slide' | 'scale' | 'rotate' | 'color-shift' | 'spring' | 'bounce' | 'morph' | 'reveal' | 'parallax' | 'complex';
type TriggerEvent = 'load' | 'hover' | 'focus' | 'click' | 'scroll' | 'viewport-enter' | 'media-query' | 'unknown';

interface KeyframeStop {
  offset: number;
  properties: Record<string, string>;
  easing?: string;
}

interface AnimationTiming {
  duration: number;
  delay: number;
  easing: string;
  iterations: number;
  direction: 'normal' | 'reverse' | 'alternate' | 'alternate-reverse';
  fillMode: 'none' | 'forwards' | 'backwards' | 'both';
}

interface ScrollBinding {
  triggerSelector?: string;
  hasScrollTrigger: boolean;
  hasIntersectionObserver: boolean;
  scrollTimelineAxis?: 'block' | 'inline';
}

interface PhysicsParams {
  type: 'spring' | 'bounce' | 'inertia';
  mass?: number;
  stiffness?: number;
  damping?: number;
  oscillationCount?: number;
  overshootPercent?: number;
}

interface AnimationGroup {
  groupId: string;
  role: 'lead' | 'follower';
  staggerDelay?: number;
}

interface AnimationToken {
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
```

### Backward Compatibility

Old `MotionToken` fields map to `rawTransition`, `rawAnimation`, `rawTransform`. The render layer checks for new fields and falls back to old format. Existing database entries remain valid.

## Extraction Architecture

Five-layer observer script injected via Agent Browser `eval`:

### Layer 1: Library Detection
- Check `window.gsap` (+ version), `window.lottie`/`window.bodymovin`, `<lottie-player>` elements
- Detect ScrollTrigger via `typeof ScrollTrigger !== 'undefined'`
- Framer Motion: heuristic via WAAPI animations on elements with `data-framer-*` attributes
- React Spring / Motion One: detected via WAAPI or MutationObserver style patterns

### Layer 2: Web Animations API
- `document.getAnimations()` captures CSS animations, transitions, and WAAPI animations
- Extract `effect.getKeyframes()` for full keyframe data
- Extract `effect.getComputedTiming()` for structured timing

### Layer 3: GSAP Introspection (conditional)
- `gsap.globalTimeline.getChildren(true, true, true)` enumerates all tweens
- Extract: `targets()`, `duration()`, `vars` (properties, easing), `startTime()`
- ScrollTrigger: `ScrollTrigger.getAll()` for scroll-bound animation metadata

### Layer 4: Lottie Extraction (conditional)
- `lottie.getRegisteredAnimations()` or `<lottie-player>` elements
- Extract: `animationData` summary (frameRate, totalFrames, duration, layer count)
- Also detect network requests for `.json` files matching Lottie schema (v, fr, ip, op, layers)

### Layer 5: Passive Scroll Detection
- Detect `ScrollTrigger` instances and their configuration
- Detect `IntersectionObserver` usage via checking if constructor has been called
- Detect CSS `ScrollTimeline` / `ViewTimeline` via `document.getAnimations()` timeline type
- Detect `scroll-snap` CSS properties

## Motion Intent Classification

Heuristic based on animated properties in keyframes:

| Animated Properties | Intent |
|---|---|
| `opacity` only | `fade` |
| `translateX/Y` | `slide` |
| `scale` / `scaleX/Y` | `scale` |
| `rotate` / `rotateX/Y/Z` | `rotate` |
| `backgroundColor`, `color`, `borderColor` | `color-shift` |
| `clip-path`, `height`/`width` animating from 0 | `reveal` |
| Overshoot + oscillation in values | `spring` or `bounce` |
| Multiple property types | `complex` |

## Physics Detection

Analyze keyframe value sequences for overshoot/oscillation:
1. Identify if animated value exceeds final value then returns (overshoot)
2. Count oscillation crossings
3. If oscillations with decreasing amplitude: `spring`
4. If single overshoot + sharp return: `bounce`
5. Store: oscillation count, overshoot percentage
6. For GSAP tweens with known ease strings (e.g., `elastic`, `bounce`, `back`), map directly

## Animation Grouping

Two detection heuristics:
1. **Stagger**: Elements sharing same animation name/keyframes with incremental delays
2. **Temporal clustering**: Animations starting within 50ms window on DOM siblings or shared-parent elements

Group structure: lead element (earliest start) + followers with computed stagger delays.

## Markdown Rendering

Grouped by motion intent with library attribution:

```markdown
## Motion System

### Libraries Detected
- **GSAP 3.12.5** with ScrollTrigger
- **Lottie** (2 animations)

### Fade Animations (4)
| Element | Duration | Easing | Trigger | Library |
|---------|----------|--------|---------|---------|
| `.hero-title` | 600ms | ease-out | load | css |
| `.card` (x3) | 400ms | ease-out | load, stagger 100ms | css |

### Spring Animations (2)
| Element | Duration | Overshoot | Oscillations | Library |
|---------|----------|-----------|--------------|---------|
| `.modal` | 500ms | 12% | 2 | framer-motion |

### Scroll-Bound (passive)
| Element | Type | Library |
|---------|------|---------|
| `.parallax-bg` | ScrollTrigger | gsap |

### Lottie Animations
| Container | Frame Rate | Duration | Frames |
|-----------|-----------|----------|--------|
| `.spinner` | 30fps | 2.0s | 60 |

### Animation Sequences
- **hero-enter**: `.hero-title` (lead) -> `.hero-subtitle` (+200ms) -> `.hero-cta` (+400ms)
```

## Files Changed

| File | Change |
|------|--------|
| `src/types.ts` | Replace `MotionToken` with `AnimationToken`, add supporting types |
| `src/extractFromUrl.ts` | New `ANIMATION_OBSERVER_SCRIPT`, integrate into capture pipeline |
| `src/render.ts` | New `renderMotionSection()` with grouped markdown |
| `src/scan.ts` | Enhanced regex for `@keyframes`, library import detection |
| `src/llm.ts` | Updated enrichment prompt for new token structure |
| `src/query.ts` | Updated search fields for new token format |
| `src/store.ts` | Backward-compatible handling of old MotionToken data |

## Implementation Order

1. Types (`types.ts`) - new interfaces
2. Extraction script (`extractFromUrl.ts`) - the observer layers
3. Classification logic - intent, physics, grouping (can be in extractFromUrl or a new `classify.ts`)
4. Rendering (`render.ts`) - new markdown output
5. Supporting updates (`scan.ts`, `llm.ts`, `query.ts`, `store.ts`)
6. Testing - verify against real sites with known animations
