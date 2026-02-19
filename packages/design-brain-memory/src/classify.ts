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
 * Extract a numeric value from a transform function string.
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
