import { loadTasteProfile, saveTasteProfile } from './store.js';
import { makeId, nowIso } from './util.js';
import type {
  AnimationToken,
  InspirationRecord,
  MotionToken,
  TasteConflict,
  TasteDecision,
  TasteProfile,
} from './types.js';

interface ConflictOptionWithValue {
  label: string;
  value: number;
}

function asAnimationToken(token: MotionToken | AnimationToken): token is AnimationToken {
  return 'library' in token && 'motionIntent' in token;
}

function parseNumericValues(input: string | undefined): number[] {
  if (!input) {
    return [];
  }

  return (input.match(/-?\d+(?:\.\d+)?/g) ?? [])
    .map((value) => Number.parseFloat(value))
    .filter((value) => Number.isFinite(value));
}

function hexToRgb(hex: string): { r: number; g: number; b: number } | null {
  const clean = hex.replace('#', '').trim();
  if (!/^[0-9a-fA-F]{3}([0-9a-fA-F]{3})?$/.test(clean)) {
    return null;
  }

  const full = clean.length === 3
    ? `${clean[0]}${clean[0]}${clean[1]}${clean[1]}${clean[2]}${clean[2]}`
    : clean;

  const r = Number.parseInt(full.slice(0, 2), 16);
  const g = Number.parseInt(full.slice(2, 4), 16);
  const b = Number.parseInt(full.slice(4, 6), 16);
  return { r, g, b };
}

function rgbToHsl(rgb: { r: number; g: number; b: number }): { h: number; s: number; l: number } {
  const r = rgb.r / 255;
  const g = rgb.g / 255;
  const b = rgb.b / 255;
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const l = (max + min) / 2;

  if (max === min) {
    return { h: 0, s: 0, l };
  }

  const d = max - min;
  const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
  let h = 0;
  if (max === r) {
    h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
  } else if (max === g) {
    h = ((b - r) / d + 2) / 6;
  } else {
    h = ((r - g) / d + 4) / 6;
  }

  return { h: h * 360, s, l };
}

function hslDistance(a: string, b: string): number {
  const rgbA = hexToRgb(a);
  const rgbB = hexToRgb(b);
  if (!rgbA || !rgbB) {
    return 0;
  }

  const hslA = rgbToHsl(rgbA);
  const hslB = rgbToHsl(rgbB);
  const hueDelta = Math.min(Math.abs(hslA.h - hslB.h), 360 - Math.abs(hslA.h - hslB.h)) / 180;
  const satDelta = Math.abs(hslA.s - hslB.s);
  const lightDelta = Math.abs(hslA.l - hslB.l);
  return Math.round((hueDelta * 0.6 + satDelta * 0.2 + lightDelta * 0.2) * 100);
}

function sourceLabel(inspiration: InspirationRecord): string {
  if (inspiration.url) {
    try {
      return new URL(inspiration.url).hostname;
    } catch {
      return inspiration.url;
    }
  }
  return inspiration.name;
}

function primaryFont(inspiration: InspirationRecord): string | null {
  const byCount = [...inspiration.analysis.typography]
    .sort((a, b) => b.count - a.count);
  const token = byCount[0];
  return token?.fontFamily?.trim() || null;
}

function detectBaseUnit(inspiration: InspirationRecord): number | null {
  const values = inspiration.analysis.components
    .flatMap((component) => [
      component.styles.padding,
      component.styles.margin,
      component.styles.gap,
      component.styles.rowGap,
      component.styles.columnGap,
    ])
    .flatMap(parseNumericValues)
    .filter((value) => value > 0);

  if (values.length === 0) {
    return null;
  }

  const aligned4 = values.filter((value) => value % 4 === 0).length;
  const aligned8 = values.filter((value) => value % 8 === 0).length;
  return aligned8 >= aligned4 ? 8 : 4;
}

function detectRadius(inspiration: InspirationRecord): number | null {
  const radii = inspiration.analysis.components
    .flatMap((component) => parseNumericValues(component.styles.borderRadius))
    .filter((value) => value >= 0);

  if (radii.length === 0) {
    return null;
  }

  const rounded = radii.map((value) => Math.round(value));
  const counts = new Map<number, number>();
  for (const value of rounded) {
    counts.set(value, (counts.get(value) ?? 0) + 1);
  }

  return [...counts.entries()].sort((a, b) => b[1] - a[1])[0]?.[0] ?? null;
}

function extractDurationMs(value: string): number[] {
  const matches = value.match(/(\d+(?:\.\d+)?)\s*(ms|s)\b/gi) ?? [];
  return matches
    .map((match) => {
      const [, raw, unit] = match.match(/(\d+(?:\.\d+)?)\s*(ms|s)\b/i) ?? [];
      const num = Number.parseFloat(raw ?? '');
      if (!Number.isFinite(num)) {
        return null;
      }
      return unit?.toLowerCase() === 's' ? num * 1000 : num;
    })
    .filter((value): value is number => value !== null);
}

function dominantDuration(inspiration: InspirationRecord): number | null {
  const durations = inspiration.analysis.motion.flatMap((token) => {
    if (asAnimationToken(token)) {
      return token.timing ? [token.timing.duration] : [];
    }
    return [
      ...extractDurationMs(token.transition),
      ...extractDurationMs(token.animation),
    ];
  });

  if (durations.length === 0) {
    return null;
  }

  const rounded = durations.map((value) => Math.round(value / 10) * 10);
  const counts = new Map<number, number>();
  for (const value of rounded) {
    counts.set(value, (counts.get(value) ?? 0) + 1);
  }

  return [...counts.entries()].sort((a, b) => b[1] - a[1])[0]?.[0] ?? null;
}

function hasSpread(values: number[], threshold: number): boolean {
  if (values.length < 2) {
    return false;
  }
  const min = Math.min(...values);
  const max = Math.max(...values);
  return max - min > threshold;
}

function toConflictOptionsBySource(entries: Array<{ source: string; value: string }>): string[] {
  return entries.map((entry) => `${entry.value} (from ${entry.source})`);
}

export function detectConflicts(inspirations: InspirationRecord[]): TasteConflict[] {
  if (inspirations.length < 2) {
    return [];
  }

  const conflicts: TasteConflict[] = [];

  const topColors = inspirations
    .map((inspiration) => ({
      source: sourceLabel(inspiration),
      value: inspiration.analysis.colors[0]?.hex?.toUpperCase(),
    }))
    .filter((entry): entry is { source: string; value: string } => Boolean(entry.value));

  let hasColorConflict = false;
  for (let i = 0; i < topColors.length && !hasColorConflict; i += 1) {
    for (let j = i + 1; j < topColors.length; j += 1) {
      if (hslDistance(topColors[i].value, topColors[j].value) > 40) {
        hasColorConflict = true;
        break;
      }
    }
  }

  if (hasColorConflict) {
    conflicts.push({
      dimension: 'color',
      description: 'Your inspirations show different dominant colors',
      options: toConflictOptionsBySource(topColors.slice(0, 5)),
      resolved: false,
    });
  }

  const fontChoices = inspirations
    .map((inspiration) => ({
      source: sourceLabel(inspiration),
      value: primaryFont(inspiration),
    }))
    .filter((entry): entry is { source: string; value: string } => Boolean(entry.value));

  const uniqueFonts = new Set(fontChoices.map((entry) => entry.value.toLowerCase()));
  if (uniqueFonts.size > 1) {
    conflicts.push({
      dimension: 'typography',
      description: 'Different inspirations use different primary fonts',
      options: toConflictOptionsBySource(fontChoices.slice(0, 5)),
      resolved: false,
    });
  }

  const spacingChoices: ConflictOptionWithValue[] = inspirations
    .map((inspiration) => {
      const unit = detectBaseUnit(inspiration);
      return unit === null ? null : {
        label: `${unit}px (from ${sourceLabel(inspiration)})`,
        value: unit,
      };
    })
    .filter((entry): entry is ConflictOptionWithValue => entry !== null);

  const spacingValues = spacingChoices
    .map((entry) => entry.value)
    .filter((value): value is number => typeof value === 'number');
  if (new Set(spacingValues).size > 1) {
    conflicts.push({
      dimension: 'spacing',
      description: 'Your inspirations suggest different spacing base units',
      options: spacingChoices.map((entry) => entry.label),
      resolved: false,
    });
  }

  const shapeChoices: ConflictOptionWithValue[] = inspirations
    .map((inspiration) => {
      const radius = detectRadius(inspiration);
      return radius === null ? null : {
        label: `${radius}px (from ${sourceLabel(inspiration)})`,
        value: radius,
      };
    })
    .filter((entry): entry is ConflictOptionWithValue => entry !== null);

  const radiusValues = shapeChoices
    .map((entry) => entry.value)
    .filter((value): value is number => typeof value === 'number');
  if (hasSpread(radiusValues, 2)) {
    conflicts.push({
      dimension: 'component',
      description: 'Your inspirations show different corner radiuses',
      options: shapeChoices.map((entry) => entry.label),
      resolved: false,
    });
  }

  const motionChoices: ConflictOptionWithValue[] = inspirations
    .map((inspiration) => {
      const duration = dominantDuration(inspiration);
      return duration === null ? null : {
        label: `${Math.round(duration)}ms (from ${sourceLabel(inspiration)})`,
        value: duration,
      };
    })
    .filter((entry): entry is ConflictOptionWithValue => entry !== null);

  const durationValues = motionChoices
    .map((entry) => entry.value)
    .filter((value): value is number => typeof value === 'number');
  if (hasSpread(durationValues, 100)) {
    conflicts.push({
      dimension: 'motion',
      description: 'Your inspirations suggest different motion tempos',
      options: motionChoices.map((entry) => entry.label),
      resolved: false,
    });
  }

  return conflicts;
}

export function nextClarifyingQuestion(profile: TasteProfile): {
  conflict: TasteConflict;
  question: string;
  options: string[];
} | null {
  const conflict = profile.conflicts.find((entry) => !entry.resolved);
  if (!conflict) {
    return null;
  }

  const numberedOptions = conflict.options
    .map((option, index) => `  ${index + 1}. ${option}`)
    .join('\n');

  return {
    conflict,
    options: conflict.options,
    question: `${conflict.description}:\n${numberedOptions}\nWhich do you prefer? [1/${conflict.options.length}/custom]:`,
  };
}

type DecisionDimension = TasteDecision['dimension'];

function normalizeDecisionDimension(dimension: string): DecisionDimension {
  if (dimension === 'color' || dimension === 'typography' || dimension === 'spacing' || dimension === 'motion' || dimension === 'component' || dimension === 'layout') {
    return dimension;
  }
  return 'general';
}

function applyAnswerToProfile(profile: TasteProfile, conflict: TasteConflict, answer: string): void {
  const trimmed = answer.trim();
  if (!trimmed) {
    return;
  }

  if (conflict.dimension === 'color') {
    const hex = trimmed.match(/#[0-9a-fA-F]{3}(?:[0-9a-fA-F]{3})?/)?.[0];
    if (hex && profile.color.palette.length > 0) {
      profile.color.palette[0] = { ...profile.color.palette[0], hex: hex.toUpperCase(), source: 'decision' };
    }
  }

  if (conflict.dimension === 'typography') {
    const font = trimmed
      .replace(/\(from.*?\)/i, '')
      .replace(/^\d+\.\s*/, '')
      .trim();
    if (font) {
      profile.typography.primaryFont = font;
    }
  }

  if (conflict.dimension === 'spacing') {
    const unit = trimmed.match(/\b(4|8)\s*px\b/i)?.[1];
    if (unit) {
      profile.spacing.baseUnit = Number.parseInt(unit, 10);
    }
  }

  if (conflict.dimension === 'motion') {
    const duration = trimmed.match(/(\d+(?:\.\d+)?)\s*(ms|s)\b/i);
    if (duration) {
      const value = Number.parseFloat(duration[1]);
      const unit = duration[2].toLowerCase();
      const durationMs = unit === 's' ? `${Math.round(value * 1000)}ms` : `${Math.round(value)}ms`;
      profile.motion.durations = [durationMs, ...profile.motion.durations.filter((d) => d !== durationMs)].slice(0, 6);
    }
  }

  if (conflict.dimension === 'component') {
    const radius = trimmed.match(/(\d+(?:\.\d+)?)\s*px\b/i);
    if (radius) {
      profile.components.borderRadius = `${Math.round(Number.parseFloat(radius[1]))}px`;
    }
  }
}

export async function applyDecision(options: {
  rootDir: string;
  projectId: string;
  conflictIndex: number;
  answer: string;
}): Promise<TasteDecision> {
  const profile = await loadTasteProfile(options.rootDir, options.projectId);
  if (!profile) {
    throw new Error(`Taste profile not found for project: ${options.projectId}`);
  }

  const conflict = profile.conflicts[options.conflictIndex];
  if (!conflict) {
    throw new Error(`Conflict index out of range: ${options.conflictIndex}`);
  }

  if (conflict.resolved) {
    throw new Error(`Conflict ${options.conflictIndex} is already resolved`);
  }

  const decision: TasteDecision = {
    id: makeId('decision', `${profile.id}-${conflict.dimension}-${options.conflictIndex}`),
    question: conflict.description,
    answer: options.answer.trim(),
    dimension: normalizeDecisionDimension(conflict.dimension),
    decidedAt: nowIso(),
  };

  profile.decisions.push(decision);
  conflict.resolved = true;
  conflict.resolvedByDecisionId = decision.id;
  applyAnswerToProfile(profile, conflict, decision.answer);
  profile.updatedAt = nowIso();
  await saveTasteProfile(options.rootDir, profile);

  return decision;
}
