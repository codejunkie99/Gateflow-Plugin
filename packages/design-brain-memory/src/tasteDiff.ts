import path from 'node:path';
import { scanDesignSystem } from './scan.js';
import { findProject, loadDatabase, loadTasteProfile, saveTasteProfile } from './store.js';
import { nowIso, slugify, unique } from './util.js';
import type {
  ComponentCherryPick,
  InspirationRecord,
  ScanTokens,
  TasteDelta,
  TasteDiffResult,
  TasteProfile,
} from './types.js';

function clampScore(value: number): number {
  return Math.max(0, Math.min(100, Math.round(value)));
}

function hexToRgb(hex: string): { r: number; g: number; b: number } | null {
  const clean = hex.replace('#', '').trim();
  if (!/^[0-9a-fA-F]{3}([0-9a-fA-F]{3})?$/.test(clean)) {
    return null;
  }
  const full = clean.length === 3
    ? `${clean[0]}${clean[0]}${clean[1]}${clean[1]}${clean[2]}${clean[2]}`
    : clean;
  return {
    r: Number.parseInt(full.slice(0, 2), 16),
    g: Number.parseInt(full.slice(2, 4), 16),
    b: Number.parseInt(full.slice(4, 6), 16),
  };
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

function parsePxValues(input: string): number[] {
  return (input.match(/-?\d+(?:\.\d+)?/g) ?? [])
    .map((value) => Number.parseFloat(value))
    .filter((value) => Number.isFinite(value));
}

function parseDurationMs(value: string): number[] {
  const matches = value.match(/(\d+(?:\.\d+)?)\s*(ms|s)\b/gi) ?? [];
  return matches
    .map((match) => {
      const parsed = match.match(/(\d+(?:\.\d+)?)\s*(ms|s)\b/i);
      if (!parsed) {
        return null;
      }
      const numeric = Number.parseFloat(parsed[1]);
      if (!Number.isFinite(numeric)) {
        return null;
      }
      return parsed[2].toLowerCase() === 's' ? numeric * 1000 : numeric;
    })
    .filter((value): value is number => value !== null);
}

function isHexColor(input: string): boolean {
  return /^#(?:[0-9a-fA-F]{3}){1,2}$/.test(input.trim());
}

function colorDistance(hex1: string, hex2: string): number {
  const rgb1 = hexToRgb(hex1);
  const rgb2 = hexToRgb(hex2);
  if (!rgb1 || !rgb2) {
    return 100;
  }

  const hsl1 = rgbToHsl(rgb1);
  const hsl2 = rgbToHsl(rgb2);

  const hueDelta = Math.min(Math.abs(hsl1.h - hsl2.h), 360 - Math.abs(hsl1.h - hsl2.h)) / 180;
  const satDelta = Math.abs(hsl1.s - hsl2.s);
  const lightDelta = Math.abs(hsl1.l - hsl2.l);
  return Math.round((hueDelta * 0.6 + satDelta * 0.2 + lightDelta * 0.2) * 100);
}

function closestTasteColor(hex: string, palette: string[]): { hex: string; distance: number } {
  const closest = palette
    .map((candidate) => ({ hex: candidate, distance: colorDistance(hex, candidate) }))
    .sort((a, b) => a.distance - b.distance)[0];
  return closest ?? { hex, distance: 100 };
}

function computeColorAlignment(tokens: ScanTokens, taste: TasteProfile): {
  alignment: number;
  summary: string;
  deltas: TasteDelta[];
} {
  const palette = taste.color.palette
    .map((entry) => entry.hex.toUpperCase())
    .filter(isHexColor);
  const codeColors = unique(tokens.colors.map((color) => color.toUpperCase()).filter(isHexColor));

  if (codeColors.length === 0 || palette.length === 0) {
    return {
      alignment: 100,
      summary: 'No color mismatch detected',
      deltas: [],
    };
  }

  let aligned = 0;
  let close = 0;
  const deltas: TasteDelta[] = [];

  for (const color of codeColors) {
    const closest = closestTasteColor(color, palette);
    if (closest.distance < 15) {
      aligned += 1;
    } else if (closest.distance < 30) {
      close += 1;
    } else {
      deltas.push({
        dimension: 'color',
        issue: `Color ${color} is outside the taste palette`,
        suggestion: `Closest palette match: ${closest.hex}`,
        severity: 'mismatch',
      });
    }
  }

  const alignment = clampScore(((aligned + close * 0.5) / codeColors.length) * 100);
  return {
    alignment,
    summary: `${aligned}/${codeColors.length} colors aligned with palette`,
    deltas,
  };
}

function normalizeFontFamily(value: string): string {
  return value.trim().replace(/['"]/g, '').toLowerCase();
}

function parseFontSize(value: string): number | null {
  const cleaned = value.trim().toLowerCase();
  const match = cleaned.match(/^(\d+(?:\.\d+)?)(px|rem|em)$/);
  if (!match) {
    return null;
  }
  const numeric = Number.parseFloat(match[1]);
  if (!Number.isFinite(numeric)) {
    return null;
  }
  return match[2] === 'px' ? numeric : numeric * 16;
}

function computeTypographyAlignment(tokens: ScanTokens, taste: TasteProfile): {
  alignment: number;
  summary: string;
  deltas: TasteDelta[];
} {
  const expectedFonts = unique([
    taste.typography.primaryFont,
    taste.typography.secondaryFont ?? '',
  ].filter(Boolean).map(normalizeFontFamily));

  const codeFonts = unique(tokens.fontFamilies.map(normalizeFontFamily).filter(Boolean));
  const matchedFonts = codeFonts.filter((font) => expectedFonts.includes(font));
  const extraFonts = codeFonts.filter((font) => !expectedFonts.includes(font));

  const expectedSizes = taste.typography.sizes
    .map(parseFontSize)
    .filter((size): size is number => size !== null);
  const codeSizes = tokens.fontSizes
    .map(parseFontSize)
    .filter((size): size is number => size !== null);

  const alignedSizes = codeSizes.filter((size) =>
    expectedSizes.some((expected) => Math.abs(size - expected) <= 1),
  ).length;
  const sizeBonus = codeSizes.length > 0 ? (alignedSizes / codeSizes.length) * 15 : 0;

  let score = expectedFonts.length > 0
    ? (matchedFonts.length / Math.max(codeFonts.length, 1)) * 100
    : 100;
  score -= extraFonts.length * 20;
  score += sizeBonus;
  const alignment = clampScore(score);

  const deltas: TasteDelta[] = [];
  for (const font of extraFonts) {
    deltas.push({
      dimension: 'typography',
      issue: `Font "${font}" is outside taste profile`,
      suggestion: `Use ${[taste.typography.primaryFont, taste.typography.secondaryFont].filter(Boolean).join(', ')}`,
      severity: 'warning',
    });
  }

  return {
    alignment,
    summary: `${matchedFonts.length}/${Math.max(codeFonts.length, 1)} font families match taste`,
    deltas,
  };
}

function computeSpacingAlignment(tokens: ScanTokens, taste: TasteProfile): {
  alignment: number;
  summary: string;
  deltas: TasteDelta[];
} {
  const codeSpacing = tokens.spacingValues.flatMap(parsePxValues).filter((value) => value > 0);
  if (codeSpacing.length === 0 || taste.spacing.scale.length === 0) {
    return {
      alignment: 100,
      summary: 'No spacing mismatch detected',
      deltas: [],
    };
  }

  const alignedCount = codeSpacing.filter((value) =>
    taste.spacing.scale.some((scaleValue) => Math.abs(value - scaleValue) <= 2),
  ).length;
  const ratio = alignedCount / codeSpacing.length;
  const alignment = clampScore(ratio * 100);

  const deltas: TasteDelta[] = ratio < 0.8
    ? [{
      dimension: 'spacing',
      issue: `${Math.round((1 - ratio) * 100)}% of spacing values are off-scale`,
      suggestion: `Align spacing to ${taste.spacing.scale.join(', ')}px`,
      severity: 'warning',
    }]
    : [];

  return {
    alignment,
    summary: `${Math.round(ratio * 100)}% of spacing values align to taste grid`,
    deltas,
  };
}

function classifyMotionIntensity(motionCount: number): TasteProfile['motion']['intensity'] {
  if (motionCount === 0) {
    return 'none';
  }
  if (motionCount <= 12) {
    return 'subtle';
  }
  if (motionCount <= 40) {
    return 'moderate';
  }
  return 'expressive';
}

function computeMotionAlignment(tokens: ScanTokens, taste: TasteProfile): {
  alignment: number;
  summary: string;
  deltas: TasteDelta[];
} {
  const codeDurations = unique(tokens.transitions.flatMap(parseDurationMs).map((value) => Math.round(value)));
  const tasteDurations = unique(taste.motion.durations.flatMap(parseDurationMs).map((value) => Math.round(value)));

  let durationScore = 0;
  if (tasteDurations.length === 0 || codeDurations.length === 0) {
    durationScore = 50;
  } else {
    const matches = codeDurations.filter((duration) =>
      tasteDurations.some((expected) => Math.abs(duration - expected) <= 40),
    ).length;
    durationScore = (matches / codeDurations.length) * 50;
  }

  const transitionsBlob = tokens.transitions.join(' ').toLowerCase();
  const easingScore = transitionsBlob.includes(taste.motion.easing.toLowerCase()) ? 30 : 0;

  const expectedIntensity = taste.motion.intensity;
  const actualIntensity = classifyMotionIntensity(tokens.transitions.length);
  const intensityScore = expectedIntensity === actualIntensity
    ? 20
    : (expectedIntensity === 'none' && actualIntensity === 'subtle') || (expectedIntensity === 'subtle' && actualIntensity === 'moderate') || (expectedIntensity === 'moderate' && actualIntensity === 'subtle')
      ? 10
      : 0;

  const alignment = clampScore(durationScore + easingScore + intensityScore);
  const deltas: TasteDelta[] = [];
  if (easingScore === 0) {
    deltas.push({
      dimension: 'motion',
      issue: `Expected easing "${taste.motion.easing}" not found`,
      suggestion: `Adopt easing ${taste.motion.easing}`,
      severity: 'warning',
    });
  }

  return {
    alignment,
    summary: `Motion intensity is ${actualIntensity}; taste expects ${expectedIntensity}`,
    deltas,
  };
}

export function computeTasteDiff(codebaseTokens: ScanTokens, taste: TasteProfile): TasteDiffResult {
  const color = computeColorAlignment(codebaseTokens, taste);
  const typography = computeTypographyAlignment(codebaseTokens, taste);
  const spacing = computeSpacingAlignment(codebaseTokens, taste);
  const motion = computeMotionAlignment(codebaseTokens, taste);

  const alignment = clampScore(
    (color.alignment + typography.alignment + spacing.alignment + motion.alignment) / 4,
  );

  return {
    alignment,
    dimensions: {
      color: { alignment: color.alignment, summary: color.summary },
      typography: { alignment: typography.alignment, summary: typography.summary },
      spacing: { alignment: spacing.alignment, summary: spacing.summary },
      motion: { alignment: motion.alignment, summary: motion.summary },
    },
    deltas: [...color.deltas, ...typography.deltas, ...spacing.deltas, ...motion.deltas],
  };
}

export async function scoreTaste(options: {
  rootDir: string;
  projectId: string;
  scanPath: string;
}): Promise<{ scanResult: Awaited<ReturnType<typeof scanDesignSystem>>; diff: TasteDiffResult }> {
  const profile = await loadTasteProfile(options.rootDir, options.projectId);
  if (!profile) {
    throw new Error(`Taste profile not found for project: ${options.projectId}`);
  }

  const resolvedPath = path.resolve(options.scanPath);
  const scanResult = await scanDesignSystem(resolvedPath);
  const diff = computeTasteDiff(scanResult.tokens, profile);
  return { scanResult, diff };
}

function normalizeHost(input: string): string | null {
  try {
    return new URL(input).hostname.toLowerCase();
  } catch {
    return null;
  }
}

function resolveSourceInspiration(projectInspirations: InspirationRecord[], sourceUrlOrId: string): InspirationRecord | null {
  const byId = projectInspirations.find((inspiration) => inspiration.id === sourceUrlOrId);
  if (byId) {
    return byId;
  }

  const normalizedInputUrl = sourceUrlOrId.startsWith('http://') || sourceUrlOrId.startsWith('https://')
    ? sourceUrlOrId
    : `https://${sourceUrlOrId}`;

  const byUrl = projectInspirations.find((inspiration) => inspiration.url === sourceUrlOrId || inspiration.url === normalizedInputUrl);
  if (byUrl) {
    return byUrl;
  }

  const inputHost = normalizeHost(normalizedInputUrl);
  if (!inputHost) {
    return null;
  }
  return projectInspirations.find((inspiration) => inspiration.url && normalizeHost(inspiration.url) === inputHost) ?? null;
}

export async function cherryPickComponent(options: {
  rootDir: string;
  projectId: string;
  componentKind: string;
  sourceUrlOrId: string;
  index?: number;
  note?: string;
}): Promise<ComponentCherryPick> {
  const db = await loadDatabase(options.rootDir);
  const project = findProject(db, slugify(options.projectId));
  if (!project) {
    throw new Error(`Project not found: ${options.projectId}`);
  }

  const source = resolveSourceInspiration(project.inspirations, options.sourceUrlOrId);
  if (!source) {
    throw new Error(`Could not resolve inspiration from "${options.sourceUrlOrId}"`);
  }

  const candidates = source.analysis.components.filter((component) =>
    component.kind.toLowerCase() === options.componentKind.toLowerCase(),
  );
  if (candidates.length === 0) {
    throw new Error(`No components of kind "${options.componentKind}" found in ${source.id}`);
  }

  const selectedIndex = Math.max(0, Math.min(options.index ?? 0, candidates.length - 1));
  const selected = candidates[selectedIndex];

  const pick: ComponentCherryPick = {
    componentKind: options.componentKind,
    sourceInspirationId: source.id,
    sourceUrl: source.url ?? source.id,
    tokens: [selected],
    styles: { ...selected.styles },
    note: options.note?.trim() || undefined,
  };

  const profile = await loadTasteProfile(options.rootDir, project.id);
  if (!profile) {
    throw new Error(`Taste profile not found for project: ${project.id}`);
  }

  profile.components.cherryPicks.push(pick);
  profile.updatedAt = nowIso();
  await saveTasteProfile(options.rootDir, profile);
  return pick;
}
