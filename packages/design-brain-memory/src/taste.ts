import os from 'node:os';
import path from 'node:path';
import { ingestInspiration } from './commands.js';
import { captureDesignFromUrl } from './extractFromUrl.js';
import { runDesignLlm } from './llm.js';
import { assignPersona } from './persona.js';
import { aggregateColors, aggregateComponents, aggregateMotion, aggregateTypography } from './render.js';
import { computeScore, designAnalysisToScanTokens, looksLikeUrl, normalizeToUrl } from './scan.js';
import { ensureProject, loadDatabase, saveDatabase, loadTasteProfile, saveTasteProfile } from './store.js';
import { theatricalScan } from './theatrical.js';
import { detectConflicts } from './tasteRefine.js';
import { nowIso, unique } from './util.js';
import type {
  AnimationToken,
  ColorToken,
  ComponentToken,
  DesignAnalysis,
  InspirationRecord,
  LlmConfig,
  MotionToken,
  ScanTokens,
  TasteColorPreference,
  TasteComponentPreference,
  TasteConflict,
  TasteMotionPreference,
  TasteProfile,
  TasteSpacingPreference,
  TasteTypographyPreference,
  TypographyToken,
} from './types.js';

function asAnimationToken(token: MotionToken | AnimationToken): token is AnimationToken {
  return 'library' in token && 'motionIntent' in token;
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

function parseNumericValues(value: string | undefined): number[] {
  if (!value) {
    return [];
  }
  return (value.match(/-?\d+(?:\.\d+)?/g) ?? [])
    .map((entry) => Number.parseFloat(entry))
    .filter((entry) => Number.isFinite(entry));
}

function parseFontSizeToPx(value: string): number | null {
  const text = value.trim().toLowerCase();
  const match = text.match(/^(\d+(?:\.\d+)?)(px|rem|em)$/);
  if (!match) {
    return null;
  }

  const numeric = Number.parseFloat(match[1]);
  if (!Number.isFinite(numeric)) {
    return null;
  }

  if (match[2] === 'px') {
    return numeric;
  }

  return numeric * 16;
}

function parseWeightValue(weight: string): number | null {
  const normalized = weight.trim().toLowerCase();
  if (/^\d+$/.test(normalized)) {
    return Number.parseInt(normalized, 10);
  }

  const map: Record<string, number> = {
    normal: 400,
    medium: 500,
    semibold: 600,
    bold: 700,
  };
  return map[normalized] ?? null;
}

function formatDuration(value: number): string {
  return `${Math.round(value)}ms`;
}

function resolveColorRole(index: number): string {
  const roles = ['primary', 'background', 'accent', 'text', 'surface'];
  return roles[index] ?? `color-${index + 1}`;
}

function sourceForColor(hex: string, inspirations: InspirationRecord[]): string {
  const normalized = hex.toUpperCase();
  let bestSource = 'aggregate';
  let bestCount = -1;

  for (const inspiration of inspirations) {
    const match = inspiration.analysis.colors.find((color) => color.hex.toUpperCase() === normalized);
    if (match && match.count > bestCount) {
      bestCount = match.count;
      bestSource = inspiration.url
        ? (() => {
          try {
            return new URL(inspiration.url as string).hostname;
          } catch {
            return inspiration.url as string;
          }
        })()
        : inspiration.id;
    }
  }

  return bestSource;
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

function hueDelta(a: number, b: number): number {
  const direct = Math.abs(a - b);
  return Math.min(direct, 360 - direct);
}

function classifyHarmony(hues: number[]): string {
  if (hues.length <= 1) {
    return 'monochromatic';
  }

  const deltas: number[] = [];
  for (let i = 0; i < hues.length; i += 1) {
    for (let j = i + 1; j < hues.length; j += 1) {
      deltas.push(hueDelta(hues[i], hues[j]));
    }
  }

  if (deltas.some((value) => value >= 150 && value <= 210)) {
    return 'complementary';
  }

  const averageDelta = deltas.reduce((sum, value) => sum + value, 0) / deltas.length;
  if (averageDelta <= 45) {
    return 'analogous';
  }

  return 'triadic';
}

function deriveColorPreference(colors: ColorToken[], inspirations: InspirationRecord[]): TasteColorPreference {
  const palette = colors
    .slice(0, 5)
    .map((color, index) => ({
      hex: color.hex.toUpperCase(),
      role: resolveColorRole(index),
      source: sourceForColor(color.hex, inspirations),
    }));

  if (palette.length === 0) {
    palette.push(
      { hex: '#111111', role: 'primary', source: 'default' },
      { hex: '#FFFFFF', role: 'surface', source: 'default' },
    );
  }

  const hslValues = palette
    .map((entry) => hexToRgb(entry.hex))
    .filter((entry): entry is { r: number; g: number; b: number } => entry !== null)
    .map(rgbToHsl);

  const hues = hslValues.map((value) => value.h);
  const sats = hslValues.map((value) => value.s);
  const lights = hslValues.map((value) => value.l);

  const hueRange = {
    min: Math.round(Math.min(...(hues.length > 0 ? hues : [0]))),
    max: Math.round(Math.max(...(hues.length > 0 ? hues : [0]))),
  };
  const avgSat = sats.length > 0 ? sats.reduce((sum, value) => sum + value, 0) / sats.length : 0;
  const avgLight = lights.length > 0 ? lights.reduce((sum, value) => sum + value, 0) / lights.length : 0;

  return {
    palette,
    harmony: classifyHarmony(hues),
    hueRange,
    saturationBias: avgSat >= 0.62 ? 'vibrant' : avgSat <= 0.35 ? 'muted' : 'neutral',
    lightnessBias: avgLight >= 0.7 ? 'light' : avgLight <= 0.33 ? 'dark' : 'balanced',
  };
}

function deriveTypographyPreference(typography: TypographyToken[]): TasteTypographyPreference {
  const familyCounts = new Map<string, number>();
  for (const token of typography) {
    familyCounts.set(token.fontFamily, (familyCounts.get(token.fontFamily) ?? 0) + token.count);
  }
  const families = [...familyCounts.entries()]
    .sort((a, b) => b[1] - a[1])
    .map((entry) => entry[0]);

  const primaryFont = families[0] ?? 'Inter';
  const secondaryFont = families[1] ?? null;

  const sizeSet = unique(
    typography
      .map((token) => token.fontSize.trim())
      .filter((size) => size.length > 0),
  );
  const sizes = sizeSet.sort((a, b) => {
    const pa = parseFontSizeToPx(a);
    const pb = parseFontSizeToPx(b);
    if (pa === null && pb === null) {
      return a.localeCompare(b);
    }
    if (pa === null) {
      return 1;
    }
    if (pb === null) {
      return -1;
    }
    return pa - pb;
  });

  const pxSizes = sizes
    .map(parseFontSizeToPx)
    .filter((value): value is number => value !== null)
    .sort((a, b) => a - b);
  const ratios: number[] = [];
  for (let i = 1; i < pxSizes.length; i += 1) {
    if (pxSizes[i - 1] > 0) {
      ratios.push(pxSizes[i] / pxSizes[i - 1]);
    }
  }
  const avgRatio = ratios.length > 0
    ? ratios.reduce((sum, value) => sum + value, 0) / ratios.length
    : 0;
  const ratioVariance = ratios.length > 0
    ? ratios.reduce((sum, value) => sum + Math.abs(value - avgRatio), 0) / ratios.length
    : 1;

  const weightValues = typography
    .map((token) => token.fontWeight.trim())
    .filter((weight) => weight.length > 0);
  const numericWeights = weightValues
    .map(parseWeightValue)
    .filter((value): value is number => value !== null)
    .sort((a, b) => a - b);
  const minWeight = numericWeights[0]?.toString() ?? weightValues[0] ?? '400';
  const maxWeight = numericWeights[numericWeights.length - 1]?.toString() ?? weightValues.at(-1) ?? '700';

  return {
    primaryFont,
    secondaryFont,
    scaleType: sizes.length <= 2 ? 'tailwind-default' : ratioVariance <= 0.2 ? 'modular' : 'custom',
    sizes,
    weightRange: {
      min: minWeight,
      max: maxWeight,
    },
  };
}

function deriveSpacingPreference(components: Array<ComponentToken & { count: number }>): TasteSpacingPreference {
  const values = components
    .flatMap((component) => [
      component.styles.padding,
      component.styles.margin,
      component.styles.gap,
      component.styles.rowGap,
      component.styles.columnGap,
    ])
    .flatMap(parseNumericValues)
    .filter((value) => value > 0);

  const baseAligned4 = values.filter((value) => value % 4 === 0).length;
  const baseAligned8 = values.filter((value) => value % 8 === 0).length;
  const baseUnit = baseAligned8 >= baseAligned4 ? 8 : 4;
  const gridAlignmentRatio = values.length > 0
    ? values.filter((value) => value % baseUnit === 0).length / values.length
    : 1;

  const scale = unique(values.map((value) => Math.round(value)))
    .sort((a, b) => a - b)
    .slice(0, 12);
  const fallbackScale = baseUnit === 8
    ? [4, 8, 12, 16, 24, 32, 48, 64]
    : [4, 8, 12, 16, 20, 24, 32, 40];

  return {
    baseUnit,
    scale: scale.length > 0 ? scale : fallbackScale,
    gridAlignmentRatio: Number(gridAlignmentRatio.toFixed(2)),
  };
}

function deriveMotionPreference(motion: Array<(MotionToken | AnimationToken) & { count: number }>): TasteMotionPreference {
  const easings = new Map<string, number>();
  const durations: number[] = [];

  for (const token of motion) {
    if (asAnimationToken(token)) {
      if (token.timing) {
        durations.push(token.timing.duration);
        const easing = token.timing.easing.trim();
        if (easing) {
          easings.set(easing, (easings.get(easing) ?? 0) + token.count);
        }
      }
      continue;
    }

    for (const duration of parseDurationMs(token.transition)) {
      durations.push(duration);
    }
    for (const duration of parseDurationMs(token.animation)) {
      durations.push(duration);
    }

    const easingCandidates = token.transition.match(/(?:ease(?:-in|-out|-in-out)?|linear|cubic-bezier\([^)]+\))/g) ?? [];
    for (const easing of easingCandidates) {
      easings.set(easing, (easings.get(easing) ?? 0) + token.count);
    }
  }

  const dominantEasing = [...easings.entries()].sort((a, b) => b[1] - a[1])[0]?.[0] ?? 'ease';
  const uniqueDurations = unique(durations.map((value) => Math.round(value))).sort((a, b) => a - b);
  const durationLabels = uniqueDurations.slice(0, 6).map(formatDuration);

  const count = motion.length;
  const intensity = count === 0
    ? 'none'
    : count <= 12
      ? 'subtle'
      : count <= 40
        ? 'moderate'
        : 'expressive';

  return {
    easing: dominantEasing,
    durations: durationLabels.length > 0 ? durationLabels : ['200ms'],
    intensity,
  };
}

function deriveComponentPreference(components: Array<ComponentToken & { count: number }>): TasteComponentPreference {
  const radiusValues = components
    .flatMap((component) => parseNumericValues(component.styles.borderRadius))
    .filter((value) => value >= 0)
    .sort((a, b) => a - b);

  const medianRadius = radiusValues.length > 0
    ? radiusValues[Math.floor(radiusValues.length / 2)]
    : 8;

  const shadows = components
    .map((component) => component.styles.boxShadow?.trim())
    .filter((shadow): shadow is string => Boolean(shadow && shadow !== 'none'));
  const noneCount = components.length - shadows.length;
  const shadowStyle = shadows.length === 0
    ? 'none'
    : shadows.length <= noneCount
      ? 'subtle'
      : shadows.some((shadow) => /(?:\b2\dpx\b|\b3\dpx\b|\b4\dpx\b|rgba?\([^)]*,\s*0\.[45-9])/i.test(shadow))
        ? 'dramatic'
        : 'elevated';

  return {
    cherryPicks: [],
    borderRadius: `${Math.round(medianRadius)}px`,
    shadowStyle,
  };
}

function buildAggregateTokens(inspirations: InspirationRecord[]): ScanTokens {
  const colors = aggregateColors(inspirations);
  const typography = aggregateTypography(inspirations);
  const components = aggregateComponents(inspirations);
  const motion = aggregateMotion(inspirations);

  const transitionValues = motion.flatMap((token) => {
    if (asAnimationToken(token)) {
      if (!token.timing) {
        return [];
      }
      return [`${token.motionIntent} ${token.timing.duration}ms ${token.timing.easing}`];
    }
    const values: string[] = [];
    if (token.transition && token.transition !== 'all 0s ease 0s') {
      values.push(token.transition);
    }
    if (token.animation && token.animation !== 'none') {
      values.push(token.animation);
    }
    return values;
  });

  const spacingValues = components.flatMap((component) => [
    component.styles.padding,
    component.styles.margin,
    component.styles.gap,
    component.styles.rowGap,
    component.styles.columnGap,
  ].filter(Boolean) as string[]);

  const cssVariableCount = inspirations.reduce((count, inspiration) => (
    count + Object.keys(inspiration.analysis.cssVariables).length
  ), 0);

  return {
    colors: colors.map((color) => color.hex),
    fontFamilies: unique(typography.map((token) => token.fontFamily.toLowerCase())),
    fontSizes: unique(typography.map((token) => token.fontSize)),
    transitions: transitionValues,
    spacingValues,
    cssVariableCount,
    framework: null,
  };
}

function extractFirstJsonObject(raw: string): string {
  const trimmed = raw.trim();
  if (trimmed.startsWith('{') && trimmed.endsWith('}')) {
    return trimmed;
  }

  const start = raw.indexOf('{');
  const end = raw.lastIndexOf('}');
  if (start >= 0 && end > start) {
    return raw.slice(start, end + 1);
  }

  throw new Error('No JSON object found in LLM response');
}

async function maybeGenerateNarrative(input: {
  llm?: LlmConfig;
  profile: TasteProfile;
}): Promise<Pick<TasteProfile, 'narrative' | 'principles'>> {
  if (!input.llm) {
    return {};
  }

  const prompt = [
    'Return strict JSON with keys: narrative (string), principles (string[]).',
    'narrative should be 2-3 sentences and concise.',
    'principles should contain 3-6 short imperative statements.',
    '',
    `Persona: ${input.profile.persona.name} — "${input.profile.persona.tagline}"`,
    `Palette: ${input.profile.color.palette.map((entry) => `${entry.hex} (${entry.role})`).join(', ')}`,
    `Typography: primary=${input.profile.typography.primaryFont}, secondary=${input.profile.typography.secondaryFont ?? 'none'}`,
    `Spacing: base=${input.profile.spacing.baseUnit}, scale=${input.profile.spacing.scale.join(', ')}`,
    `Motion: intensity=${input.profile.motion.intensity}, durations=${input.profile.motion.durations.join(', ')}, easing=${input.profile.motion.easing}`,
    `Shape: radius=${input.profile.components.borderRadius}, shadow=${input.profile.components.shadowStyle}`,
  ].join('\n');

  const content = await runDesignLlm({
    llm: input.llm,
    system: 'You are a design systems editor. Output JSON only.',
    userContent: prompt,
    temperature: 0.3,
  });

  const parsed = JSON.parse(extractFirstJsonObject(content)) as {
    narrative?: unknown;
    principles?: unknown;
  };

  return {
    narrative: typeof parsed.narrative === 'string' ? parsed.narrative.trim() : undefined,
    principles: Array.isArray(parsed.principles)
      ? parsed.principles
          .map((value) => (typeof value === 'string' ? value.trim() : ''))
          .filter((value) => value.length > 0)
          .slice(0, 6)
      : undefined,
  };
}

function mergeConflicts(previous: TasteProfile | null, next: TasteConflict[]): TasteConflict[] {
  if (!previous) {
    return next;
  }

  const previousByKey = new Map<string, TasteConflict>();
  for (const conflict of previous.conflicts) {
    previousByKey.set(`${conflict.dimension}:${conflict.description}`, conflict);
  }

  return next.map((conflict) => {
    const prior = previousByKey.get(`${conflict.dimension}:${conflict.description}`);
    if (!prior) {
      return conflict;
    }
    return {
      ...conflict,
      resolved: prior.resolved,
      resolvedByDecisionId: prior.resolvedByDecisionId,
    };
  });
}

async function analyzeUrl(options: {
  rootDir: string;
  url: string;
  headed: boolean;
}): Promise<DesignAnalysis> {
  if (options.headed) {
    const result = await theatricalScan(options.url);
    return result.analysis;
  }

  const sessionName = `taste-${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`;
  const screenshotPath = path.join(os.tmpdir(), `${sessionName}.png`);
  return captureDesignFromUrl({
    url: options.url,
    sessionName,
    screenshotPath,
    workingDir: options.rootDir,
    journeySteps: 1,
    responsiveViewports: [{ label: 'desktop', width: 1440, height: 1200 }],
  });
}

function normalizeUrls(urls: string[]): string[] {
  const normalized = urls
    .map((url) => url.trim())
    .filter((url) => url.length > 0)
    .map((url) => {
      if (!looksLikeUrl(url)) {
        throw new Error(`Invalid URL/domain input: ${url}`);
      }
      return normalizeToUrl(url);
    });
  return unique(normalized);
}

export async function buildTasteProfile(options: {
  rootDir: string;
  projectId: string;
  projectName?: string;
  urls: string[];
  headed?: boolean;
  llm?: LlmConfig;
}): Promise<TasteProfile> {
  const urls = normalizeUrls(options.urls);
  if (urls.length === 0) {
    throw new Error('At least one URL is required to build a taste profile');
  }

  const db = await loadDatabase(options.rootDir);
  const project = ensureProject(db, {
    projectId: options.projectId,
    projectName: options.projectName,
  });
  await saveDatabase(options.rootDir, db);

  const previewAnalyses: DesignAnalysis[] = [];
  for (const url of urls) {
    previewAnalyses.push(await analyzeUrl({
      rootDir: options.rootDir,
      url,
      headed: Boolean(options.headed),
    }));
  }

  for (const url of urls) {
    await ingestInspiration({
      rootDir: options.rootDir,
      project: project.id,
      projectName: options.projectName,
      url,
      name: url,
      tags: ['taste'],
    });
  }

  const latestDb = await loadDatabase(options.rootDir);
  const latestProject = latestDb.projects.find((entry) => entry.id === project.id);
  if (!latestProject) {
    throw new Error(`Project not found after ingestion: ${project.id}`);
  }
  if (latestProject.inspirations.length === 0) {
    throw new Error(`No inspirations available for project: ${project.id}`);
  }

  const aggregatedColors = aggregateColors(latestProject.inspirations);
  const aggregatedTypography = aggregateTypography(latestProject.inspirations);
  const aggregatedComponents = aggregateComponents(latestProject.inspirations);
  const aggregatedMotion = aggregateMotion(latestProject.inspirations);

  const color = deriveColorPreference(aggregatedColors, latestProject.inspirations);
  const typography = deriveTypographyPreference(aggregatedTypography);
  const spacing = deriveSpacingPreference(aggregatedComponents);
  const motion = deriveMotionPreference(aggregatedMotion);
  const components = deriveComponentPreference(aggregatedComponents);

  const aggregateTokensFromProject = buildAggregateTokens(latestProject.inspirations);
  const aggregateTokensFromPreview = previewAnalyses
    .map(designAnalysisToScanTokens)
    .reduce<ScanTokens>((acc, tokens) => ({
      colors: unique([...acc.colors, ...tokens.colors]),
      fontFamilies: unique([...acc.fontFamilies, ...tokens.fontFamilies]),
      fontSizes: unique([...acc.fontSizes, ...tokens.fontSizes]),
      transitions: [...acc.transitions, ...tokens.transitions],
      spacingValues: [...acc.spacingValues, ...tokens.spacingValues],
      cssVariableCount: acc.cssVariableCount + tokens.cssVariableCount,
      framework: null,
    }), {
      colors: [],
      fontFamilies: [],
      fontSizes: [],
      transitions: [],
      spacingValues: [],
      cssVariableCount: 0,
      framework: null,
    });

  const aggregateTokens: ScanTokens = {
    colors: unique([...aggregateTokensFromProject.colors, ...aggregateTokensFromPreview.colors]),
    fontFamilies: unique([...aggregateTokensFromProject.fontFamilies, ...aggregateTokensFromPreview.fontFamilies]),
    fontSizes: unique([...aggregateTokensFromProject.fontSizes, ...aggregateTokensFromPreview.fontSizes]),
    transitions: [...aggregateTokensFromProject.transitions, ...aggregateTokensFromPreview.transitions],
    spacingValues: [...aggregateTokensFromProject.spacingValues, ...aggregateTokensFromPreview.spacingValues],
    cssVariableCount: aggregateTokensFromProject.cssVariableCount + aggregateTokensFromPreview.cssVariableCount,
    framework: null,
  };

  const aggregateScore = computeScore(aggregateTokens);
  const persona = assignPersona(aggregateTokens);
  const detectedConflicts = detectConflicts(latestProject.inspirations);

  const previous = await loadTasteProfile(options.rootDir, project.id);
  const now = nowIso();
  const profile: TasteProfile = {
    id: project.id,
    name: options.projectName?.trim() || latestProject.name,
    version: (previous?.version ?? 0) + 1,
    sourceInspirationIds: latestProject.inspirations.map((inspiration) => inspiration.id),
    sourceUrls: unique(latestProject.inspirations.map((inspiration) => inspiration.url).filter((url): url is string => Boolean(url))),
    persona,
    aggregateScore,
    color,
    typography,
    spacing,
    motion,
    components: {
      ...components,
      cherryPicks: previous?.components.cherryPicks ?? [],
    },
    decisions: previous?.decisions ?? [],
    conflicts: mergeConflicts(previous, detectedConflicts),
    narrative: previous?.narrative,
    principles: previous?.principles,
    createdAt: previous?.createdAt ?? now,
    updatedAt: now,
  };

  try {
    const narrative = await maybeGenerateNarrative({
      llm: options.llm,
      profile,
    });
    profile.narrative = narrative.narrative ?? profile.narrative;
    profile.principles = narrative.principles ?? profile.principles;
  } catch {
    // LLM enrichment is optional for taste profile building.
  }

  await saveTasteProfile(options.rootDir, profile);
  return profile;
}
