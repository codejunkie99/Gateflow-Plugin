import { runDesignLlm } from './llm.js';
import type { LlmConfig, TasteProfile } from './types.js';

function resolvePaletteColor(taste: TasteProfile, role: string, fallbackIndex: number, fallback: string): string {
  const byRole = taste.color.palette.find((entry) => entry.role.toLowerCase() === role);
  if (byRole) {
    return byRole.hex.toUpperCase();
  }
  return taste.color.palette[fallbackIndex]?.hex?.toUpperCase() ?? fallback;
}

function formatFontVariable(font: string | null): string {
  if (!font) {
    return `'Inter', sans-serif`;
  }
  return `'${font.replace(/'/g, "\\'")}', sans-serif`;
}

function textSizeVarName(index: number): string {
  const names = ['sm', 'base', 'lg', 'xl', '2xl', '3xl', '4xl', '5xl'];
  return `--text-${names[index] ?? `step-${index + 1}`}`;
}

function durationVarName(index: number): string {
  const names = ['fast', 'normal', 'slow', 'slower'];
  return `--duration-${names[index] ?? `step-${index + 1}`}`;
}

function spacingVarName(value: number, index: number): string {
  const twIndex = Math.round(value / 4);
  if (twIndex > 0) {
    return `--space-${twIndex}`;
  }
  return `--space-step-${index + 1}`;
}

export function generateDesignTokens(taste: TasteProfile): string {
  const primary = resolvePaletteColor(taste, 'primary', 0, '#111111');
  const background = resolvePaletteColor(taste, 'background', 1, '#FFFFFF');
  const accent = resolvePaletteColor(taste, 'accent', 2, primary);
  const text = resolvePaletteColor(taste, 'text', 3, '#000000');
  const surface = resolvePaletteColor(taste, 'surface', 4, '#FFFFFF');

  const typographyLines = taste.typography.sizes
    .slice(0, 8)
    .map((size, index) => `  ${textSizeVarName(index)}: ${size};`);
  const spacingLines = taste.spacing.scale
    .slice(0, 12)
    .map((value, index) => `  ${spacingVarName(value, index)}: ${Math.round(value)}px;`);
  const durationLines = taste.motion.durations
    .slice(0, 4)
    .map((duration, index) => `  ${durationVarName(index)}: ${duration};`);

  return [
    ':root {',
    '  /* Colors — from taste profile */',
    `  --color-primary: ${primary};`,
    `  --color-background: ${background};`,
    `  --color-accent: ${accent};`,
    `  --color-text: ${text};`,
    `  --color-surface: ${surface};`,
    '',
    '  /* Typography */',
    `  --font-primary: ${formatFontVariable(taste.typography.primaryFont)};`,
    `  --font-secondary: ${formatFontVariable(taste.typography.secondaryFont)};`,
    ...typographyLines,
    '',
    '  /* Spacing */',
    ...spacingLines,
    '',
    '  /* Motion */',
    ...(durationLines.length > 0 ? durationLines : ['  --duration-normal: 200ms;']),
    `  --easing-default: ${taste.motion.easing};`,
    '',
    '  /* Shape */',
    `  --radius-default: ${taste.components.borderRadius};`,
    '}',
  ].join('\n');
}

function extractCodeBlock(raw: string): { code: string; explanation: string } {
  const match = raw.match(/```[a-zA-Z0-9_-]*\n([\s\S]*?)```/);
  if (!match) {
    return {
      code: raw.trim(),
      explanation: 'Generated directly from LLM output.',
    };
  }

  const code = match[1].trim();
  const explanation = raw
    .replace(match[0], '')
    .trim()
    .replace(/^[-:\s]+/, '');

  return {
    code,
    explanation: explanation || 'Generated from taste profile context.',
  };
}

function buildGenerationPrompt(options: {
  taste: TasteProfile;
  target: 'component' | 'page' | 'tokens';
  componentKind?: string;
  framework?: string;
}): string {
  const framework = options.framework?.trim() || 'vanilla HTML/CSS';
  const palette = options.taste.color.palette
    .map((entry) => `${entry.role}:${entry.hex}`)
    .join(', ');
  const principles = (options.taste.principles ?? []).join(' | ') || 'Keep output minimal and coherent.';
  const cherryPicks = options.taste.components.cherryPicks
    .map((pick) => `${pick.componentKind} from ${pick.sourceUrl} (${Object.entries(pick.styles).slice(0, 4).map(([k, v]) => `${k}:${v}`).join(', ')})`)
    .join('\n');

  return [
    `You are a frontend developer. Generate production-ready ${framework} code matching this taste profile.`,
    '',
    `Persona: ${options.taste.persona.name} — "${options.taste.persona.tagline}"`,
    `Palette: ${palette}`,
    `Typography: Primary=${options.taste.typography.primaryFont}, Secondary=${options.taste.typography.secondaryFont ?? 'none'}`,
    `Spacing: ${options.taste.spacing.baseUnit}px base, scale=[${options.taste.spacing.scale.join(', ')}]`,
    `Motion: ${options.taste.motion.intensity}, ${options.taste.motion.durations.join(', ')}, ${options.taste.motion.easing}`,
    `Shape: radius=${options.taste.components.borderRadius}, shadow=${options.taste.components.shadowStyle}`,
    `Principles: ${principles}`,
    '',
    'Cherry-picked references:',
    cherryPicks || '- none',
    '',
    `Generate: ${options.target}${options.componentKind ? ` (${options.componentKind})` : ''}`,
    'Requirements: Use exact token values. Semantic HTML. Accessible.',
    'Output: Single code block, then a 2-sentence explanation.',
  ].join('\n');
}

export async function generateFromTaste(options: {
  taste: TasteProfile;
  target: 'component' | 'page' | 'tokens';
  componentKind?: string;
  llm?: LlmConfig;
  framework?: string;
}): Promise<{ code: string; explanation: string }> {
  if (options.target === 'tokens') {
    return {
      code: generateDesignTokens(options.taste),
      explanation: 'Generated deterministic CSS custom properties from the saved taste profile.',
    };
  }

  if (!options.llm) {
    throw new Error('LLM configuration is required for component/page generation');
  }

  const content = await runDesignLlm({
    llm: options.llm,
    system: 'You are a senior frontend engineer. Return only a code block followed by a short explanation.',
    userContent: buildGenerationPrompt({
      taste: options.taste,
      target: options.target,
      componentKind: options.componentKind,
      framework: options.framework,
    }),
    temperature: 0.2,
  });

  return extractCodeBlock(content);
}
