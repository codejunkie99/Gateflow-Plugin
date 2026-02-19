import type { PersonaMatch, ScanTokens } from './types.js';

interface PersonaSignals {
  uniqueColorCount: number;
  cssVarUsage: boolean;
  spacingGridAlignment: number;   // 0–1, fraction of values on 4/8px grid
  typographyVariety: number;      // distinct font families
  isMonochrome: boolean;          // ≤3 distinct hue families
  motionCount: number;
  hasFramework: boolean;
}

function hexToHsl(hex: string): { h: number; s: number; l: number } | null {
  const clean = hex.replace('#', '');
  if (clean.length !== 6 && clean.length !== 3) return null;
  const full = clean.length === 3
    ? clean[0] + clean[0] + clean[1] + clean[1] + clean[2] + clean[2]
    : clean;
  const r = parseInt(full.slice(0, 2), 16) / 255;
  const g = parseInt(full.slice(2, 4), 16) / 255;
  const b = parseInt(full.slice(4, 6), 16) / 255;

  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const l = (max + min) / 2;

  if (max === min) return { h: 0, s: 0, l };

  const d = max - min;
  const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
  let h = 0;
  if (max === r) h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
  else if (max === g) h = ((b - r) / d + 2) / 6;
  else h = ((r - g) / d + 4) / 6;

  return { h: h * 360, s, l };
}

function extractSignals(tokens: ScanTokens): PersonaSignals {
  const uniqueColorCount = tokens.colors.length;
  const cssVarUsage = tokens.cssVariableCount > 0;
  const typographyVariety = tokens.fontFamilies.length;
  const motionCount = tokens.transitions.length;
  const hasFramework = tokens.framework !== null;

  // Spacing grid alignment: what fraction of values are multiples of 4px
  let gridAligned = 0;
  let totalSpacing = 0;
  for (const val of tokens.spacingValues) {
    const nums = val.match(/(\d+(?:\.\d+)?)/g);
    if (!nums) continue;
    for (const n of nums) {
      const px = parseFloat(n);
      if (px > 0) {
        totalSpacing++;
        if (px % 4 === 0) gridAligned++;
      }
    }
  }
  const spacingGridAlignment = totalSpacing > 0 ? gridAligned / totalSpacing : 0;

  // Monochrome check: ≤3 distinct hue buckets (30-degree buckets)
  const hueBuckets = new Set<number>();
  for (const color of tokens.colors) {
    const hsl = hexToHsl(color);
    if (!hsl) continue;
    if (hsl.s < 0.1) continue; // skip grays
    hueBuckets.add(Math.floor(hsl.h / 30));
  }
  const isMonochrome = hueBuckets.size <= 3;

  return {
    uniqueColorCount,
    cssVarUsage,
    spacingGridAlignment,
    typographyVariety,
    isMonochrome,
    motionCount,
    hasFramework,
  };
}

// Clamp to 0–1
function clamp01(n: number): number {
  return Math.max(0, Math.min(1, n));
}

interface PersonaDef {
  name: string;
  tagline: string;
  score: (s: PersonaSignals) => number;
  reasoning: (s: PersonaSignals) => string;
}

const PERSONAS: PersonaDef[] = [
  {
    name: 'Jony Ive',
    tagline: 'Less, but better \u2014 with a unibody finish',
    score: (s) => {
      let v = 0;
      // Low color count rewards
      v += clamp01(1 - s.uniqueColorCount / 20) * 0.25;
      // CSS variable usage (systemization)
      v += s.cssVarUsage ? 0.15 : 0;
      // Monochrome palette
      v += s.isMonochrome ? 0.2 : 0;
      // Grid-aligned spacing
      v += s.spacingGridAlignment * 0.2;
      // Minimal typography
      v += clamp01(1 - s.typographyVariety / 5) * 0.1;
      // Minimal motion (not zero, but restrained)
      v += (s.motionCount > 0 && s.motionCount <= 8) ? 0.1 : 0;
      return clamp01(v);
    },
    reasoning: (s) =>
      `Your codebase shows restrained color use (${s.uniqueColorCount} unique colors), ` +
      `${s.isMonochrome ? 'monochromatic palette, ' : ''}` +
      `and ${s.typographyVariety <= 2 ? 'minimal' : 'moderate'} typography \u2014 ` +
      `hallmarks of Ive's reductive design philosophy.`,
  },
  {
    name: 'Dieter Rams',
    tagline: 'Good design is as little design as possible',
    score: (s) => {
      let v = 0;
      // Strong grid alignment
      v += s.spacingGridAlignment * 0.3;
      // Few colors
      v += clamp01(1 - s.uniqueColorCount / 15) * 0.2;
      // Systematic (CSS vars)
      v += s.cssVarUsage ? 0.2 : 0;
      // Very few fonts (1-2)
      v += s.typographyVariety <= 2 ? 0.2 : (s.typographyVariety <= 3 ? 0.1 : 0);
      // No excess motion
      v += s.motionCount <= 3 ? 0.1 : 0;
      return clamp01(v);
    },
    reasoning: (s) =>
      `Strong grid alignment (${Math.round(s.spacingGridAlignment * 100)}% on grid), ` +
      `${s.cssVarUsage ? 'systematic CSS variables, ' : ''}` +
      `and ${s.typographyVariety} font ${s.typographyVariety === 1 ? 'family' : 'families'} \u2014 ` +
      `your design is honest, functional, and unobtrusive.`,
  },
  {
    name: 'Virgil Abloh',
    tagline: 'Everything in quotes \u2014 design is a DJ set',
    score: (s) => {
      let v = 0;
      // Mixed fonts (variety is good)
      v += clamp01(s.typographyVariety / 5) * 0.25;
      // Off-grid spacing (low alignment)
      v += clamp01(1 - s.spacingGridAlignment) * 0.2;
      // Bold color variety
      v += clamp01(s.uniqueColorCount / 20) * 0.25;
      // Not monochrome
      v += s.isMonochrome ? 0 : 0.15;
      // Some motion
      v += s.motionCount > 3 ? 0.15 : 0;
      return clamp01(v);
    },
    reasoning: (s) =>
      `${s.typographyVariety} font families, ${s.uniqueColorCount} colors, and ` +
      `${Math.round((1 - s.spacingGridAlignment) * 100)}% off-grid spacing \u2014 ` +
      `your design remixes conventions with bold, eclectic energy.`,
  },
  {
    name: 'Ye',
    tagline: 'No More Parties in LA \u2014 but make it brutalist',
    score: (s) => {
      let v = 0;
      // Extreme minimalism (very few colors) OR extreme maximalism (lots)
      const extremeMin = s.uniqueColorCount <= 4;
      const extremeMax = s.uniqueColorCount >= 25;
      v += (extremeMin || extremeMax) ? 0.25 : 0;
      // Few fonts (1-2)
      v += s.typographyVariety <= 2 ? 0.15 : 0;
      // Strong contrast (monochrome or very bold)
      v += s.isMonochrome ? 0.1 : (s.uniqueColorCount >= 25 ? 0.1 : 0);
      // No framework (raw, custom)
      v += s.hasFramework ? 0 : 0.1;
      // Little to no motion (brutalist)
      v += s.motionCount <= 2 ? 0.15 : 0;
      // Anti-systematic: CSS vars and grid alignment indicate polish, not brutalism
      if (s.cssVarUsage) v -= 0.15;
      if (s.spacingGridAlignment > 0.5) v -= 0.1;
      return clamp01(v);
    },
    reasoning: (s) =>
      `${s.uniqueColorCount <= 4 ? 'Extreme minimalism' : s.uniqueColorCount >= 25 ? 'Extreme maximalism' : 'Bold choices'} ` +
      `with ${s.typographyVariety} font ${s.typographyVariety === 1 ? 'family' : 'families'}` +
      `${s.motionCount <= 2 ? ' and zero-frills motion' : ''} \u2014 ` +
      `raw, uncompromising, brutalist energy.`,
  },
  {
    name: 'Paula Scher',
    tagline: 'Make it bigger \u2014 typography IS the design',
    score: (s) => {
      let v = 0;
      // High typography variety
      v += clamp01(s.typographyVariety / 5) * 0.3;
      // Bold color palette (many colors)
      v += clamp01(s.uniqueColorCount / 15) * 0.25;
      // Not monochrome
      v += s.isMonochrome ? 0 : 0.2;
      // Expressive motion
      v += s.motionCount > 5 ? 0.15 : (s.motionCount > 2 ? 0.08 : 0);
      // Font sizes variety as proxy (uses fontSizes from scan)
      v += 0.1; // base bonus for expressive intent
      return clamp01(v);
    },
    reasoning: (s) =>
      `${s.typographyVariety} font families and ${s.uniqueColorCount} colors ` +
      `${s.motionCount > 5 ? 'with expressive motion ' : ''}` +
      `create a bold, typographic-first design language.`,
  },
  {
    name: 'Massimo Vignelli',
    tagline: 'One typeface is enough \u2014 if it\'s Helvetica',
    score: (s) => {
      let v = 0;
      // Very few fonts (ideally 1-2)
      v += s.typographyVariety <= 2 ? 0.35 : (s.typographyVariety === 3 ? 0.15 : 0);
      // Systematic spacing
      v += s.spacingGridAlignment * 0.25;
      // Neutral/restrained palette
      v += clamp01(1 - s.uniqueColorCount / 12) * 0.2;
      // CSS vars (systematic)
      v += s.cssVarUsage ? 0.1 : 0;
      // No decoration (low motion)
      v += s.motionCount <= 2 ? 0.1 : 0;
      return clamp01(v);
    },
    reasoning: (s) =>
      `${s.typographyVariety} font ${s.typographyVariety === 1 ? 'family' : 'families'}, ` +
      `${Math.round(s.spacingGridAlignment * 100)}% grid-aligned spacing, and ` +
      `${s.uniqueColorCount} colors \u2014 ` +
      `systematic, disciplined, timeless.`,
  },
];

export function assignPersona(tokens: ScanTokens): PersonaMatch {
  const signals = extractSignals(tokens);

  let best: PersonaDef = PERSONAS[0];
  let bestScore = -1;

  for (const persona of PERSONAS) {
    const s = persona.score(signals);
    if (s > bestScore) {
      bestScore = s;
      best = persona;
    }
  }

  return {
    name: best.name,
    tagline: best.tagline,
    score: bestScore,
    reasoning: best.reasoning(signals),
  };
}
