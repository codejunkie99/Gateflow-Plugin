import { readdirSync, readFileSync, statSync, existsSync } from 'node:fs';
import { join, extname } from 'node:path';
import type { ScanTokens, ScanScore, ScanResult, DesignAnalysis, AnimationToken, MotionToken } from './types.js';
import { assignPersona } from './persona.js';
import { theatricalScan } from './theatrical.js';

/* ─── File collection ─── */

const SKIP_DIRS = new Set([
  'node_modules', '.git', 'dist', 'build', '.next', '.nuxt',
  '.output', 'coverage', 'vendor', '.svelte-kit', '__pycache__',
]);

const SCAN_EXTENSIONS = new Set([
  '.css', '.scss', '.sass', '.less', '.styl',
  '.tsx', '.jsx', '.vue', '.svelte',
  '.html', '.htm',
]);

export function collectFiles(dir: string): string[] {
  const results: string[] = [];

  function walk(current: string): void {
    let entries: string[];
    try {
      entries = readdirSync(current);
    } catch {
      return;
    }
    for (const entry of entries) {
      if (entry.startsWith('.') && entry !== '.') continue;
      const full = join(current, entry);
      let stat;
      try {
        stat = statSync(full);
      } catch {
        continue;
      }
      if (stat.isDirectory()) {
        if (!SKIP_DIRS.has(entry)) walk(full);
      } else if (SCAN_EXTENSIONS.has(extname(entry).toLowerCase())) {
        results.push(full);
      }
    }
  }

  walk(dir);
  return results;
}

/* ─── CSS content scanning ─── */

const HEX_COLOR_RE = /#(?:[0-9a-fA-F]{3}){1,2}\b/g;
const RGB_COLOR_RE = /rgba?\(\s*(\d{1,3})\s*,\s*(\d{1,3})\s*,\s*(\d{1,3})/g;
const FONT_FAMILY_RE = /font-family\s*:\s*([^;}]+)/g;
const FONT_SIZE_RE = /font-size\s*:\s*([^;}"']+)/g;
const TRANSITION_RE = /transition\s*:\s*([^;}"']+)/g;
const ANIMATION_RE = /animation\s*:\s*([^;}"']+)/g;
const SPACING_RE = /(?:margin|padding|gap|row-gap|column-gap)\s*:\s*([^;}"']+)/g;
const CSS_VAR_RE = /--[\w-]+\s*:/g;

function rgbToHex(r: number, g: number, b: number): string {
  const toHex = (n: number) => Math.max(0, Math.min(255, n)).toString(16).padStart(2, '0');
  return `#${toHex(r)}${toHex(g)}${toHex(b)}`;
}

function normalizeHex(hex: string): string {
  const clean = hex.replace('#', '').toLowerCase();
  if (clean.length === 3) {
    return `#${clean[0]}${clean[0]}${clean[1]}${clean[1]}${clean[2]}${clean[2]}`;
  }
  return `#${clean}`;
}

export function scanCssContent(css: string): Omit<ScanTokens, 'framework'> {
  const colors = new Set<string>();
  const fontFamilies = new Set<string>();
  const fontSizes = new Set<string>();
  const transitions: string[] = [];
  const spacingValues: string[] = [];

  // Hex colors
  for (const m of css.matchAll(HEX_COLOR_RE)) {
    colors.add(normalizeHex(m[0]));
  }

  // RGB/RGBA colors
  for (const m of css.matchAll(RGB_COLOR_RE)) {
    colors.add(rgbToHex(parseInt(m[1]), parseInt(m[2]), parseInt(m[3])));
  }

  // Font families
  for (const m of css.matchAll(FONT_FAMILY_RE)) {
    const families = m[1].split(',').map(f => f.trim().replace(/['"]/g, '').toLowerCase());
    for (const f of families) {
      if (f && !f.startsWith('var(') && f !== 'inherit' && f !== 'initial') {
        fontFamilies.add(f);
      }
    }
  }

  // Font sizes
  for (const m of css.matchAll(FONT_SIZE_RE)) {
    fontSizes.add(m[1].trim().toLowerCase());
  }

  // Transitions
  for (const m of css.matchAll(TRANSITION_RE)) {
    transitions.push(m[1].trim());
  }
  for (const m of css.matchAll(ANIMATION_RE)) {
    transitions.push(m[1].trim());
  }

  // Spacing
  for (const m of css.matchAll(SPACING_RE)) {
    spacingValues.push(m[1].trim());
  }

  // CSS variables
  const cssVariableCount = [...css.matchAll(CSS_VAR_RE)].length;

  return {
    colors: [...colors],
    fontFamilies: [...fontFamilies],
    fontSizes: [...fontSizes],
    transitions,
    spacingValues,
    cssVariableCount,
  };
}

/* ─── Tailwind class scanning (for .tsx/.jsx/.vue/.svelte) ─── */

const TW_COLOR_CLASSES = /(?:bg|text|border|ring|fill|stroke|accent|outline|decoration|shadow)-(?:slate|gray|zinc|neutral|stone|red|orange|amber|yellow|lime|green|emerald|teal|cyan|sky|blue|indigo|violet|purple|fuchsia|pink|rose)-(\d{2,3})\b/g;
const TW_SPACING_CLASSES = /(?:p|px|py|pt|pb|pl|pr|m|mx|my|mt|mb|ml|mr|gap|space-x|space-y)-(\d+(?:\.5)?)\b/g;
const TW_FONT_CLASSES = /font-(?:sans|serif|mono|thin|extralight|light|normal|medium|semibold|bold|extrabold|black)\b/g;
const TW_TEXT_SIZE_CLASSES = /text-(?:xs|sm|base|lg|xl|2xl|3xl|4xl|5xl|6xl|7xl|8xl|9xl)\b/g;
const TW_TRANSITION_CLASSES = /transition(?:-(?:all|colors|opacity|shadow|transform|none))?\b/g;

function scanTailwindClasses(content: string): Partial<ScanTokens> {
  const colors = new Set<string>();
  const fontFamilies = new Set<string>();
  const fontSizes = new Set<string>();
  const transitions: string[] = [];
  const spacingValues: string[] = [];

  // Tailwind color classes → track as palette indicators
  for (const m of content.matchAll(TW_COLOR_CLASSES)) {
    colors.add(`tw:${m[0]}`);
  }

  // Spacing
  for (const m of content.matchAll(TW_SPACING_CLASSES)) {
    const val = parseFloat(m[1]);
    spacingValues.push(`${val * 4}px`);
  }

  // Font families
  for (const m of content.matchAll(TW_FONT_CLASSES)) {
    fontFamilies.add(m[0].replace('font-', ''));
  }

  // Text sizes
  for (const m of content.matchAll(TW_TEXT_SIZE_CLASSES)) {
    fontSizes.add(m[0]);
  }

  // Transitions
  for (const m of content.matchAll(TW_TRANSITION_CLASSES)) {
    transitions.push(m[0]);
  }

  return {
    colors: [...colors],
    fontFamilies: [...fontFamilies],
    fontSizes: [...fontSizes],
    transitions,
    spacingValues,
  };
}

/* ─── Framework detection ─── */

export async function detectFramework(scanPath: string): Promise<string | null> {
  // Check package.json
  const pkgPath = join(scanPath, 'package.json');
  if (existsSync(pkgPath)) {
    try {
      const pkg = JSON.parse(readFileSync(pkgPath, 'utf-8'));
      const allDeps = { ...pkg.dependencies, ...pkg.devDependencies };
      if (allDeps['tailwindcss']) return 'tailwind';
      if (allDeps['@chakra-ui/react']) return 'chakra';
      if (allDeps['@mui/material']) return 'mui';
    } catch {
      // ignore parse errors
    }
  }

  // Check for tailwind config files
  const twConfigs = ['tailwind.config.js', 'tailwind.config.ts', 'tailwind.config.mjs', 'tailwind.config.cjs'];
  for (const config of twConfigs) {
    if (existsSync(join(scanPath, config))) return 'tailwind';
  }

  return null;
}

/* ─── Token merging ─── */

function mergeTokens(a: Omit<ScanTokens, 'framework'>, b: Partial<ScanTokens>): Omit<ScanTokens, 'framework'> {
  return {
    colors: [...new Set([...a.colors, ...(b.colors ?? [])])],
    fontFamilies: [...new Set([...a.fontFamilies, ...(b.fontFamilies ?? [])])],
    fontSizes: [...new Set([...a.fontSizes, ...(b.fontSizes ?? [])])],
    transitions: [...a.transitions, ...(b.transitions ?? [])],
    spacingValues: [...a.spacingValues, ...(b.spacingValues ?? [])],
    cssVariableCount: a.cssVariableCount + (b.cssVariableCount ?? 0),
  };
}

/* ─── Score computation ─── */

function computeScore(tokens: ScanTokens): ScanScore {
  // Color Discipline (0–25): fewer unique colors = higher score
  const colorCount = tokens.colors.length;
  let colorDiscipline: number;
  if (colorCount === 0) colorDiscipline = 5;           // no colors found → low score
  else if (colorCount <= 5) colorDiscipline = 25;       // extremely disciplined
  else if (colorCount <= 10) colorDiscipline = 22;
  else if (colorCount <= 15) colorDiscipline = 18;
  else if (colorCount <= 25) colorDiscipline = 14;
  else if (colorCount <= 40) colorDiscipline = 10;
  else colorDiscipline = 6;
  // Bonus for CSS variables or framework
  if (tokens.cssVariableCount >= 5) colorDiscipline = Math.min(25, colorDiscipline + 2);
  if (tokens.framework) colorDiscipline = Math.min(25, colorDiscipline + 1);

  // Typography System (0–25): fewer families + consistent scale = better
  const fontCount = tokens.fontFamilies.length;
  let typographySystem: number;
  if (fontCount === 0) typographySystem = 5;
  else if (fontCount <= 2) typographySystem = 25;
  else if (fontCount <= 3) typographySystem = 20;
  else if (fontCount <= 5) typographySystem = 15;
  else typographySystem = 8;
  // Bonus for consistent size scale
  if (tokens.fontSizes.length >= 3 && tokens.fontSizes.length <= 8) {
    typographySystem = Math.min(25, typographySystem + 2);
  }

  // Spacing & Layout (0–25): grid alignment = better
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
  const gridRatio = totalSpacing > 0 ? gridAligned / totalSpacing : 0;
  let spacingLayout = Math.round(gridRatio * 20);
  if (totalSpacing === 0) spacingLayout = 5;
  // Bonus for CSS variables in spacing
  if (tokens.cssVariableCount >= 3) spacingLayout = Math.min(25, spacingLayout + 3);
  if (tokens.framework) spacingLayout = Math.min(25, spacingLayout + 2);

  // Motion & Polish (0–25): having transitions = good, consistency = bonus
  const motionCount = tokens.transitions.length;
  let motionPolish: number;
  if (motionCount === 0) motionPolish = 5;
  else if (motionCount <= 3) motionPolish = 15;
  else if (motionCount <= 10) motionPolish = 22;
  else if (motionCount <= 20) motionPolish = 25;
  else motionPolish = 20; // too many different durations = slight penalty
  // Check timing consistency
  const durations = new Set<string>();
  for (const t of tokens.transitions) {
    const durationMatch = t.match(/(\d+(?:\.\d+)?m?s)/g);
    if (durationMatch) {
      for (const d of durationMatch) durations.add(d);
    }
  }
  if (durations.size > 0 && durations.size <= 3) {
    motionPolish = Math.min(25, motionPolish + 2); // consistent timing
  }

  const total = colorDiscipline + typographySystem + spacingLayout + motionPolish;

  return { colorDiscipline, typographySystem, spacingLayout, motionPolish, total };
}

/* ─── URL detection ─── */

export function looksLikeUrl(input: string): boolean {
  if (input.startsWith('http://') || input.startsWith('https://')) return true;
  // Bare domain: has dot, no path separator at start, valid TLD pattern
  if (/^[a-zA-Z0-9-]+\.[a-zA-Z]{2,}/.test(input) && !input.startsWith('.') && !input.startsWith('/')) return true;
  return false;
}

export function normalizeToUrl(input: string): string {
  if (input.startsWith('http://') || input.startsWith('https://')) return input;
  return `https://${input}`;
}

/* ─── DesignAnalysis → ScanTokens bridge ─── */

function isAnimationToken(token: MotionToken | AnimationToken): token is AnimationToken {
  return 'library' in token && 'motionIntent' in token;
}

export function designAnalysisToScanTokens(analysis: DesignAnalysis): ScanTokens {
  const transitionValues: string[] = [];
  for (const m of analysis.motion) {
    if (isAnimationToken(m)) {
      if (m.timing) {
        transitionValues.push(`${m.motionIntent} ${m.timing.duration}ms ${m.timing.easing}`);
      }
    } else {
      if (m.transition && m.transition !== 'all 0s ease 0s') {
        transitionValues.push(m.transition);
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

/* ─── Main scan function ─── */

export async function scanDesignSystem(scanPath: string): Promise<ScanResult> {
  const framework = await detectFramework(scanPath);
  const files = collectFiles(scanPath);

  let merged: Omit<ScanTokens, 'framework'> = {
    colors: [],
    fontFamilies: [],
    fontSizes: [],
    transitions: [],
    spacingValues: [],
    cssVariableCount: 0,
  };

  for (const file of files) {
    let content: string;
    try {
      content = readFileSync(file, 'utf-8');
    } catch {
      continue;
    }

    const ext = extname(file).toLowerCase();

    // CSS-like files get full CSS scanning
    if (['.css', '.scss', '.sass', '.less', '.styl'].includes(ext)) {
      merged = mergeTokens(merged, scanCssContent(content));
    }
    // Template/component files get both CSS and Tailwind scanning
    else if (['.tsx', '.jsx', '.vue', '.svelte', '.html', '.htm'].includes(ext)) {
      merged = mergeTokens(merged, scanCssContent(content));
      if (framework === 'tailwind') {
        merged = mergeTokens(merged, scanTailwindClasses(content));
      }
    }
  }

  const tokens: ScanTokens = { ...merged, framework };
  const score = computeScore(tokens);
  const persona = assignPersona(tokens);

  return {
    path: scanPath,
    filesScanned: files.length,
    tokens,
    score,
    persona,
    framework,
  };
}

/* ─── URL scan function ─── */

export async function scanFromUrl(url: string): Promise<ScanResult> {
  const { analysis } = await theatricalScan(url);
  const tokens = designAnalysisToScanTokens(analysis);
  const score = computeScore(tokens);
  const persona = assignPersona(tokens);

  return {
    path: url,
    filesScanned: 0,
    tokens,
    score,
    persona,
    framework: null,
  };
}
