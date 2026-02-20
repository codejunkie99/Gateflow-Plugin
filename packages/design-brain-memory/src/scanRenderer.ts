import type { ScanResult, ScanScore } from './types.js';

/* ─── ANSI helpers ─── */

const USE_COLOR = process.stdout.isTTY !== false;

const RESET  = USE_COLOR ? '\x1b[0m' : '';
const BOLD   = USE_COLOR ? '\x1b[1m' : '';
const DIM    = USE_COLOR ? '\x1b[2m' : '';
const GREEN  = USE_COLOR ? '\x1b[32m' : '';
const CYAN   = USE_COLOR ? '\x1b[36m' : '';
const YELLOW = USE_COLOR ? '\x1b[33m' : '';
const WHITE  = USE_COLOR ? '\x1b[37m' : '';
const MAGENTA = USE_COLOR ? '\x1b[35m' : '';

/* ─── Box drawing ─── */

const BOX_WIDTH = 48;

function topBorder(title?: string): string {
  if (title) {
    const label = `\u2500 ${title} `;
    const rest = '\u2500'.repeat(Math.max(0, BOX_WIDTH - label.length - 1));
    return `  ${DIM}\u250c${label}${rest}\u2510${RESET}`;
  }
  return `  ${DIM}\u250c${'\u2500'.repeat(BOX_WIDTH)}\u2510${RESET}`;
}

function bottomBorder(): string {
  return `  ${DIM}\u2514${'\u2500'.repeat(BOX_WIDTH)}\u2518${RESET}`;
}

function boxLine(content: string, rawLength: number): string {
  const padding = Math.max(0, BOX_WIDTH - rawLength);
  return `  ${DIM}\u2502${RESET} ${content}${' '.repeat(padding - 1)}${DIM}\u2502${RESET}`;
}

function emptyBoxLine(): string {
  return `  ${DIM}\u2502${' '.repeat(BOX_WIDTH)}\u2502${RESET}`;
}

/* ─── Score bar ─── */

function scoreBar(label: string, value: number, max: number): string {
  const barWidth = 16;
  const filled = Math.round((value / max) * barWidth);
  const empty = barWidth - filled;
  const bar = `${GREEN}\u2588${RESET}`.repeat(filled) + `${DIM}\u2591${RESET}`.repeat(empty);
  const paddedLabel = label.padEnd(22);
  const valueStr = `${value}`.padStart(2);
  return `${paddedLabel}${bar}  ${BOLD}${valueStr}${RESET}`;
}

function scoreBarRaw(label: string, value: number, max: number): number {
  // Raw length without ANSI
  return label.padEnd(22).length + 16 + 2 + `${value}`.padStart(2).length;
}

/* ─── Checkmark lines ─── */

function check(text: string): string {
  return `  ${GREEN}\u2714${RESET} ${text}`;
}

/* ─── Framework display name ─── */

function frameworkName(fw: string | null): string {
  if (!fw) return 'None detected';
  const names: Record<string, string> = {
    tailwind: 'Tailwind CSS',
    chakra: 'Chakra UI',
    mui: 'Material UI',
  };
  return names[fw] ?? fw;
}

/* ─── Main renderer ─── */

export function renderScanResults(result: ScanResult): void {
  const { tokens, score, persona, filesScanned, framework } = result;

  console.log('');

  // Header box
  console.log(topBorder());
  console.log(emptyBoxLine());
  const title = `${BOLD}${CYAN}design-brain${RESET}  v0.9.2`;
  console.log(boxLine(title, 'design-brain  v0.9.2'.length));
  const subtitle = `${DIM}Relational design memory${RESET}`;
  console.log(boxLine(subtitle, 'Relational design memory'.length));
  console.log(emptyBoxLine());
  console.log(bottomBorder());

  console.log('');

  // Checkmark summary
  const isUrl = result.path.startsWith('http://') || result.path.startsWith('https://');
  if (isUrl) {
    console.log(check(`Scanned ${BOLD}${result.path}${RESET} (live site)`));
  } else {
    console.log(check(`Scanned ${BOLD}${filesScanned}${RESET} files`));
  }
  console.log(check(
    `Found ${BOLD}${tokens.colors.length}${RESET} colors, ` +
    `${BOLD}${tokens.fontFamilies.length}${RESET} fonts, ` +
    `${BOLD}${tokens.spacingValues.length}${RESET} spacing values, ` +
    `${BOLD}${tokens.transitions.length}${RESET} transitions`
  ));
  if (framework) {
    console.log(check(`Detected framework: ${BOLD}${frameworkName(framework)}${RESET}`));
  }
  console.log(check(`Design Health Score: ${BOLD}${scoreColor(score.total)}${score.total}/100${RESET}`));

  console.log('');

  // Score breakdown box
  console.log(topBorder('Design Health'));
  console.log(emptyBoxLine());

  const categories: Array<[string, number, number]> = [
    ['Color Discipline', score.colorDiscipline, 25],
    ['Typography System', score.typographySystem, 25],
    ['Spacing & Layout', score.spacingLayout, 25],
    ['Motion & Polish', score.motionPolish, 25],
  ];

  for (const [label, value, max] of categories) {
    const bar = scoreBar(label, value, max);
    const rawLen = scoreBarRaw(label, value, max);
    console.log(boxLine(bar, rawLen));
  }

  console.log(emptyBoxLine());
  const totalBar = scoreBar('Total', score.total, 100);
  const totalRawLen = scoreBarRaw('Total', score.total, 100);
  console.log(boxLine(totalBar, totalRawLen));
  console.log(emptyBoxLine());
  console.log(bottomBorder());

  console.log('');

  // Persona box
  console.log(topBorder('Your Design Persona'));
  console.log(emptyBoxLine());

  const personaLine = `${MAGENTA}\u{1f3a8}${RESET}  ${BOLD}${persona.name}${RESET}`;
  console.log(boxLine(personaLine, `\u{1f3a8}  ${persona.name}`.length + 1));

  // Tagline (wrapped)
  const tagline = `${DIM}"${persona.tagline}"${RESET}`;
  console.log(boxLine(tagline, `"${persona.tagline}"`.length));

  console.log(emptyBoxLine());

  // Reasoning (word-wrap to box width)
  const reasonLines = wordWrap(persona.reasoning, BOX_WIDTH - 4);
  for (const line of reasonLines) {
    console.log(boxLine(`${DIM}${line}${RESET}`, line.length));
  }

  console.log(emptyBoxLine());
  console.log(bottomBorder());

  console.log('');
}

function scoreColor(total: number): string {
  if (total >= 75) return GREEN;
  if (total >= 50) return YELLOW;
  return '\x1b[31m'; // red
}

function wordWrap(text: string, maxWidth: number): string[] {
  const words = text.split(' ');
  const lines: string[] = [];
  let current = '';

  for (const word of words) {
    if (current.length + word.length + 1 > maxWidth) {
      if (current) lines.push(current);
      current = word;
    } else {
      current = current ? `${current} ${word}` : word;
    }
  }
  if (current) lines.push(current);
  return lines;
}
