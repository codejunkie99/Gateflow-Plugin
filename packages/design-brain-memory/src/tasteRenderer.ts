import type { TasteDiffResult, TasteProfile } from './types.js';

const USE_COLOR = process.stdout.isTTY !== false;
const RESET = USE_COLOR ? '\x1b[0m' : '';
const DIM = USE_COLOR ? '\x1b[2m' : '';
const BOLD = USE_COLOR ? '\x1b[1m' : '';
const GREEN = USE_COLOR ? '\x1b[32m' : '';
const YELLOW = USE_COLOR ? '\x1b[33m' : '';
const CYAN = USE_COLOR ? '\x1b[36m' : '';
const RED = USE_COLOR ? '\x1b[31m' : '';

const BOX_WIDTH = 58;

function topBorder(title: string): string {
  const label = `─ ${title} `;
  const rest = '─'.repeat(Math.max(0, BOX_WIDTH - label.length - 1));
  return `  ${DIM}┌${label}${rest}┐${RESET}`;
}

function bottomBorder(): string {
  return `  ${DIM}└${'─'.repeat(BOX_WIDTH)}┘${RESET}`;
}

function boxLine(content: string, rawLength: number): string {
  const pad = Math.max(0, BOX_WIDTH - rawLength);
  return `  ${DIM}│${RESET} ${content}${' '.repeat(Math.max(0, pad - 1))}${DIM}│${RESET}`;
}

function emptyLine(): string {
  return `  ${DIM}│${' '.repeat(BOX_WIDTH)}│${RESET}`;
}

function truncate(value: string, max = 52): string {
  if (value.length <= max) {
    return value;
  }
  return `${value.slice(0, max - 1)}…`;
}

function alignmentBar(value: number): string {
  const width = 16;
  const filled = Math.round((value / 100) * width);
  const empty = width - filled;
  return `${GREEN}${'█'.repeat(filled)}${RESET}${DIM}${'░'.repeat(empty)}${RESET}`;
}

function scoreColor(value: number): string {
  if (value >= 80) {
    return GREEN;
  }
  if (value >= 60) {
    return YELLOW;
  }
  return RED;
}

export function renderTasteProfileCompact(profile: TasteProfile): string {
  return `${profile.name} • ${profile.sourceInspirationIds.length} sources • ${profile.persona.name} • ${profile.aggregateScore.total}/100`;
}

export function renderTasteProfile(profile: TasteProfile): void {
  console.log('');
  console.log(topBorder('Taste Profile'));
  console.log(emptyLine());
  const title = `${BOLD}${CYAN}design-brain${RESET}  Taste Engine`;
  console.log(boxLine(title, 'design-brain  Taste Engine'.length));
  console.log(boxLine(`${DIM}Project: ${profile.name} (${profile.sourceInspirationIds.length} sources)${RESET}`, `Project: ${profile.name} (${profile.sourceInspirationIds.length} sources)`.length));
  console.log(emptyLine());
  console.log(bottomBorder());

  console.log('');
  console.log(`  ${GREEN}✔${RESET} Persona: ${BOLD}${profile.persona.name}${RESET} — "${profile.persona.tagline}"`);
  console.log(`  ${GREEN}✔${RESET} Aggregate score: ${BOLD}${profile.aggregateScore.total}/100${RESET}`);
  if (profile.conflicts.some((conflict) => !conflict.resolved)) {
    const unresolved = profile.conflicts.filter((conflict) => !conflict.resolved).length;
    console.log(`  ${YELLOW}⚠${RESET} ${unresolved} conflicts detected. Run: taste ask --project ${profile.id}`);
  }

  console.log('');
  console.log(topBorder('Color Palette'));
  for (const color of profile.color.palette.slice(0, 8)) {
    const line = `${color.hex}  ${color.role} (${color.source})`;
    console.log(boxLine(line, line.length));
  }
  const harmonyLine = `Harmony: ${profile.color.harmony} · ${profile.color.saturationBias} · ${profile.color.lightnessBias}`;
  console.log(emptyLine());
  console.log(boxLine(harmonyLine, harmonyLine.length));
  console.log(bottomBorder());

  console.log('');
  console.log(topBorder('Typography'));
  const primaryLine = `Primary: ${profile.typography.primaryFont}`;
  const secondaryLine = `Secondary: ${profile.typography.secondaryFont ?? 'none'}`;
  const scaleLine = `Scale: ${profile.typography.sizes.slice(0, 8).join(', ')}`;
  console.log(boxLine(primaryLine, primaryLine.length));
  console.log(boxLine(secondaryLine, secondaryLine.length));
  console.log(boxLine(truncate(scaleLine), truncate(scaleLine).length));
  console.log(bottomBorder());

  console.log('');
  console.log(topBorder('Spacing'));
  const spacingLine = `Base: ${profile.spacing.baseUnit}px grid · ${Math.round(profile.spacing.gridAlignmentRatio * 100)}% aligned`;
  const spacingScale = `Scale: ${profile.spacing.scale.join(' ')}`;
  console.log(boxLine(spacingLine, spacingLine.length));
  console.log(boxLine(truncate(spacingScale), truncate(spacingScale).length));
  console.log(bottomBorder());

  console.log('');
  console.log(topBorder('Motion'));
  const intensityLine = `Intensity: ${profile.motion.intensity}`;
  const durationsLine = `Durations: ${profile.motion.durations.join(', ')}`;
  const easingLine = `Easing: ${profile.motion.easing}`;
  console.log(boxLine(intensityLine, intensityLine.length));
  console.log(boxLine(truncate(durationsLine), truncate(durationsLine).length));
  console.log(boxLine(truncate(easingLine), truncate(easingLine).length));
  console.log(bottomBorder());

  if (profile.narrative) {
    console.log('');
    console.log(`  ${DIM}${profile.narrative}${RESET}`);
  }
}

export function renderTasteDiff(diff: TasteDiffResult): void {
  console.log('');
  console.log(topBorder('Taste Alignment'));
  console.log(emptyLine());

  const entries: Array<[string, number]> = [
    ['Color', diff.dimensions.color.alignment],
    ['Typography', diff.dimensions.typography.alignment],
    ['Spacing', diff.dimensions.spacing.alignment],
    ['Motion', diff.dimensions.motion.alignment],
  ];

  for (const [label, score] of entries) {
    const line = `${label.padEnd(12)} ${alignmentBar(score)}  ${BOLD}${scoreColor(score)}${String(score).padStart(3)}${RESET}`;
    const raw = `${label.padEnd(12)} ${'█'.repeat(16)}  ${String(score).padStart(3)}`;
    console.log(boxLine(line, raw.length));
  }

  console.log(emptyLine());
  const totalLine = `${BOLD}Overall${RESET}`.padEnd(13) + ` ${alignmentBar(diff.alignment)}  ${BOLD}${scoreColor(diff.alignment)}${String(diff.alignment).padStart(3)}${RESET}`;
  const totalRaw = `Overall      ${'█'.repeat(16)}  ${String(diff.alignment).padStart(3)}`;
  console.log(boxLine(totalLine, totalRaw.length));
  console.log(emptyLine());
  console.log(bottomBorder());

  if (diff.deltas.length > 0) {
    console.log('\nDeltas:');
    for (const delta of diff.deltas.slice(0, 8)) {
      console.log(`  ${delta.severity === 'mismatch' ? '⚠' : '•'} ${delta.issue} → ${delta.suggestion}`);
    }
  }
}
