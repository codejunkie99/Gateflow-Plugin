# Phase 1: Foundation (MUST go first)

## Goal
Add all shared types to `types.ts`, add taste storage to `store.ts`, export `runCompletion` wrapper from `llm.ts`, export aggregation functions from `render.ts`.

## Files to modify

### `src/types.ts` — Append all taste profile types (~90 lines)

```typescript
/* ─── Taste Profile types ─── */

export interface TasteColorPreference {
  palette: Array<{ hex: string; role: string; source: string }>;
  harmony: string;              // "monochromatic" | "complementary" | "analogous" | "triadic"
  hueRange: { min: number; max: number };
  saturationBias: 'muted' | 'vibrant' | 'neutral';
  lightnessBias: 'light' | 'dark' | 'balanced';
}

export interface TasteTypographyPreference {
  primaryFont: string;
  secondaryFont: string | null;
  scaleType: string;            // "modular" | "custom" | "tailwind-default"
  sizes: string[];
  weightRange: { min: string; max: string };
}

export interface TasteSpacingPreference {
  baseUnit: number;             // 4 or 8
  scale: number[];              // e.g. [4, 8, 12, 16, 24, 32, 48, 64]
  gridAlignmentRatio: number;
}

export interface TasteMotionPreference {
  easing: string;
  durations: string[];
  intensity: 'none' | 'subtle' | 'moderate' | 'expressive';
}

export interface TasteComponentPreference {
  cherryPicks: ComponentCherryPick[];
  borderRadius: string;
  shadowStyle: 'none' | 'subtle' | 'elevated' | 'dramatic';
}

export interface ComponentCherryPick {
  componentKind: string;
  sourceInspirationId: string;
  sourceUrl: string;
  tokens: ComponentToken[];
  styles: Record<string, string>;
  note?: string;
}

export interface TasteDecision {
  id: string;
  question: string;
  answer: string;
  dimension: 'color' | 'typography' | 'spacing' | 'motion' | 'component' | 'layout' | 'general';
  decidedAt: string;
}

export interface TasteConflict {
  dimension: string;
  description: string;
  options: string[];
  resolved: boolean;
  resolvedByDecisionId?: string;
}

export interface TasteProfile {
  id: string;
  name: string;
  version: number;
  sourceInspirationIds: string[];
  sourceUrls: string[];
  persona: PersonaMatch;
  aggregateScore: ScanScore;
  color: TasteColorPreference;
  typography: TasteTypographyPreference;
  spacing: TasteSpacingPreference;
  motion: TasteMotionPreference;
  components: TasteComponentPreference;
  decisions: TasteDecision[];
  conflicts: TasteConflict[];
  narrative?: string;
  principles?: string[];
  createdAt: string;
  updatedAt: string;
}

export interface TasteDiffResult {
  alignment: number;            // 0-100
  dimensions: {
    color: TasteDimensionDiff;
    typography: TasteDimensionDiff;
    spacing: TasteDimensionDiff;
    motion: TasteDimensionDiff;
  };
  deltas: TasteDelta[];
}

export interface TasteDimensionDiff {
  alignment: number;
  summary: string;
}

export interface TasteDelta {
  dimension: string;
  issue: string;
  suggestion: string;
  severity: 'info' | 'warning' | 'mismatch';
}
```

### `src/store.ts` — Add taste profile storage (+25 lines)

```typescript
export function tasteDir(rootDir: string): string {
  return path.join(brainRoot(rootDir), 'taste');
}

export function tasteProfilePath(rootDir: string, projectId: string): string {
  return path.join(tasteDir(rootDir), `${projectId}.json`);
}

export async function loadTasteProfile(rootDir: string, projectId: string): Promise<TasteProfile | null> {
  const filePath = tasteProfilePath(rootDir, projectId);
  if (!await fs.pathExists(filePath)) return null;
  return fs.readJson(filePath);
}

export async function saveTasteProfile(rootDir: string, profile: TasteProfile): Promise<void> {
  const dir = tasteDir(rootDir);
  await fs.ensureDir(dir);
  await fs.writeJson(tasteProfilePath(rootDir, profile.id), profile, { spaces: 2 });
}
```

### `src/llm.ts` — Export `runDesignLlm` wrapper (+8 lines)

```typescript
export async function runDesignLlm(params: {
  llm: LlmConfig;
  system: string;
  userContent: string;
  temperature?: number;
}): Promise<string> {
  return runCompletion(params);
}
```

### `src/render.ts` — Export aggregation functions (+4 lines)

Add `export` keyword to each function definition:
- `aggregateColors`
- `aggregateTypography`
- `aggregateComponents`
- `aggregateMotion`

### `src/index.ts` — Add taste exports (+10 lines)

```typescript
export { loadTasteProfile, saveTasteProfile } from './store.js';
export type { TasteProfile, TasteDiffResult, ComponentCherryPick, TasteDecision, TasteConflict } from './types.js';
```

## Verification

```bash
cd packages/design-brain-memory && npm run build && npm test
```

## Status
- [ ] Pending
