# Phase 2: Taste Builder Core

## Goal
Create `buildTasteProfile()` — aggregates multiple inspirations into a TasteProfile.

**Depends on**: Phase 1 types + exported aggregation functions from `render.ts`

## New files

### `src/taste.ts` (~250 lines)

```typescript
import { aggregateColors, aggregateTypography, aggregateComponents, aggregateMotion } from './render.js';
import { designAnalysisToScanTokens } from './scan.js';
import { assignPersona } from './persona.js';
import { loadDatabase, ensureProject, saveTasteProfile, loadTasteProfile } from './store.js';
import { theatricalScan } from './theatrical.js';
import { looksLikeUrl, normalizeToUrl } from './scan.js';
import type { TasteProfile, InspirationRecord, DesignAnalysis, ... } from './types.js';
```

#### Key functions

**`buildTasteProfile(options)`** — Build or update a taste profile from multiple URL/inspiration sources.

Options:
```typescript
{
  rootDir: string;
  projectId: string;
  projectName?: string;
  urls: string[];
  headed?: boolean;
  llm?: LlmConfig;
}
```

Returns: `Promise<TasteProfile>`

#### Algorithm for `buildTasteProfile`:
1. For each URL: call `theatricalScan(url)` (or headless variant) → get `DesignAnalysis`
2. Also `ingestInspiration()` for each → store in the project (reuse existing pipeline)
3. Load all project inspirations from database
4. Call `aggregateColors()`, `aggregateTypography()`, `aggregateComponents()`, `aggregateMotion()` on all inspirations
5. Run each `derive*Preference()` function
6. Build `ScanTokens` from aggregated data → `computeScore()` → `assignPersona()`
7. Detect conflicts (see Phase 4 interface)
8. If LLM available: generate narrative + principles
9. Save TasteProfile
10. Return it

#### Headless vs Headed
- Default: use `captureDesignFromUrl()` from `extractFromUrl.ts` (headless, fast)
- With `--headed`: use `theatricalScan()` from `theatrical.ts` (visible browser)
- Both produce `DesignAnalysis` — same downstream pipeline

#### Private derive functions

**`deriveColorPreference(colors, inspirations)`** → `TasteColorPreference`
- Determines harmony type, hue range, saturation/lightness bias

**`deriveTypographyPreference(typography)`** → `TasteTypographyPreference`
- Picks primary/secondary font by frequency, detects scale type

**`deriveSpacingPreference(components)`** → `TasteSpacingPreference`
- Detects base unit (4 or 8), builds scale, computes grid alignment

**`deriveMotionPreference(motion)`** → `TasteMotionPreference`
- Picks dominant easing/durations, classifies intensity

**`deriveComponentPreference(components)`** → `TasteComponentPreference`
- Derives border-radius, shadow style from component tokens

---

### `src/tasteRenderer.ts` (~200 lines)

TUI rendering for taste profiles (ANSI boxes like `scanRenderer.ts`).

#### Functions

**`renderTasteProfile(profile)`** — Full taste card output
**`renderTasteProfileCompact(profile)`** — One-line summary

#### Output format

```
  ┌─ Taste Profile ──────────────────────────────┐
  │                                                │
  │  design-brain  Taste Engine                    │
  │  Project: my-app (3 sources)                   │
  │                                                │
  └────────────────────────────────────────────────┘

  ✔ Analyzed stripe.com, linear.app, vercel.com
  ✔ Persona: Jony Ive — "Less, but better"
  ✔ Aggregate score: 78/100

  ┌─ Color Palette ──────────────────────────────┐
  │  ■ #635BFF  primary (stripe.com)              │
  │  ■ #0A2540  background (stripe.com)           │
  │  ■ #5E6AD2  accent (linear.app)               │
  │  ■ #000000  text (vercel.com)                  │
  │  ■ #FFFFFF  surface (all)                      │
  │                                                │
  │  Harmony: analogous · Vibrant · Dark           │
  └────────────────────────────────────────────────┘

  ┌─ Typography ─────────────────────────────────┐
  │  Primary: Inter                                │
  │  Secondary: GT America                         │
  │  Scale: 14px, 16px, 20px, 24px, 32px, 48px   │
  └────────────────────────────────────────────────┘

  ┌─ Spacing ────────────────────────────────────┐
  │  Base: 8px grid · 94% aligned                  │
  │  Scale: 4 8 12 16 24 32 48 64                  │
  └────────────────────────────────────────────────┘

  ┌─ Motion ─────────────────────────────────────┐
  │  Intensity: subtle                             │
  │  Durations: 150ms, 300ms                       │
  │  Easing: cubic-bezier(0.4, 0, 0.2, 1)         │
  └────────────────────────────────────────────────┘

  ⚠ 2 conflicts detected. Run: taste ask --project my-app
```

## Existing functions to reuse (DO NOT reimplement)

| Function | File |
|----------|------|
| `theatricalScan()` | `src/theatrical.ts` |
| `captureDesignFromUrl()` | `src/extractFromUrl.ts` |
| `ingestInspiration()` | `src/commands.ts` |
| `designAnalysisToScanTokens()` | `src/scan.ts` |
| `computeScore()` | `src/scan.ts` |
| `assignPersona()` | `src/persona.ts` |
| `aggregateColors()` | `src/render.ts` |
| `aggregateTypography()` | `src/render.ts` |
| `aggregateComponents()` | `src/render.ts` |
| `aggregateMotion()` | `src/render.ts` |
| `enrichWithLlm()` | `src/llm.ts` |
| `makeId()`, `nowIso()`, `slugify()` | `src/util.ts` |
| `loadDatabase()`, `findProject()` | `src/store.ts` |

## Verification

```bash
npm run build && npm test
# Manual: node dist/cli.js taste stripe.com --project demo
```

## Status
- [ ] Pending
