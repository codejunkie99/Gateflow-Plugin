# Phase 3: Cherry-Picking + Taste Diff

## Goal
Score a codebase against a taste profile, and cherry-pick specific components from inspirations.

**Depends on**: Phase 1 types only (reads TasteProfile from disk, doesn't import from Phase 2)

## New file: `src/tasteDiff.ts` (~200 lines)

### Key functions

**`computeTasteDiff(codebaseTokens, taste)`** → `TasteDiffResult`
- Compare codebase `ScanTokens` against a `TasteProfile`
- Returns alignment score (0-100) and actionable deltas

**`scoreTaste(options)`** → `{ scanResult, diff }`
- Combines `scanDesignSystem` + `computeTasteDiff`
- Options: `{ rootDir, projectId, scanPath }`

**`cherryPickComponent(options)`** → `ComponentCherryPick`
- Cherry-pick a component from an inspiration
- Options: `{ rootDir, projectId, componentKind, sourceUrlOrId, index?, note? }`

**`colorDistance(hex1, hex2)`** → `number` (private)
- Simplified HSL delta for taste matching

**`closestTasteColor(hex, palette)`** → `{ hex, distance }` (private)
- Find closest taste palette color for a given hex

### Diff algorithm details

#### Color alignment (0-100)
- For each codebase color, find closest taste palette color via HSL distance
- Colors within distance < 15 = aligned, 15-30 = close, >30 = mismatch
- Score = (aligned + close*0.5) / total * 100
- Deltas: list mismatched colors with closest suggestion

#### Typography alignment (0-100)
- Check if codebase fonts ∈ {primaryFont, secondaryFont} → 100 per match
- Extra fonts penalized: -20 per extra font family
- Size alignment: check if codebase sizes ∈ taste scale → bonus

#### Spacing alignment (0-100)
- Parse codebase spacing values to px
- Check each against taste `spacing.scale` (allow ±2px tolerance)
- Score = % of values on-scale

#### Motion alignment (0-100)
- Duration match: codebase durations ∈ taste durations → 50 points
- Easing match: check if codebase uses similar easing → 30 points
- Intensity match: motion count matches intensity level → 20 points

### Cherry-pick resolution chain for `sourceUrlOrId`
1. Exact match on `InspirationRecord.id`
2. Exact match on `InspirationRecord.url`
3. Hostname match (extract domain, find inspiration with same domain)

### TUI rendering (add to `src/tasteRenderer.ts`)

**`renderTasteDiff(diff)`** — Renders alignment bars and deltas:

```
  ┌─ Taste Alignment ────────────────────────────┐
  │                                                │
  │  Color           ████████████░░░░  78          │
  │  Typography      ████████████████  100         │
  │  Spacing         ██████████░░░░░░  65          │
  │  Motion          ████████░░░░░░░░  50          │
  │                                                │
  │  Overall         ████████████░░░░  73          │
  └────────────────────────────────────────────────┘

  Deltas:
  ⚠ Color #FF5733 not in taste palette → closest: #635BFF
  ⚠ Font "Roboto" not in taste → expected: Inter, GT America
  ✔ Spacing 92% on taste grid
```

## Existing functions to reuse

| Function | File |
|----------|------|
| `scanDesignSystem()` | `src/scan.ts` |
| `loadTasteProfile()` | `src/store.ts` |
| `loadDatabase()`, `findProject()` | `src/store.ts` |

## Verification

```bash
npm run build && npm test
# Manual: node dist/cli.js taste score . --project demo
```

## Status
- [ ] Pending
