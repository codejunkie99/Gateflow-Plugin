# Phase 4: Interactive Refinement

## Goal
Detect conflicts between inspirations and generate clarifying questions. Apply user decisions to refine the taste profile.

**Depends on**: Phase 1 types only

## New file: `src/tasteRefine.ts` (~150 lines)

### Key functions

**`detectConflicts(inspirations)`** → `TasteConflict[]`
- Detect conflicts across inspirations
- Called by Phase 2's `buildTasteProfile`, but can also be called standalone

**`nextClarifyingQuestion(profile)`** → `{ conflict, question, options } | null`
- Generate the next clarifying question from unresolved conflicts
- Returns null if no conflicts remain

**`applyDecision(options)`** → `TasteDecision`
- Apply a user's answer to a conflict, creating a `TasteDecision`
- Marks the conflict as resolved
- Options: `{ rootDir, projectId, conflictIndex, answer }`

### Conflict detection rules

#### Color conflicts
- Group top-5 colors from each inspiration by source
- If top-3 colors from different sources have HSL distance > 40 → conflict
- Description: "Your inspirations show different dominant colors"
- Options: list each source's top color with source name

#### Typography conflicts
- Extract primary font (most frequent) from each inspiration
- If different inspirations use different primary fonts → conflict
- Description: "Different inspirations use different primary fonts"
- Options: list each font with source name

#### Spacing conflicts
- Detect base unit per inspiration (most common divisor: 4 or 8)
- If base units differ → conflict

#### Shape conflicts (border-radius)
- Extract most common border-radius from each inspiration's components
- If they cluster around different values (>2px difference) → conflict
- Description: "Your inspirations show different corner radiuses"
- Options: "8px (stripe.com)", "6px (linear.app)", "12px (vercel.com)"

#### Motion conflicts
- Extract dominant duration from each inspiration
- If durations differ significantly (>100ms) → conflict

### Question format
```
Your inspirations show different corner radiuses:
  1. 8px (from stripe.com) — rounded but restrained
  2. 6px (from linear.app) — tight, modern
  3. 12px (from vercel.com) — soft, approachable
Which do you prefer? [1/2/3/custom]:
```

## Existing functions to reuse

| Function | File |
|----------|------|
| `loadTasteProfile()`, `saveTasteProfile()` | `src/store.ts` |
| `makeId()`, `nowIso()` | `src/util.ts` |
| `confirmPrompt()` | `src/interactive.ts` |

## Verification

```bash
npm run build && npm test
```

## Status
- [ ] Pending
