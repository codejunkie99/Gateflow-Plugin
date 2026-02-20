# Phase 5: LLM Generation + Skill + CLI Wiring

## Goal
Generate design tokens/components from taste profile, update CLI with all taste commands, update skill.

**Depends on**: Phase 1 types + `runDesignLlm` from `llm.ts`

**CLI wiring** imports from Phases 2-4, so this should finalize AFTER 2-4 are done. The `tasteGenerate.ts` file itself has no Phase 2-4 dependencies.

## New file: `src/tasteGenerate.ts` (~200 lines)

### Key functions

**`generateDesignTokens(taste)`** → `string`
- Generate CSS custom properties from taste profile (no LLM needed, deterministic)

**`generateFromTaste(options)`** → `{ code, explanation }`
- Generate a component or page using LLM + taste profile as context
- Options: `{ taste, target, componentKind?, llm, framework? }`
- Target: `'component' | 'page' | 'tokens'`

### Token generation output (deterministic, no LLM)

```css
:root {
  /* Colors — from taste profile */
  --color-primary: #635BFF;
  --color-background: #0A2540;
  --color-accent: #5E6AD2;
  --color-text: #000000;
  --color-surface: #FFFFFF;

  /* Typography */
  --font-primary: 'Inter', sans-serif;
  --font-secondary: 'GT America', sans-serif;
  --text-sm: 14px;
  --text-base: 16px;
  --text-lg: 20px;
  --text-xl: 24px;
  --text-2xl: 32px;
  --text-3xl: 48px;

  /* Spacing */
  --space-1: 4px;
  --space-2: 8px;
  --space-3: 12px;
  --space-4: 16px;
  --space-6: 24px;
  --space-8: 32px;
  --space-12: 48px;
  --space-16: 64px;

  /* Motion */
  --duration-fast: 150ms;
  --duration-normal: 300ms;
  --easing-default: cubic-bezier(0.4, 0, 0.2, 1);

  /* Shape */
  --radius-default: 8px;
}
```

### LLM generation prompt template

```
You are a frontend developer. Generate production-ready {framework} code matching this taste profile.

Persona: {persona.name} — "{persona.tagline}"
Palette: {palette list}
Typography: Primary={primaryFont}, Secondary={secondaryFont}
Spacing: {baseUnit}px base, scale=[{scale}]
Motion: {intensity}, {durations}, {easing}
Shape: radius={borderRadius}, shadow={shadowStyle}
Principles: {principles list}

Cherry-picked references:
{for each cherry-pick: kind from source with key styles}

Generate: {target} {componentKind?}
Requirements: Use exact token values. Semantic HTML. Accessible.
Output: Single code block, then a 2-sentence explanation.
```

---

## CLI Wiring (modify `src/cli.ts`)

Add `taste` command group with subcommands:

### `taste build <urls...>`
- Build taste profile from one or more URLs
- Options: `--project`, `--name`, `--headed`, `--llm-base-url`, `--llm-api-key`, `--llm-model`
- Calls `buildTasteProfile()`

### `taste show`
- Display current profile
- Options: `--project`, `--json`
- Loads + renders taste profile

### `taste pick`
- Cherry-pick a component
- Required: `--component`, `--from`
- Options: `--project`, `--note`
- Calls `cherryPickComponent()`

### `taste score [path]`
- Score codebase against taste
- Options: `--project`
- Calls `scoreTaste()`

### `taste ask`
- Answer clarifying questions
- Options: `--project`, `--answer`
- Calls `nextClarifyingQuestion()` + `applyDecision()`

### `taste generate`
- Generate code from taste
- Options: `--project`, `--target`, `--component`, `--framework`, `--llm-*`
- Calls `generateFromTaste()`

### Default command routing
Bare `npx design-brain-memory stripe.com linear.app` should route to `taste build`.

---

## Skill update (`skills/design-brain/SKILL.md`)

Add section:

```markdown
## Taste Profile Context

Before generating UI code, check for a taste profile:
\`\`\`bash
cat .design-brain/taste/*.json 2>/dev/null
\`\`\`

If a taste profile exists, ALL generated UI code MUST use:
- Colors from the palette (exact hex values)
- The specified font families
- Spacing values from the scale
- Motion parameters (durations, easing)
- Cherry-picked component styles where applicable

Commands:
- `design-brain-memory taste show --project <id> --json` — get taste as JSON
- `design-brain-memory taste score . --project <id>` — check alignment
- `design-brain-memory taste generate --target tokens --project <id>` — emit CSS vars
```

## Verification

```bash
npm run build && npm test
# Full flow:
node dist/cli.js taste build stripe.com linear.app --project demo
node dist/cli.js taste show --project demo
node dist/cli.js taste score . --project demo
node dist/cli.js taste generate --target tokens --project demo
```

## Status
- [ ] Pending
