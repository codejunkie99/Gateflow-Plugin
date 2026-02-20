---
name: design-brain
description: Build and query a relational markdown design memory using design-brain-memory and Agent Browser CLI.
version: 1.0.0
---

# Design Brain

Capture inspiration from websites/screenshots and turn it into a searchable design memory.

## Install

```bash
design-brain-memory install-skill
```

or

```bash
npx -y skills add design-brain/design-brain
```

## Workflow

1. Initialize:

```bash
design-brain-memory init --root <workspace>
```

2. Ingest inspiration:

```bash
design-brain-memory ingest --project <id> --url <url> --name "<name>" --tags <tags>
```

or

```bash
design-brain-memory ingest --project <id> --screenshot <path> --name "<name>" --tags <tags>
```

3. Record outcome:

```bash
design-brain-memory outcome --project <id> --title "<title>" --description "<what was built>" --inspired-by <inspiration-id>
```

4. Query:

```bash
design-brain-memory search --query "<keywords>"
```

```bash
design-brain-memory ask --query "<question>" --llm-base-url <url> --llm-api-key <key> --llm-model <model>
```

## Taste Profile Context

Before generating UI code, check for a taste profile:

```bash
cat .design-brain/taste/*.json 2>/dev/null
```

If a taste profile exists, all generated UI code should use:
- Colors from the palette (exact hex values)
- The specified font families
- Spacing values from the scale
- Motion parameters (durations, easing)
- Cherry-picked component styles where applicable

Commands:
- `design-brain-memory taste show --project <id> --json` to read taste JSON
- `design-brain-memory taste score . --project <id>` to check alignment
- `design-brain-memory taste generate --target tokens --project <id>` to emit CSS variables
