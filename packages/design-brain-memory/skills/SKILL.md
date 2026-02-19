---
name: design-brain
description: Design system awareness for AI coding agents. Provides design token guidance, component patterns, and design principles extracted from your codebase.
---

# Design Brain Skill

You have access to design system knowledge extracted by design-brain-memory.

## When to Use This Skill

- When writing UI components, reference the color palette and typography system
- When adding spacing/layout, follow the established spacing scale
- When creating new components, follow existing component patterns
- When adding transitions/animations, match existing motion patterns

## Design Principles

1. **Consistency** — Use existing design tokens rather than ad-hoc values
2. **Systematic spacing** — Prefer multiples of 4px (4, 8, 12, 16, 24, 32, 48, 64)
3. **Color discipline** — Use palette colors from CSS variables or design tokens
4. **Typography scale** — Stick to the established font size scale
5. **Motion restraint** — Use consistent transition timing across the UI

## Quick Reference

- Run `npx design-brain-memory scan` to see your design health score
- Run `npx design-brain-memory scan .` to scan the current directory
- Design tokens are extracted from CSS, SCSS, and component files

## Tips for Code Generation

- Prefer CSS custom properties (--var-name) over hardcoded values
- Use the project's existing color palette — don't introduce new colors without reason
- Match existing component patterns before creating new abstractions
- Keep transition durations consistent (prefer 150ms, 200ms, or 300ms)
