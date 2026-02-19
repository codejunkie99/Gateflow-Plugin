import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { join, dirname } from 'node:path';
import { confirmPrompt } from './interactive.js';
import type { AgentInfo, InstallResult } from './types.js';

/* ─── User config persistence ─── */

interface UserConfig {
  skillPromptDismissed?: boolean;
}

const CONFIG_DIRECTORY = join(homedir(), '.design-brain-memory');
const CONFIG_FILE = join(CONFIG_DIRECTORY, 'config.json');
const DEFAULT_SKILL_REPO = 'design-brain/design-brain';

function readConfig(): UserConfig {
  try {
    if (!existsSync(CONFIG_FILE)) return {};
    return JSON.parse(readFileSync(CONFIG_FILE, 'utf-8')) as UserConfig;
  } catch {
    return {};
  }
}

function writeConfig(config: UserConfig): void {
  try {
    if (!existsSync(CONFIG_DIRECTORY)) {
      mkdirSync(CONFIG_DIRECTORY, { recursive: true });
    }
    writeFileSync(CONFIG_FILE, JSON.stringify(config, null, 2));
  } catch {
    // no-op: config persistence should never block command execution
  }
}

/* ─── Backward-compatible export ─── */

export function getDefaultSkillRepo(): string {
  return process.env.DESIGN_BRAIN_SKILL_REPO?.trim() || DEFAULT_SKILL_REPO;
}

/* ─── SKILL.md content ─── */

function getSkillContent(): string {
  // Try to load from bundled skills/SKILL.md first
  const bundledPath = join(dirname(new URL(import.meta.url).pathname), '..', 'skills', 'SKILL.md');
  try {
    if (existsSync(bundledPath)) {
      return readFileSync(bundledPath, 'utf-8');
    }
  } catch {
    // fall through to inline content
  }

  // Inline fallback
  return `---
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

- Run \`npx design-brain-memory scan\` to see your design health score
- Run \`npx design-brain-memory scan .\` to scan the current directory
- Design tokens are extracted from CSS, SCSS, and component files

## Tips for Code Generation

- Prefer CSS custom properties (--var-name) over hardcoded values
- Use the project's existing color palette — don't introduce new colors without reason
- Match existing component patterns before creating new abstractions
- Keep transition durations consistent (prefer 150ms, 200ms, or 300ms)
`;
}

/* ─── Agent detection ─── */

const AGENT_DEFS: Array<{ name: string; configCheck: string; skillSubpath: string }> = [
  {
    name: 'Claude Code',
    configCheck: join(homedir(), '.claude'),
    skillSubpath: join('.claude', 'skills', 'design-brain', 'SKILL.md'),
  },
  {
    name: 'Cursor',
    configCheck: join(homedir(), '.cursor'),
    skillSubpath: join('.cursor', 'skills', 'design-brain', 'SKILL.md'),
  },
  {
    name: 'Windsurf',
    configCheck: join(homedir(), '.codeium', 'windsurf'),
    skillSubpath: join('.codeium', 'windsurf', 'skills', 'design-brain', 'SKILL.md'),
  },
  {
    name: 'Amp',
    configCheck: join(homedir(), '.amp'),
    skillSubpath: join('.amp', 'skills', 'design-brain', 'SKILL.md'),
  },
  {
    name: 'Codex',
    configCheck: join(homedir(), '.codex'),
    skillSubpath: join('.codex', 'skills', 'design-brain', 'SKILL.md'),
  },
];

export function detectAgents(): AgentInfo[] {
  const agents: AgentInfo[] = [];
  for (const def of AGENT_DEFS) {
    if (existsSync(def.configCheck)) {
      agents.push({
        name: def.name,
        configDir: def.configCheck,
        skillDir: join(homedir(), def.skillSubpath),
      });
    }
  }
  return agents;
}

export function installSkillToAgents(agents: AgentInfo[]): InstallResult[] {
  const content = getSkillContent();
  const results: InstallResult[] = [];

  for (const agent of agents) {
    try {
      const dir = dirname(agent.skillDir);
      if (!existsSync(dir)) {
        mkdirSync(dir, { recursive: true });
      }
      writeFileSync(agent.skillDir, content, 'utf-8');
      results.push({ agent, success: true });
    } catch (err) {
      results.push({
        agent,
        success: false,
        error: err instanceof Error ? err.message : String(err),
      });
    }
  }

  return results;
}

/* ─── ANSI helpers ─── */

const USE_COLOR = process.stdout.isTTY !== false;
const RESET = USE_COLOR ? '\x1b[0m' : '';
const BOLD  = USE_COLOR ? '\x1b[1m' : '';
const GREEN = USE_COLOR ? '\x1b[32m' : '';
const DIM   = USE_COLOR ? '\x1b[2m' : '';
const RED   = USE_COLOR ? '\x1b[31m' : '';

/* ─── Main prompt flow ─── */

export async function maybePromptSkillInstall(skipPrompts: boolean): Promise<void> {
  const config = readConfig();
  if (config.skillPromptDismissed) return;
  if (skipPrompts) return;

  const agents = detectAgents();
  if (agents.length === 0) {
    console.log(`\n${DIM}No AI agents detected. Skill installation skipped.${RESET}`);
    return;
  }

  console.log(`\n  ${BOLD}Detected AI agents:${RESET}`);
  for (const agent of agents) {
    console.log(`    ${DIM}\u2022${RESET} ${agent.name}`);
  }
  console.log('');

  const shouldInstall = await confirmPrompt(
    `Install design-brain skill to ${agents.length} agent${agents.length > 1 ? 's' : ''}?`,
    true,
  );

  if (!shouldInstall) {
    writeConfig({ ...config, skillPromptDismissed: true });
    return;
  }

  const results = installSkillToAgents(agents);

  console.log('');
  for (const r of results) {
    if (r.success) {
      console.log(`  ${GREEN}\u2714${RESET} ${r.agent.name}`);
    } else {
      console.log(`  ${RED}\u2718${RESET} ${r.agent.name} — ${r.error}`);
    }
  }

  const allOk = results.every(r => r.success);
  if (allOk) {
    console.log(`\n  ${GREEN}Design Brain skill installed to all agents.${RESET}\n`);
  }

  writeConfig({ ...config, skillPromptDismissed: true });
}
