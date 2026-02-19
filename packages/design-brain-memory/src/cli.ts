#!/usr/bin/env node
import path from 'node:path';
import { Command } from 'commander';
import {
  askBrain,
  initBrain,
  ingestInspiration,
  recordOutcome,
  reindexBrain,
  searchBrain,
} from './commands.js';
import { shouldSkipPrompts } from './interactive.js';
import { resolveLlmConfig } from './llm.js';
import { getDefaultSkillRepo, maybePromptSkillInstall } from './skillPrompt.js';
import { scanDesignSystem } from './scan.js';
import { renderScanResults } from './scanRenderer.js';

function toStringList(value?: string | string[]): string[] {
  if (!value) {
    return [];
  }

  if (Array.isArray(value)) {
    return value.flatMap((item) => item.split(',')).map((item) => item.trim()).filter(Boolean);
  }

  return value.split(',').map((item) => item.trim()).filter(Boolean);
}

function parseInteger(value: string, defaultValue: number): number {
  const parsed = Number.parseInt(value, 10);
  return Number.isFinite(parsed) ? parsed : defaultValue;
}

function parseViewports(values?: string[]): Array<{ label: string; width: number; height: number }> | undefined {
  if (!values || values.length === 0) {
    return undefined;
  }

  const parsed = values
    .flatMap((value) => value.split(','))
    .map((item) => item.trim())
    .filter(Boolean)
    .map((item, index) => {
      const [label, size] = item.includes('=') ? item.split('=') : [`vp${index + 1}`, item];
      const [widthRaw, heightRaw] = size.split('x');
      const width = Number.parseInt(widthRaw, 10);
      const height = Number.parseInt(heightRaw, 10);
      if (!Number.isFinite(width) || !Number.isFinite(height)) {
        throw new Error(`Invalid viewport format: ${item}. Use label=1440x1200.`);
      }
      return { label: label.trim(), width, height };
    });

  return parsed.length > 0 ? parsed : undefined;
}

async function main(): Promise<void> {
  const program = new Command();

  program
    .name('design-brain-memory')
    .description('Relational markdown design memory powered by Agent Browser CLI')
    .version('0.2.0')
    .option('-y, --yes', 'Skip interactive prompts');

  /* ─── scan (default command) ─── */

  program
    .command('scan [path]')
    .description('Scan codebase for design tokens and compute health score')
    .action(async (scanPath?: string) => {
      const resolved = path.resolve(scanPath ?? process.cwd());
      const result = await scanDesignSystem(resolved);
      renderScanResults(result);

      const globalOptions = program.opts<{ yes?: boolean }>();
      await maybePromptSkillInstall(shouldSkipPrompts(Boolean(globalOptions.yes)));
    });

  /* ─── init ─── */

  program
    .command('init')
    .description('Initialize .design-brain in the given workspace')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: { root: string }) => {
      await initBrain(path.resolve(options.root));
      console.log(`Initialized design brain at ${path.resolve(options.root, '.design-brain')}`);
    });

  /* ─── ingest ─── */

  program
    .command('ingest')
    .description('Ingest a URL or screenshot into a project design wiki')
    .requiredOption('--project <project>', 'Project ID/slug')
    .option('--project-name <name>', 'Readable project name')
    .option('--project-description <text>', 'Project description shown in the wiki')
    .option('--url <url>', 'Website URL inspiration source')
    .option('--screenshot <path>', 'Local screenshot inspiration source')
    .option('--name <name>', 'Record name')
    .option('--notes <notes>', 'Freeform notes about why it matters')
    .option('--inspiration <text>', 'Summary of what this source inspired')
    .option('--tags <tags...>', 'Tags list (repeat or comma-separated)')
    .option('--journey-steps <n>', 'How many click-through journey steps to capture', '3')
    .option('--viewport <viewports...>', 'Responsive viewports: desktop=1440x1200,mobile=390x844')
    .option('--llm-base-url <url>', 'OpenAI-compatible LLM base URL')
    .option('--llm-api-key <key>', 'LLM API key')
    .option('--llm-model <model>', 'LLM model id')
    .option('--llm-timeout-ms <ms>', 'LLM timeout in milliseconds', '30000')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      project: string;
      projectName?: string;
      projectDescription?: string;
      url?: string;
      screenshot?: string;
      name?: string;
      notes?: string;
      inspiration?: string;
      tags?: string[];
      journeySteps: string;
      viewport?: string[];
      llmBaseUrl?: string;
      llmApiKey?: string;
      llmModel?: string;
      llmTimeoutMs: string;
      root: string;
    }) => {
      const llm = resolveLlmConfig({
        baseUrl: options.llmBaseUrl,
        apiKey: options.llmApiKey,
        model: options.llmModel,
        timeoutMs: parseInteger(options.llmTimeoutMs, 30000),
      });

      const result = await ingestInspiration({
        rootDir: path.resolve(options.root),
        project: options.project,
        projectName: options.projectName,
        projectDescription: options.projectDescription,
        url: options.url,
        screenshot: options.screenshot,
        name: options.name,
        notes: options.notes,
        inspirationSummary: options.inspiration,
        tags: toStringList(options.tags),
        llm,
        journeySteps: parseInteger(options.journeySteps, 3),
        responsiveViewports: parseViewports(options.viewport),
      });

      console.log(`Captured inspiration ${result.inspirationId} in project ${result.projectId}`);

      const globalOptions = program.opts<{ yes?: boolean }>();
      await maybePromptSkillInstall(shouldSkipPrompts(Boolean(globalOptions.yes)));
    });

  /* ─── outcome ─── */

  program
    .command('outcome')
    .description('Record what the team built and link it to inspirations')
    .requiredOption('--project <project>', 'Project ID/slug')
    .requiredOption('--title <title>', 'Outcome title')
    .requiredOption('--description <description>', 'Outcome description')
    .option('--artifact-url <url>', 'Deployed link, Figma link, or PR URL')
    .option('--inspired-by <ids...>', 'Linked inspiration IDs')
    .option('--tags <tags...>', 'Tags list (repeat or comma-separated)')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      project: string;
      title: string;
      description: string;
      artifactUrl?: string;
      inspiredBy?: string[];
      tags?: string[];
      root: string;
    }) => {
      const result = await recordOutcome({
        rootDir: path.resolve(options.root),
        project: options.project,
        title: options.title,
        description: options.description,
        inspiredBy: toStringList(options.inspiredBy),
        artifactUrl: options.artifactUrl,
        tags: toStringList(options.tags),
      });

      console.log(`Recorded outcome ${result.outcomeId} in project ${result.projectId}`);
    });

  /* ─── search ─── */

  program
    .command('search')
    .description('Keyword search over relational design memory')
    .requiredOption('--query <text>', 'Search query')
    .option('--project <project>', 'Filter to project')
    .option('--limit <n>', 'Max results', '10')
    .option('--json', 'Output as JSON', false)
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      query: string;
      project?: string;
      limit: string;
      json: boolean;
      root: string;
    }) => {
      const results = await searchBrain({
        rootDir: path.resolve(options.root),
        query: options.query,
        project: options.project,
        limit: parseInteger(options.limit, 10),
      });

      if (options.json) {
        console.log(JSON.stringify(results, null, 2));
        return;
      }

      if (results.length === 0) {
        console.log('No matches found.');
        return;
      }

      for (const result of results) {
        console.log(`[${result.type}] ${result.projectId}/${result.id} :: ${result.title} (score=${result.score})`);
        console.log(`  ${result.snippet}`);
      }
    });

  /* ─── ask ─── */

  program
    .command('ask')
    .description('Ask a design question against the design brain')
    .requiredOption('--query <text>', 'Question')
    .option('--project <project>', 'Filter to project')
    .option('--limit <n>', 'Context result count', '8')
    .option('--llm-base-url <url>', 'OpenAI-compatible LLM base URL')
    .option('--llm-api-key <key>', 'LLM API key')
    .option('--llm-model <model>', 'LLM model id')
    .option('--llm-timeout-ms <ms>', 'LLM timeout in milliseconds', '30000')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      query: string;
      project?: string;
      limit: string;
      llmBaseUrl?: string;
      llmApiKey?: string;
      llmModel?: string;
      llmTimeoutMs: string;
      root: string;
    }) => {
      const llm = resolveLlmConfig({
        baseUrl: options.llmBaseUrl,
        apiKey: options.llmApiKey,
        model: options.llmModel,
        timeoutMs: parseInteger(options.llmTimeoutMs, 30000),
      });

      const result = await askBrain({
        rootDir: path.resolve(options.root),
        query: options.query,
        project: options.project,
        limit: parseInteger(options.limit, 8),
        llm,
      });

      console.log(result.answer);
      if (result.matches.length > 0) {
        console.log('\nSources:');
        for (const match of result.matches.slice(0, 8)) {
          console.log(`- [${match.type}] ${match.projectId}/${match.id}: ${match.title}`);
        }
      }
    });

  /* ─── install-skill ─── */

  program
    .command('install-skill')
    .description('Install Design Brain skill into your AI agents')
    .action(async () => {
      await maybePromptSkillInstall(false);
    });

  /* ─── reindex ─── */

  program
    .command('reindex')
    .description('Regenerate markdown wiki and relation graph from database.json')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: { root: string }) => {
      await reindexBrain(path.resolve(options.root));
      console.log(`Reindexed ${path.resolve(options.root, '.design-brain')}`);
    });

  /* ─── Default command routing ─── */
  // When user runs `npx design-brain-memory` (no args), or
  // `npx design-brain-memory .` / `npx design-brain-memory ./src` (bare path),
  // route to the scan command.

  const commandNames = program.commands.map(c => c.name());
  const firstArg = process.argv[2];
  if (
    !firstArg ||
    (firstArg && !firstArg.startsWith('-') && !commandNames.includes(firstArg))
  ) {
    process.argv.splice(2, 0, 'scan');
  }

  await program.parseAsync(process.argv);
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
