#!/usr/bin/env node
import path from 'node:path';
import { Command } from 'commander';
import { loadTasteProfile } from './store.js';
import {
  askBrain,
  initBrain,
  ingestInspiration,
  recordOutcome,
  reindexBrain,
  searchBrain,
} from './commands.js';
import { applyDecision, nextClarifyingQuestion } from './tasteRefine.js';
import { buildTasteProfile } from './taste.js';
import { cherryPickComponent, scoreTaste } from './tasteDiff.js';
import { generateFromTaste } from './tasteGenerate.js';
import { renderTasteDiff, renderTasteProfile, renderTasteProfileCompact } from './tasteRenderer.js';
import { confirmPrompt, shouldSkipPrompts } from './interactive.js';
import { resolveLlmConfig } from './llm.js';
import { getDefaultSkillRepo, maybePromptSkillInstall } from './skillPrompt.js';
import { scanDesignSystem, scanFromUrl, looksLikeUrl, normalizeToUrl } from './scan.js';
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

function resolveTasteAnswer(answer: string, options: string[]): string {
  const trimmed = answer.trim();
  if (/^\d+$/.test(trimmed)) {
    const index = Number.parseInt(trimmed, 10) - 1;
    if (index >= 0 && index < options.length) {
      return options[index];
    }
  }
  return trimmed;
}

async function main(): Promise<void> {
  const program = new Command();

  program
    .name('design-brain-memory')
    .description('Relational markdown design memory powered by Agent Browser CLI')
    .version('0.9.0')
    .option('-y, --yes', 'Skip interactive prompts');

  /* ─── scan (default command) ─── */

  program
    .command('scan [path]')
    .description('Scan codebase for design tokens and compute health score')
    .action(async (scanPath?: string) => {
      const input = scanPath ?? process.cwd();

      let result;
      if (looksLikeUrl(input)) {
        const url = normalizeToUrl(input);
        result = await scanFromUrl(url);
      } else {
        result = await scanDesignSystem(path.resolve(input));
      }

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

  /* ─── taste ─── */

  const taste = program
    .command('taste')
    .description('Build, inspect, and apply taste profiles');

  taste
    .command('build <urls...>')
    .description('Build taste profile from one or more inspiration URLs')
    .option('--project <project>', 'Project ID/slug', 'default')
    .option('--name <name>', 'Readable project name')
    .option('--headed', 'Use visible browser scan for taste analysis', false)
    .option('--llm-base-url <url>', 'OpenAI-compatible LLM base URL')
    .option('--llm-api-key <key>', 'LLM API key')
    .option('--llm-model <model>', 'LLM model id')
    .option('--llm-timeout-ms <ms>', 'LLM timeout in milliseconds', '30000')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (urls: string[], options: {
      project: string;
      name?: string;
      headed: boolean;
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

      const profile = await buildTasteProfile({
        rootDir: path.resolve(options.root),
        projectId: options.project,
        projectName: options.name,
        urls,
        headed: options.headed,
        llm,
      });

      renderTasteProfile(profile);
    });

  taste
    .command('show')
    .description('Display saved taste profile for a project')
    .option('--project <project>', 'Project ID/slug', 'default')
    .option('--json', 'Output as JSON', false)
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      project: string;
      json: boolean;
      root: string;
    }) => {
      const profile = await loadTasteProfile(path.resolve(options.root), options.project);
      if (!profile) {
        throw new Error(`Taste profile not found for project: ${options.project}`);
      }

      if (options.json) {
        console.log(JSON.stringify(profile, null, 2));
        return;
      }

      renderTasteProfile(profile);
    });

  taste
    .command('pick')
    .description('Cherry-pick a component from an inspiration source')
    .requiredOption('--component <kind>', 'Component kind to pick')
    .requiredOption('--from <source>', 'Source inspiration ID, URL, or hostname')
    .option('--project <project>', 'Project ID/slug', 'default')
    .option('--index <n>', 'Pick Nth matched component', '0')
    .option('--note <text>', 'Optional note for why this was picked')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      component: string;
      from: string;
      project: string;
      index: string;
      note?: string;
      root: string;
    }) => {
      const pick = await cherryPickComponent({
        rootDir: path.resolve(options.root),
        projectId: options.project,
        componentKind: options.component,
        sourceUrlOrId: options.from,
        index: parseInteger(options.index, 0),
        note: options.note,
      });

      console.log(`Cherry-picked ${pick.componentKind} from ${pick.sourceUrl}`);
    });

  taste
    .command('score [scanPath]')
    .description('Score codebase alignment against a taste profile')
    .option('--project <project>', 'Project ID/slug', 'default')
    .option('--json', 'Output as JSON', false)
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (scanPath: string | undefined, options: {
      project: string;
      json: boolean;
      root: string;
    }) => {
      const result = await scoreTaste({
        rootDir: path.resolve(options.root),
        projectId: options.project,
        scanPath: scanPath ?? process.cwd(),
      });

      if (options.json) {
        console.log(JSON.stringify(result, null, 2));
        return;
      }

      renderTasteDiff(result.diff);
    });

  taste
    .command('ask')
    .description('Resolve unresolved taste conflicts')
    .option('--project <project>', 'Project ID/slug', 'default')
    .option('--answer <text>', 'Answer text or option number')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      project: string;
      answer?: string;
      root: string;
    }) => {
      const rootDir = path.resolve(options.root);
      const profile = await loadTasteProfile(rootDir, options.project);
      if (!profile) {
        throw new Error(`Taste profile not found for project: ${options.project}`);
      }

      const next = nextClarifyingQuestion(profile);
      if (!next) {
        console.log('No unresolved taste conflicts.');
        return;
      }

      const unresolvedIndex = profile.conflicts.findIndex((conflict) => !conflict.resolved);
      if (unresolvedIndex < 0) {
        console.log('No unresolved taste conflicts.');
        return;
      }

      let answer = options.answer ? resolveTasteAnswer(options.answer, next.options) : '';
      if (!answer) {
        console.log(next.question);
        for (let i = 0; i < next.options.length; i += 1) {
          const shouldUse = await confirmPrompt(`Use option ${i + 1}: ${next.options[i]}?`, false);
          if (shouldUse) {
            answer = next.options[i];
            break;
          }
        }
      }

      if (!answer) {
        console.log('No decision applied.');
        return;
      }

      const decision = await applyDecision({
        rootDir,
        projectId: options.project,
        conflictIndex: unresolvedIndex,
        answer,
      });

      console.log(`Saved decision ${decision.id}: ${decision.answer}`);
    });

  taste
    .command('generate')
    .description('Generate code from a taste profile')
    .option('--project <project>', 'Project ID/slug', 'default')
    .option('--target <target>', 'Generation target: component, page, or tokens', 'component')
    .option('--component <kind>', 'Component kind when target=component')
    .option('--framework <name>', 'Framework hint (react, next, vue, etc.)')
    .option('--llm-base-url <url>', 'OpenAI-compatible LLM base URL')
    .option('--llm-api-key <key>', 'LLM API key')
    .option('--llm-model <model>', 'LLM model id')
    .option('--llm-timeout-ms <ms>', 'LLM timeout in milliseconds', '30000')
    .option('--root <dir>', 'Workspace root', process.cwd())
    .action(async (options: {
      project: string;
      target: string;
      component?: string;
      framework?: string;
      llmBaseUrl?: string;
      llmApiKey?: string;
      llmModel?: string;
      llmTimeoutMs: string;
      root: string;
    }) => {
      const profile = await loadTasteProfile(path.resolve(options.root), options.project);
      if (!profile) {
        throw new Error(`Taste profile not found for project: ${options.project}`);
      }

      const target = options.target as 'component' | 'page' | 'tokens';
      if (!['component', 'page', 'tokens'].includes(target)) {
        throw new Error(`Invalid target: ${options.target}`);
      }

      const llm = target === 'tokens'
        ? undefined
        : resolveLlmConfig({
          baseUrl: options.llmBaseUrl,
          apiKey: options.llmApiKey,
          model: options.llmModel,
          timeoutMs: parseInteger(options.llmTimeoutMs, 30000),
        });

      const generated = await generateFromTaste({
        taste: profile,
        target,
        componentKind: options.component,
        framework: options.framework,
        llm,
      });

      console.log(generated.code);
      if (generated.explanation) {
        console.log(`\n${generated.explanation}`);
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
  // Bare URLs/domains route to `taste build`.
  // Bare local paths route to `scan`.
  // No args defaults to `scan`.

  const commandNames = program.commands.map((command) => command.name());
  const firstArg = process.argv[2];
  if (!firstArg) {
    process.argv.splice(2, 0, 'scan');
  } else if (!firstArg.startsWith('-') && !commandNames.includes(firstArg)) {
    if (looksLikeUrl(firstArg)) {
      process.argv.splice(2, 0, 'taste', 'build');
    } else {
      process.argv.splice(2, 0, 'scan');
    }
  }

  await program.parseAsync(process.argv);
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
