import path from 'node:path';
import fs from 'fs-extra';
import { captureDesignFromImage } from './extractFromImage.js';
import { captureDesignFromUrl } from './extractFromUrl.js';
import { enrichWithLlm } from './llm.js';
import { askDesignBrain, searchDesignBrain } from './query.js';
import { renderAll } from './render.js';
import {
  ensureBrainExists,
  ensureProject,
  loadDatabase,
  projectAssetDir,
  saveDatabase,
} from './store.js';
import { makeId, normalizeUrl, nowIso, slugify, stableHash, unique } from './util.js';
import type {
  DesignAnalysis,
  IngestOptions,
  InspirationDiff,
  InspirationRecord,
  LlmConfig,
  OutcomeOptions,
} from './types.js';

function computeFingerprint(input: {
  url?: string;
  analysis: DesignAnalysis;
}): string {
  const basis = {
    url: input.url ? normalizeUrl(input.url) : null,
    topColors: input.analysis.colors.slice(0, 20).map((color) => color.hex.toUpperCase()),
    componentKinds: input.analysis.components.slice(0, 40).map((component) => component.kind),
    layout: input.analysis.layout.slice(0, 20).map((layout) => `${layout.tag}:${layout.role}`),
    motion: input.analysis.motion.slice(0, 20).map((m) => {
      if ('library' in m && 'motionIntent' in m) {
        return `${(m as { library: string }).library}|${(m as { motionIntent: string }).motionIntent}|${m.selector}`;
      }
      return `${(m as { transition: string }).transition}|${(m as { animation: string }).animation}`;
    }),
  };

  return stableHash(JSON.stringify(basis));
}

function buildDiff(previous: InspirationRecord, next: DesignAnalysis): InspirationDiff {
  const previousColors = new Set(previous.analysis.colors.map((color) => color.hex.toUpperCase()));
  const nextColors = new Set(next.colors.map((color) => color.hex.toUpperCase()));

  const addedColors = [...nextColors].filter((color) => !previousColors.has(color)).slice(0, 30);
  const removedColors = [...previousColors].filter((color) => !nextColors.has(color)).slice(0, 30);

  return {
    previousId: previous.id,
    addedColors,
    removedColors,
    componentCountDelta: next.components.length - previous.analysis.components.length,
    motionCountDelta: next.motion.length - previous.analysis.motion.length,
  };
}

function resolvePreviousVersion(projectInspirations: InspirationRecord[], fingerprint: string): InspirationRecord | undefined {
  const versions = projectInspirations
    .filter((entry) => entry.fingerprint === fingerprint)
    .sort((a, b) => a.capturedAt.localeCompare(b.capturedAt));

  return versions.at(-1);
}

function mergeTags(...lists: string[][]): string[] {
  return unique(
    lists
      .flat()
      .map((tag) => slugify(tag))
      .filter((tag) => tag.length > 0)
  );
}

export async function initBrain(rootDir: string): Promise<void> {
  await ensureBrainExists(rootDir);
  const db = await loadDatabase(rootDir);
  await renderAll(rootDir, db);
}

export async function ingestInspiration(options: IngestOptions): Promise<{ projectId: string; inspirationId: string }> {
  if (!options.url && !options.screenshot) {
    throw new Error('Provide either --url or --screenshot');
  }

  if (options.url && options.screenshot) {
    throw new Error('Use either --url or --screenshot, not both');
  }

  await ensureBrainExists(options.rootDir);
  const db = await loadDatabase(options.rootDir);
  const project = ensureProject(db, {
    projectId: options.project,
    projectName: options.projectName,
    description: options.projectDescription,
  });

  const inspirationName = options.name?.trim() || options.url || options.screenshot || 'inspiration';
  const inspirationId = makeId('inspo', inspirationName);
  const assetDir = projectAssetDir(options.rootDir, project.id);
  await fs.ensureDir(assetDir);

  let screenshotPath: string | undefined;
  let analysis: DesignAnalysis;

  if (options.url) {
    screenshotPath = path.join(assetDir, `${inspirationId}.png`);
    const sessionName = `designbrain-${project.id}-${Date.now().toString(36)}`;
    analysis = await captureDesignFromUrl({
      url: options.url,
      sessionName,
      screenshotPath,
      workingDir: options.rootDir,
      journeySteps: options.journeySteps,
      responsiveViewports: options.responsiveViewports,
    });
  } else {
    const source = path.resolve(options.rootDir, options.screenshot as string);
    const ext = path.extname(source) || '.png';
    screenshotPath = path.join(assetDir, `${inspirationId}${ext}`);
    await fs.copy(source, screenshotPath);
    analysis = await captureDesignFromImage({
      imagePath: screenshotPath,
      sourceName: inspirationName,
      notes: options.notes,
      llm: options.llm,
    });
  }

  let llmEnrichment;
  if (options.llm) {
    llmEnrichment = await enrichWithLlm({
      llm: options.llm,
      sourceName: inspirationName,
      sourceUrl: options.url,
      notes: options.notes,
      fallbackSummary: options.inspirationSummary,
      analysis,
    });
  }

  const fingerprint = computeFingerprint({
    url: options.url,
    analysis,
  });

  const previousVersion = resolvePreviousVersion(project.inspirations, fingerprint);
  const version = previousVersion ? previousVersion.version + 1 : 1;

  const mergedTags = mergeTags(
    options.tags,
    llmEnrichment?.suggestedTags ?? []
  );

  const inspirationSummary = options.inspirationSummary
    || llmEnrichment?.summary
    || undefined;

  const record: InspirationRecord = {
    id: inspirationId,
    name: inspirationName,
    sourceType: options.url ? 'url' : 'screenshot',
    url: options.url,
    originalImagePath: options.screenshot ? path.resolve(options.rootDir, options.screenshot) : undefined,
    screenshotPath,
    capturedAt: nowIso(),
    tags: mergedTags,
    notes: options.notes,
    inspirationSummary,
    llmEnrichment,
    fingerprint,
    version,
    supersedes: previousVersion?.id,
    diffFromPrevious: previousVersion ? buildDiff(previousVersion, analysis) : undefined,
    analysis,
  };

  project.inspirations.push(record);

  project.updatedAt = nowIso();
  await saveDatabase(options.rootDir, db);
  await renderAll(options.rootDir, db);

  return { projectId: project.id, inspirationId };
}

export async function recordOutcome(options: OutcomeOptions): Promise<{ projectId: string; outcomeId: string }> {
  if (!options.title.trim()) {
    throw new Error('--title is required');
  }

  if (!options.description.trim()) {
    throw new Error('--description is required');
  }

  await ensureBrainExists(options.rootDir);
  const db = await loadDatabase(options.rootDir);
  const project = ensureProject(db, {
    projectId: options.project,
  });

  const outcomeId = makeId('outcome', options.title);

  const knownInspirationIds = new Set(project.inspirations.map((entry) => entry.id));
  const inspiredBy = options.inspiredBy.filter((id) => knownInspirationIds.has(id));

  project.outcomes.push({
    id: outcomeId,
    title: options.title,
    description: options.description,
    inspiredBy,
    artifactUrl: options.artifactUrl,
    createdAt: nowIso(),
    tags: unique(options.tags.map((tag) => slugify(tag)).filter(Boolean)),
  });

  project.updatedAt = nowIso();
  await saveDatabase(options.rootDir, db);
  await renderAll(options.rootDir, db);

  return { projectId: project.id, outcomeId };
}

export async function reindexBrain(rootDir: string): Promise<void> {
  const db = await loadDatabase(rootDir);
  await renderAll(rootDir, db);
}

export async function searchBrain(params: {
  rootDir: string;
  query: string;
  project?: string;
  limit?: number;
}) {
  return searchDesignBrain(params);
}

export async function askBrain(params: {
  rootDir: string;
  query: string;
  project?: string;
  limit?: number;
  llm?: LlmConfig;
}) {
  return askDesignBrain(params);
}
