import { answerDesignQuestion } from './llm.js';
import { loadDatabase } from './store.js';
import { truncate, unique } from './util.js';
import type { LlmConfig } from './types.js';

export interface SearchResult {
  type: 'project' | 'inspiration' | 'outcome';
  projectId: string;
  id: string;
  title: string;
  score: number;
  snippet: string;
}

function tokenize(input: string): string[] {
  const base = input
    .toLowerCase()
    .split(/\s+/)
    .map((token) => token.trim())
    .filter((token) => token.length > 1);

  const expanded: string[] = [];
  for (const token of base) {
    expanded.push(token);
    if (token.endsWith('s') && token.length > 3) {
      expanded.push(token.slice(0, -1));
    }
  }

  return unique(expanded);
}

function countHits(haystack: string, tokens: string[]): number {
  const lower = haystack.toLowerCase();
  let score = 0;

  for (const token of tokens) {
    if (lower.includes(token)) {
      score += 1;
    }
  }

  return score;
}

function buildSnippet(haystack: string, tokens: string[]): string {
  const lower = haystack.toLowerCase();
  for (const token of tokens) {
    const idx = lower.indexOf(token);
    if (idx >= 0) {
      const start = Math.max(0, idx - 60);
      const end = Math.min(haystack.length, idx + 120);
      return truncate(haystack.slice(start, end).replace(/\s+/g, ' ').trim(), 180);
    }
  }
  return truncate(haystack.replace(/\s+/g, ' ').trim(), 180);
}

export async function searchDesignBrain(params: {
  rootDir: string;
  query: string;
  project?: string;
  limit?: number;
}): Promise<SearchResult[]> {
  const db = await loadDatabase(params.rootDir);
  const tokens = tokenize(params.query);
  const results: SearchResult[] = [];

  if (tokens.length === 0) {
    return [];
  }

  for (const project of db.projects) {
    if (params.project && params.project !== project.id) {
      continue;
    }

    const projectText = `${project.name}\n${project.description ?? ''}`;
    const projectScore = countHits(projectText, tokens);
    if (projectScore > 0) {
      results.push({
        type: 'project',
        projectId: project.id,
        id: project.id,
        title: project.name,
        score: projectScore,
        snippet: buildSnippet(projectText, tokens),
      });
    }

    for (const inspiration of project.inspirations) {
      const inspirationText = [
        inspiration.name,
        inspiration.url,
        inspiration.notes,
        inspiration.inspirationSummary,
        inspiration.llmEnrichment?.summary,
        ...(inspiration.llmEnrichment?.designPrinciples ?? []),
        ...(inspiration.llmEnrichment?.componentPatterns ?? []),
        inspiration.analysis.colors.map((color) => color.hex).join(' '),
        inspiration.analysis.components.map((component) => component.kind).join(' '),
        inspiration.analysis.motion.map((m) => {
          if ('library' in m && 'motionIntent' in m) {
            return `${(m as { motionIntent: string }).motionIntent} ${(m as { library: string }).library} ${m.selector}`;
          }
          return `${(m as { transition: string }).transition} ${(m as { animation: string }).animation}`;
        }).join(' '),
        inspiration.analysis.stateStyles && inspiration.analysis.stateStyles.length > 0 ? 'interaction states hover focus active' : '',
        (inspiration.analysis.stateStyles ?? []).map((state) => `${state.selector} ${state.state}`).join(' '),
        (inspiration.analysis.responsiveSnapshots ?? []).map((snap) => `${snap.label} ${snap.viewport.width}x${snap.viewport.height}`).join(' '),
        (inspiration.analysis.journey ?? []).map((step) => `${step.action} ${step.summary ?? ''}`).join(' '),
      ].filter(Boolean).join('\n');

      const score = countHits(inspirationText, tokens);
      if (score > 0) {
        results.push({
          type: 'inspiration',
          projectId: project.id,
          id: inspiration.id,
          title: inspiration.name,
          score,
          snippet: buildSnippet(inspirationText, tokens),
        });
      }
    }

    for (const outcome of project.outcomes) {
      const outcomeText = [
        outcome.title,
        outcome.description,
        outcome.tags.join(' '),
        outcome.artifactUrl,
      ].filter(Boolean).join('\n');
      const score = countHits(outcomeText, tokens);
      if (score > 0) {
        results.push({
          type: 'outcome',
          projectId: project.id,
          id: outcome.id,
          title: outcome.title,
          score,
          snippet: buildSnippet(outcomeText, tokens),
        });
      }
    }
  }

  return results
    .sort((a, b) => b.score - a.score)
    .slice(0, params.limit ?? 10);
}

function buildContext(results: SearchResult[]): string {
  if (results.length === 0) {
    return 'No matches found.';
  }

  return results
    .map((result, index) => `${index + 1}. [${result.type}] ${result.projectId}/${result.id}: ${result.title}\n${result.snippet}`)
    .join('\n\n');
}

export async function askDesignBrain(params: {
  rootDir: string;
  query: string;
  project?: string;
  limit?: number;
  llm?: LlmConfig;
}): Promise<{ answer: string; matches: SearchResult[] }> {
  const matches = await searchDesignBrain({
    rootDir: params.rootDir,
    query: params.query,
    project: params.project,
    limit: params.limit ?? 8,
  });

  if (!params.llm) {
    if (matches.length === 0) {
      return { answer: 'No matching design memory records found.', matches };
    }

    const answer = [
      'Top matches (LLM not configured):',
      ...matches.map((match) => `- [${match.type}] ${match.projectId}/${match.id}: ${match.title} (${match.score})`),
    ].join('\n');

    return { answer, matches };
  }

  const context = buildContext(matches);
  const answer = await answerDesignQuestion({
    llm: params.llm,
    query: params.query,
    context,
  });

  return { answer, matches };
}
