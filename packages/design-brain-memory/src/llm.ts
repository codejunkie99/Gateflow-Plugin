import fs from 'node:fs/promises';
import path from 'node:path';
import { nowIso, unique } from './util.js';
import type {
  AnimationToken,
  ComponentToken,
  DesignAnalysis,
  LayoutToken,
  LlmConfig,
  LlmEnrichment,
  MotionToken,
  TypographyToken,
} from './types.js';

interface ChatCompletionResponse {
  choices?: Array<{
    message?: {
      content?: string | Array<{ type?: string; text?: string }>;
    };
  }>;
}

export function resolveLlmConfig(input: {
  baseUrl?: string;
  apiKey?: string;
  model?: string;
  timeoutMs?: number;
}): LlmConfig | undefined {
  const baseUrl = input.baseUrl?.trim() || process.env.DESIGN_BRAIN_LLM_BASE_URL || '';
  const apiKey = input.apiKey?.trim() || process.env.DESIGN_BRAIN_LLM_API_KEY || '';
  const model = input.model?.trim() || process.env.DESIGN_BRAIN_LLM_MODEL || 'gpt-4o-mini';

  if (!baseUrl && !apiKey && !input.model) {
    return undefined;
  }

  if (!apiKey) {
    throw new Error('LLM enabled but API key is missing. Set --llm-api-key or DESIGN_BRAIN_LLM_API_KEY.');
  }

  return {
    baseUrl: baseUrl || 'https://api.openai.com/v1',
    apiKey,
    model,
    timeoutMs: input.timeoutMs,
  };
}

function normalizeBaseUrl(baseUrl: string): string {
  const trimmed = baseUrl.trim().replace(/\/+$/, '');
  if (!trimmed) {
    throw new Error('LLM base URL is empty');
  }
  return trimmed;
}

function normalizeMessageContent(content: string | Array<{ type?: string; text?: string }> | undefined): string {
  if (typeof content === 'string') {
    return content;
  }

  if (!Array.isArray(content)) {
    return '';
  }

  return content
    .map((item) => item.text ?? '')
    .join('')
    .trim();
}

function extractFirstJsonObject(raw: string): string {
  const direct = raw.trim();
  if (direct.startsWith('{') && direct.endsWith('}')) {
    return direct;
  }

  const start = raw.indexOf('{');
  const end = raw.lastIndexOf('}');
  if (start >= 0 && end > start) {
    return raw.slice(start, end + 1);
  }

  throw new Error('LLM did not return JSON output');
}

function toStringArray(value: unknown): string[] {
  if (!Array.isArray(value)) {
    return [];
  }

  return unique(
    value
      .map((item) => (typeof item === 'string' ? item.trim() : ''))
      .filter((item) => item.length > 0)
  );
}

function clip(items: string[], max = 8): string[] {
  return items.slice(0, max);
}

async function runCompletion(params: {
  llm: LlmConfig;
  system: string;
  userContent: string | Array<Record<string, unknown>>;
  temperature?: number;
}): Promise<string> {
  const baseUrl = normalizeBaseUrl(params.llm.baseUrl);
  const apiKey = params.llm.apiKey.trim();

  if (!apiKey) {
    throw new Error('LLM API key is empty');
  }

  const controller = new AbortController();
  const timeoutMs = params.llm.timeoutMs ?? 30_000;
  const timer = setTimeout(() => {
    controller.abort();
  }, timeoutMs);

  try {
    const response = await fetch(`${baseUrl}/chat/completions`, {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${apiKey}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        model: params.llm.model,
        temperature: params.temperature ?? 0.2,
        messages: [
          {
            role: 'system',
            content: params.system,
          },
          {
            role: 'user',
            content: params.userContent,
          },
        ],
      }),
      signal: controller.signal,
    });

    if (!response.ok) {
      const errorText = await response.text();
      throw new Error(`LLM request failed (${response.status}): ${errorText}`);
    }

    const body = (await response.json()) as ChatCompletionResponse;
    const content = normalizeMessageContent(body.choices?.[0]?.message?.content);
    if (!content) {
      throw new Error('LLM returned empty content');
    }

    return content;
  } finally {
    clearTimeout(timer);
  }
}

function buildPrompt(input: {
  sourceName: string;
  sourceUrl?: string;
  notes?: string;
  fallbackSummary?: string;
  analysis: DesignAnalysis;
}): string {
  const colorList = input.analysis.colors.slice(0, 16).map((color) => `${color.hex}(${color.count})`).join(', ');
  const typographyList = input.analysis.typography
    .slice(0, 10)
    .map((token) => `${token.fontFamily} ${token.fontSize}/${token.lineHeight} w${token.fontWeight}`)
    .join('; ');
  const componentList = input.analysis.components.slice(0, 20).map((component) => `${component.kind}:${component.selector}`).join(', ');
  const motionList = input.analysis.motion.slice(0, 12).map((m) => {
    if ('library' in m && 'motionIntent' in m) {
      const at = m as AnimationToken;
      const dur = at.timing ? `${at.timing.duration}ms` : '';
      return `${at.selector}:${at.motionIntent}(${at.library}${dur ? ' ' + dur : ''})`;
    }
    const mt = m as MotionToken;
    return `${mt.selector}:${mt.transition || mt.animation || mt.transform}`;
  }).join(', ');

  return [
    'Create semantic design memory enrichment from extracted tokens.',
    'Return JSON only with keys:',
    'summary (string), designPrinciples (string[]), componentPatterns (string[]), colorNarrative (string), suggestedTags (string[]), layoutGuidance (string[]), motionGuidance (string[]).',
    '',
    `Source: ${input.sourceName}`,
    `URL: ${input.sourceUrl ?? 'N/A'}`,
    `User notes: ${input.notes ?? 'N/A'}`,
    `Current summary: ${input.fallbackSummary ?? 'N/A'}`,
    `Top colors: ${colorList || 'none'}`,
    `Typography: ${typographyList || 'none'}`,
    `Components: ${componentList || 'none'}`,
    `Motion: ${motionList || 'none'}`,
    '',
    'Constraints:',
    '- summary <= 40 words',
    '- 3 to 6 designPrinciples',
    '- 3 to 6 componentPatterns',
    '- 2 to 5 layoutGuidance',
    '- 2 to 5 motionGuidance',
    '- suggestedTags should be short kebab-case candidates',
  ].join('\n');
}

export async function enrichWithLlm(params: {
  llm: LlmConfig;
  sourceName: string;
  sourceUrl?: string;
  notes?: string;
  fallbackSummary?: string;
  analysis: DesignAnalysis;
}): Promise<LlmEnrichment> {
  const content = await runCompletion({
    llm: params.llm,
    system:
      'You are a senior design systems analyst. Return strict JSON only with the required keys and no markdown.',
    userContent: buildPrompt({
      sourceName: params.sourceName,
      sourceUrl: params.sourceUrl,
      notes: params.notes,
      fallbackSummary: params.fallbackSummary,
      analysis: params.analysis,
    }),
  });

  const jsonText = extractFirstJsonObject(content);
  const parsed = JSON.parse(jsonText) as Record<string, unknown>;

  const summary = typeof parsed.summary === 'string' ? parsed.summary.trim() : '';
  const colorNarrative = typeof parsed.colorNarrative === 'string' ? parsed.colorNarrative.trim() : '';

  if (!summary) {
    throw new Error('LLM response missing `summary`');
  }

  if (!colorNarrative) {
    throw new Error('LLM response missing `colorNarrative`');
  }

  return {
    summary,
    colorNarrative,
    designPrinciples: clip(toStringArray(parsed.designPrinciples), 6),
    componentPatterns: clip(toStringArray(parsed.componentPatterns), 6),
    layoutGuidance: clip(toStringArray(parsed.layoutGuidance), 5),
    motionGuidance: clip(toStringArray(parsed.motionGuidance), 5),
    suggestedTags: clip(toStringArray(parsed.suggestedTags), 8),
    model: params.llm.model,
    baseUrl: normalizeBaseUrl(params.llm.baseUrl),
    generatedAt: nowIso(),
  };
}

interface VisionEnrichment {
  summary?: string;
  components?: string[];
  typography?: string[];
  layout?: string[];
  motion?: string[];
  tags?: string[];
}

export async function enrichImageWithLlmVision(params: {
  llm: LlmConfig;
  imagePath: string;
  sourceName: string;
  notes?: string;
}): Promise<{
  summary?: string;
  tags: string[];
  components: ComponentToken[];
  typography: TypographyToken[];
  layout: LayoutToken[];
  motion: MotionToken[];
}> {
  const absolutePath = path.resolve(params.imagePath);
  const buffer = await fs.readFile(absolutePath);
  const base64 = buffer.toString('base64');

  const content = await runCompletion({
    llm: params.llm,
    system:
      'You are a UI design reverse-engineering expert. Return strict JSON only; no markdown.',
    userContent: [
      {
        type: 'text',
        text: [
          'Analyze this screenshot and return JSON with keys:',
          'summary (string), components (string[]), typography (string[]), layout (string[]), motion (string[]), tags (string[]).',
          'Use short, concrete entries.',
          `Source name: ${params.sourceName}`,
          `Notes: ${params.notes ?? 'N/A'}`,
        ].join('\n'),
      },
      {
        type: 'image_url',
        image_url: {
          url: `data:image/png;base64,${base64}`,
        },
      },
    ],
  });

  const jsonText = extractFirstJsonObject(content);
  const parsed = JSON.parse(jsonText) as VisionEnrichment;

  const components = (parsed.components ?? []).slice(0, 12).map((item, index) => ({
    kind: 'vision-inferred',
    tag: 'unknown',
    selector: `vision-component-${index + 1}`,
    text: item,
    className: '',
    styles: {},
  }));

  const typography = (parsed.typography ?? []).slice(0, 10).map((item) => ({
    fontFamily: 'vision-inferred',
    fontSize: item,
    fontWeight: 'unknown',
    lineHeight: 'unknown',
    count: 1,
  }));

  const layout = (parsed.layout ?? []).slice(0, 10).map((item, index) => ({
    tag: 'vision-layout',
    selector: `vision-layout-${index + 1}`,
    role: item,
    children: 0,
  }));

  const motion = (parsed.motion ?? []).slice(0, 8).map((item, index) => ({
    selector: `vision-motion-${index + 1}`,
    transition: item,
    animation: item,
    transform: 'vision-inferred',
  }));

  return {
    summary: parsed.summary,
    tags: clip(toStringArray(parsed.tags), 10),
    components,
    typography,
    layout,
    motion,
  };
}

export async function answerDesignQuestion(params: {
  llm: LlmConfig;
  query: string;
  context: string;
}): Promise<string> {
  return runCompletion({
    llm: params.llm,
    system: 'You answer design memory questions from provided context. Be concise and factual.',
    userContent: [`Question: ${params.query}`, '', 'Context:', params.context].join('\n'),
    temperature: 0.1,
  });
}
