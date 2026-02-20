import path from 'node:path';
import fs from 'fs-extra';
import { brainRoot, projectDir } from './store.js';
import { csvEscape, relPath, truncate, unique } from './util.js';
import type {
  AnimationToken,
  ColorToken,
  ComponentToken,
  DesignBrainDatabase,
  InspirationRecord,
  MotionToken,
  ProjectRecord,
  TypographyToken,
} from './types.js';

function isAnimationToken(token: MotionToken | AnimationToken): token is AnimationToken {
  return 'library' in token && 'motionIntent' in token;
}

function mdTable(headers: string[], rows: string[][]): string {
  const head = `| ${headers.join(' | ')} |`;
  const rule = `| ${headers.map(() => '---').join(' | ')} |`;
  const body = rows.map((row) => `| ${row.join(' | ')} |`).join('\n');
  return [head, rule, body].filter((line) => line.length > 0).join('\n');
}

export function aggregateColors(records: InspirationRecord[]): ColorToken[] {
  const map = new Map<string, ColorToken>();

  for (const record of records) {
    for (const color of record.analysis.colors) {
      const existing = map.get(color.hex) ?? { hex: color.hex, count: 0, samples: [] };
      existing.count += color.count;
      for (const sample of color.samples) {
        if (existing.samples.length < 6 && !existing.samples.includes(sample)) {
          existing.samples.push(sample);
        }
      }
      map.set(color.hex, existing);
    }
  }

  return [...map.values()].sort((a, b) => b.count - a.count).slice(0, 40);
}

export function aggregateTypography(records: InspirationRecord[]): TypographyToken[] {
  const map = new Map<string, TypographyToken>();

  for (const record of records) {
    for (const token of record.analysis.typography) {
      const key = `${token.fontFamily}|${token.fontSize}|${token.fontWeight}|${token.lineHeight}`;
      const existing = map.get(key) ?? { ...token, count: 0 };
      existing.count += token.count;
      map.set(key, existing);
    }
  }

  return [...map.values()].sort((a, b) => b.count - a.count).slice(0, 60);
}

export function aggregateComponents(records: InspirationRecord[]): Array<ComponentToken & { count: number }> {
  const map = new Map<string, ComponentToken & { count: number }>();

  for (const record of records) {
    for (const token of record.analysis.components) {
      const key = `${token.kind}|${token.tag}|${token.selector}`;
      const existing = map.get(key) ?? { ...token, count: 0 };
      existing.count += 1;
      map.set(key, existing);
    }
  }

  return [...map.values()].sort((a, b) => b.count - a.count).slice(0, 120);
}

export function aggregateMotion(records: InspirationRecord[]): Array<(MotionToken | AnimationToken) & { count: number }> {
  const map = new Map<string, (MotionToken | AnimationToken) & { count: number }>();

  for (const record of records) {
    for (const token of record.analysis.motion) {
      const key = isAnimationToken(token)
        ? `${token.selector}|${token.library}|${token.motionIntent}`
        : `${token.selector}|${token.transition}|${token.animation}|${token.transform}`;
      const existing = map.get(key) ?? { ...token, count: 0 };
      existing.count += 1;
      map.set(key, existing);
    }
  }

  return [...map.values()].sort((a, b) => b.count - a.count).slice(0, 140);
}

function renderRichMotionSection(tokens: Array<(MotionToken | AnimationToken) & { count: number }>): string {
  const animTokens = tokens.filter(isAnimationToken) as Array<AnimationToken & { count: number }>;
  const legacyTokens = tokens.filter((t) => !isAnimationToken(t)) as Array<MotionToken & { count: number }>;

  if (animTokens.length === 0 && legacyTokens.length > 0) {
    const rows = legacyTokens.map((t) => [
      truncate(t.transition || 'none'),
      truncate(t.animation || 'none'),
      `\`${t.selector}\``,
      `${t.count}`,
    ]);
    return mdTable(['Transition', 'Animation', 'Selector', 'Occurrences'], rows);
  }

  const sections: string[] = [];

  // Libraries
  const libraries = new Set<string>();
  for (const t of animTokens) {
    if (t.library !== 'css' && t.library !== 'unknown') {
      libraries.add(t.library);
    }
  }
  if (libraries.size > 0) {
    sections.push('### Libraries Detected\n' + [...libraries].map((l) => `- **${l}**`).join('\n'));
  }

  // Group by motionIntent
  const groups = new Map<string, Array<AnimationToken & { count: number }>>();
  for (const t of animTokens) {
    const group = groups.get(t.motionIntent) ?? [];
    group.push(t);
    groups.set(t.motionIntent, group);
  }

  const intentOrder = ['fade', 'slide', 'scale', 'rotate', 'spring', 'bounce', 'color-shift', 'reveal', 'morph', 'parallax', 'complex'];

  for (const intent of intentOrder) {
    const group = groups.get(intent);
    if (!group || group.length === 0) continue;

    const label = intent.charAt(0).toUpperCase() + intent.slice(1);

    if (intent === 'spring' || intent === 'bounce') {
      const rows = group.map((t) => [
        `\`${t.selector}\``,
        t.timing ? `${t.timing.duration}ms` : '-',
        t.physics?.overshootPercent != null ? `${t.physics.overshootPercent}%` : '-',
        t.physics?.oscillationCount != null ? `${t.physics.oscillationCount}` : '-',
        t.library,
      ]);
      sections.push(`### ${label} Animations (${group.length})\n\n` + mdTable(['Element', 'Duration', 'Overshoot', 'Oscillations', 'Library'], rows));
    } else {
      const rows = group.map((t) => [
        `\`${t.selector}\``,
        t.timing ? `${t.timing.duration}ms` : '-',
        t.timing?.easing ?? '-',
        t.trigger,
        t.library,
      ]);
      sections.push(`### ${label} Animations (${group.length})\n\n` + mdTable(['Element', 'Duration', 'Easing', 'Trigger', 'Library'], rows));
    }
  }

  // Lottie
  const lotties = animTokens.filter((t) => t.lottieMetadata);
  if (lotties.length > 0) {
    const rows = lotties.map((t) => [
      `\`${t.selector}\``,
      t.lottieMetadata ? `${t.lottieMetadata.frameRate}fps` : '-',
      t.lottieMetadata ? `${t.lottieMetadata.duration.toFixed(1)}s` : '-',
      t.lottieMetadata ? `${t.lottieMetadata.totalFrames}` : '-',
    ]);
    sections.push('### Lottie Animations\n\n' + mdTable(['Container', 'Frame Rate', 'Duration', 'Frames'], rows));
  }

  // Scroll-bound
  const scrollBound = animTokens.filter((t) => t.trigger === 'scroll' || t.scrollBinding);
  if (scrollBound.length > 0) {
    const rows = scrollBound.map((t) => [
      `\`${t.selector}\``,
      t.scrollBinding?.hasScrollTrigger ? 'ScrollTrigger' : 'CSS ScrollTimeline',
      t.library,
    ]);
    sections.push('### Scroll-Bound (passive)\n\n' + mdTable(['Element', 'Type', 'Library'], rows));
  }

  // Animation sequences
  const groupedTokens = animTokens.filter((t) => t.group);
  const sequenceMap = new Map<string, Array<AnimationToken & { count: number }>>();
  for (const t of groupedTokens) {
    const gid = t.group!.groupId;
    const seq = sequenceMap.get(gid) ?? [];
    seq.push(t);
    sequenceMap.set(gid, seq);
  }
  if (sequenceMap.size > 0) {
    const seqLines: string[] = [];
    for (const [gid, seq] of sequenceMap) {
      const sorted = seq.sort((a, b) => (a.group?.staggerDelay ?? 0) - (b.group?.staggerDelay ?? 0));
      const parts = sorted.map((t) => {
        const delay = t.group?.staggerDelay ?? 0;
        return t.group?.role === 'lead'
          ? `\`${t.selector}\` (lead)`
          : `\`${t.selector}\` (+${delay}ms)`;
      });
      seqLines.push(`- **${gid}**: ${parts.join(' → ')}`);
    }
    sections.push('### Animation Sequences\n\n' + seqLines.join('\n'));
  }

  // Legacy tokens at the end
  if (legacyTokens.length > 0) {
    const rows = legacyTokens.map((t) => [
      truncate(t.transition || 'none'),
      truncate(t.animation || 'none'),
      `\`${t.selector}\``,
      `${t.count}`,
    ]);
    sections.push('### CSS Transitions (legacy)\n\n' + mdTable(['Transition', 'Animation', 'Selector', 'Occurrences'], rows));
  }

  return sections.join('\n\n');
}

function renderProjectReadme(project: ProjectRecord): string {
  const inspirationLinks =
    project.inspirations.length > 0
      ? project.inspirations.map((record) => `- [${record.name}](./inspirations/${record.id}.md)`).join('\n')
      : '- No inspirations captured yet.';

  const outcomeLinks =
    project.outcomes.length > 0
      ? project.outcomes.map((record) => `- [${record.title}](./outcomes/${record.id}.md)`).join('\n')
      : '- No outcomes recorded yet.';

  return `# ${project.name}\n\n`
    + `Project ID: \`${project.id}\`\n\n`
    + `Created: ${project.createdAt}\n\n`
    + `Updated: ${project.updatedAt}\n\n`
    + `${project.description ? `${project.description}\n\n` : ''}`
    + `## Wiki\n\n`
    + `- [Colors](./tokens/colors.md)\n`
    + `- [Typography](./tokens/typography.md)\n`
    + `- [Components](./tokens/components.md)\n`
    + `- [Motion](./tokens/motion.md)\n`
    + `- [Layout](./tokens/layout.md)\n\n`
    + `## Inspirations\n\n${inspirationLinks}\n\n`
    + `## Outcomes\n\n${outcomeLinks}\n`;
}

function renderInspiration(record: InspirationRecord, projectId: string): string {
  const colorsRows = record.analysis.colors.slice(0, 30).map((color) => [
    color.hex,
    `${color.count}`,
    color.samples.map((value) => `\`${value}\``).join('<br/>'),
  ]);

  const typeRows = record.analysis.typography.slice(0, 40).map((token) => [
    token.fontFamily,
    token.fontSize,
    token.fontWeight,
    token.lineHeight,
    `${token.count}`,
  ]);

  const componentRows = record.analysis.components.slice(0, 60).map((component) => [
    component.kind,
    `\`${component.selector}\``,
    component.tag,
    truncate(component.text || '-'),
    truncate(component.className || '-'),
  ]);

  const motionContent = renderRichMotionSection(
    record.analysis.motion.slice(0, 80).map((t) => ({ ...t, count: 1 }))
  );

  const layoutRows = record.analysis.layout.slice(0, 80).map((layout) => [
    layout.tag,
    `\`${layout.selector}\``,
    layout.role || '-',
    `${layout.children}`,
  ]);

  const variablesRows = Object.entries(record.analysis.cssVariables)
    .slice(0, 120)
    .map(([key, value]) => [key, truncate(value, 80)]);

  const stateRows = (record.analysis.stateStyles ?? []).slice(0, 80).map((state) => [
    `\`${state.selector}\``,
    state.state,
    Object.entries(state.declarations)
      .map(([key, value]) => `${key}: ${truncate(value, 40)}`)
      .join('<br/>'),
  ]);

  const responsiveRows = (record.analysis.responsiveSnapshots ?? []).slice(0, 20).map((item) => [
    item.label,
    `${item.viewport.width}x${item.viewport.height}`,
    `${item.colorCount}`,
    `${item.typographyCount}`,
    `${item.componentCount}`,
    truncate(item.title ?? '-', 60),
  ]);

  const journeyRows = (record.analysis.journey ?? []).slice(0, 20).map((step) => [
    `${step.step}`,
    step.action,
    truncate(step.fromUrl ?? '-', 40),
    truncate(step.toUrl ?? '-', 40),
    truncate(step.summary ?? '-', 70),
  ]);

  const tags = record.tags.length > 0 ? record.tags.map((tag) => `\`${tag}\``).join(', ') : '-';

  return `# ${record.name}\n\n`
    + `ID: \`${record.id}\`\n\n`
    + `Project: \`${projectId}\`\n\n`
    + `Captured: ${record.capturedAt}\n\n`
    + `Source type: \`${record.sourceType}\`\n\n`
    + `${record.url ? `URL: ${record.url}\n\n` : ''}`
    + `${record.originalImagePath ? `Original image: \`${record.originalImagePath}\`\n\n` : ''}`
    + `${record.screenshotPath ? `Screenshot: \`${record.screenshotPath}\`\n\n` : ''}`
    + `Fingerprint: \`${record.fingerprint}\`\n\n`
    + `Version: \`${record.version}\`\n\n`
    + `${record.supersedes ? `Supersedes: \`${record.supersedes}\`\n\n` : ''}`
    + `Tags: ${tags}\n\n`
    + `${record.notes ? `Notes: ${record.notes}\n\n` : ''}`
    + `${record.inspirationSummary ? `Inspiration summary: ${record.inspirationSummary}\n\n` : ''}`
    + `${record.diffFromPrevious ? `## Diff From Previous\n\n- Previous: \`${record.diffFromPrevious.previousId}\`\n- Added colors: ${record.diffFromPrevious.addedColors.join(', ') || '-'}\n- Removed colors: ${record.diffFromPrevious.removedColors.join(', ') || '-'}\n- Component delta: ${record.diffFromPrevious.componentCountDelta}\n- Motion delta: ${record.diffFromPrevious.motionCountDelta}\n\n` : ''}`
    + `${record.llmEnrichment ? `## LLM Enrichment\n\n- Model: \`${record.llmEnrichment.model}\`\n- Base URL: \`${record.llmEnrichment.baseUrl}\`\n- Generated: ${record.llmEnrichment.generatedAt}\n- Color narrative: ${record.llmEnrichment.colorNarrative}\n\n### Design Principles\n${record.llmEnrichment.designPrinciples.map((item) => `- ${item}`).join('\n') || '- none'}\n\n### Component Patterns\n${record.llmEnrichment.componentPatterns.map((item) => `- ${item}`).join('\n') || '- none'}\n\n### Layout Guidance\n${(record.llmEnrichment.layoutGuidance ?? []).map((item) => `- ${item}`).join('\n') || '- none'}\n\n### Motion Guidance\n${(record.llmEnrichment.motionGuidance ?? []).map((item) => `- ${item}`).join('\n') || '- none'}\n\n` : ''}`
    + `${responsiveRows.length > 0 ? `## Responsive Coverage\n\n${mdTable(['Viewport', 'Size', 'Colors', 'Typography', 'Components', 'Title'], responsiveRows)}\n\n` : ''}`
    + `${stateRows.length > 0 ? `## Interaction States\n\n${mdTable(['Selector', 'State', 'Declarations'], stateRows)}\n\n` : ''}`
    + `${journeyRows.length > 0 ? `## Journey Capture\n\n${mdTable(['Step', 'Action', 'From', 'To', 'Summary'], journeyRows)}\n\n` : ''}`
    + `## Colors\n\n${mdTable(['Hex', 'Weight', 'Samples'], colorsRows)}\n\n`
    + `## Typography\n\n${mdTable(['Font', 'Size', 'Weight', 'Line Height', 'Weight'], typeRows)}\n\n`
    + `## Components\n\n${mdTable(['Kind', 'Selector', 'Tag', 'Text', 'Class'], componentRows)}\n\n`
    + `## Motion\n\n${motionContent}\n\n`
    + `## Layout\n\n${mdTable(['Tag', 'Selector', 'Role', 'Children'], layoutRows)}\n\n`
    + `## CSS Variables\n\n${mdTable(['Variable', 'Value'], variablesRows)}\n\n`
    + `${record.analysis.accessibilitySnapshot ? `## Accessibility Snapshot\n\n\`\`\`text\n${record.analysis.accessibilitySnapshot}\n\`\`\`\n` : ''}`;
}

function renderOutcome(project: ProjectRecord, outcomeId: string): string {
  const outcome = project.outcomes.find((entry) => entry.id === outcomeId);
  if (!outcome) {
    throw new Error(`Outcome not found: ${outcomeId}`);
  }

  const inspirations = outcome.inspiredBy
    .map((id) => project.inspirations.find((entry) => entry.id === id))
    .filter((entry): entry is InspirationRecord => Boolean(entry));

  const related =
    inspirations.length > 0
      ? inspirations.map((entry) => `- [${entry.name}](../inspirations/${entry.id}.md)`).join('\n')
      : '- None linked.';

  return `# ${outcome.title}\n\n`
    + `ID: \`${outcome.id}\`\n\n`
    + `Created: ${outcome.createdAt}\n\n`
    + `Description: ${outcome.description}\n\n`
    + `${outcome.artifactUrl ? `Artifact URL: ${outcome.artifactUrl}\n\n` : ''}`
    + `${outcome.tags.length > 0 ? `Tags: ${outcome.tags.map((tag) => `\`${tag}\``).join(', ')}\n\n` : ''}`
    + `## Inspired By\n\n${related}\n`;
}

function renderTokens(project: ProjectRecord): Record<string, string> {
  const colors = aggregateColors(project.inspirations);
  const typography = aggregateTypography(project.inspirations);
  const components = aggregateComponents(project.inspirations);
  const motion = aggregateMotion(project.inspirations);

  const colorRows = colors.map((token) => [token.hex, `${token.count}`, token.samples.map((sample) => `\`${sample}\``).join('<br/>')]);
  const typographyRows = typography.map((token) => [token.fontFamily, token.fontSize, token.fontWeight, token.lineHeight, `${token.count}`]);
  const componentRows = components.map((token) => [token.kind, token.tag, `\`${token.selector}\``, `${token.count}`]);
  const motionMarkdown = renderRichMotionSection(motion);

  const layoutRows = project.inspirations
    .flatMap((inspiration) => inspiration.analysis.layout.map((layout) => [
      layout.tag,
      `\`${layout.selector}\``,
      layout.role || '-',
      `${layout.children}`,
      inspiration.id,
    ]))
    .slice(0, 250);

  return {
    colors:
      `# ${project.name} Color Brain\n\n` + mdTable(['Hex', 'Weight', 'Samples'], colorRows) + '\n',
    typography:
      `# ${project.name} Typography Brain\n\n` + mdTable(['Font', 'Size', 'Weight', 'Line Height', 'Weight'], typographyRows) + '\n',
    components:
      `# ${project.name} Component Brain\n\n` + mdTable(['Kind', 'Tag', 'Selector', 'Occurrences'], componentRows) + '\n',
    motion:
      `# ${project.name} Motion Brain\n\n` + motionMarkdown + '\n',
    layout:
      `# ${project.name} Layout Brain\n\n` + mdTable(['Tag', 'Selector', 'Role', 'Children', 'Source'], layoutRows) + '\n',
  };
}

function renderRootReadme(db: DesignBrainDatabase): string {
  const projects =
    db.projects.length > 0
      ? db.projects
          .map((project) => {
            const inspirationCount = project.inspirations.length;
            const outcomeCount = project.outcomes.length;
            return `- [${project.name}](./projects/${project.id}/README.md) - ${inspirationCount} inspirations, ${outcomeCount} outcomes`;
          })
          .join('\n')
      : '- No projects yet.';

  return `# Design Brain\n\n`
    + `Relational design memory generated by \`design-brain-memory\`.\n\n`
    + `## Projects\n\n${projects}\n\n`
    + `## Retrieval\n\n`
    + `- Search all inspirations: \`rg "inspiration|component|color" .design-brain/projects\`\n`
    + `- Query relation graph: \`rg "has_inspiration|inspired_by" .design-brain/graph/relations.csv\`\n`
    + `- Find a color usage: \`rg "#0055FF" .design-brain\`\n`
    + `- CLI keyword search: \`design-brain-memory search --query "button hierarchy"\`\n`
    + `- CLI semantic ask: \`design-brain-memory ask --query "What changed between versions?"\`\n`;
}

function renderGraphFiles(db: DesignBrainDatabase): { entities: string; relations: string } {
  const entityRows: string[] = ['id,type,project,title,path'];
  const relationRows: string[] = ['from,relation,to,project,notes'];
  const seenEntities = new Set<string>();
  const seenRelations = new Set<string>();

  function pushEntity(values: string[]): void {
    const row = values.map(csvEscape).join(',');
    if (!seenEntities.has(row)) {
      seenEntities.add(row);
      entityRows.push(row);
    }
  }

  function pushRelation(values: string[]): void {
    const row = values.map(csvEscape).join(',');
    if (!seenRelations.has(row)) {
      seenRelations.add(row);
      relationRows.push(row);
    }
  }

  for (const project of db.projects) {
    const projectPath = `projects/${project.id}/README.md`;
    pushEntity([project.id, 'project', project.id, project.name, projectPath]);

    for (const inspiration of project.inspirations) {
      const inspirationPath = `projects/${project.id}/inspirations/${inspiration.id}.md`;
      pushEntity([inspiration.id, 'inspiration', project.id, inspiration.name, inspirationPath]);
      pushRelation([project.id, 'has_inspiration', inspiration.id, project.id, inspiration.url ?? inspiration.originalImagePath ?? '']);
      pushEntity([`fingerprint:${inspiration.fingerprint}`, 'fingerprint', project.id, inspiration.fingerprint, inspirationPath]);
      pushRelation([inspiration.id, 'has_fingerprint', `fingerprint:${inspiration.fingerprint}`, project.id, '']);
      if (inspiration.supersedes) {
        pushRelation([inspiration.id, 'supersedes', inspiration.supersedes, project.id, 'version lineage']);
      }

      const componentKinds = unique(inspiration.analysis.components.map((component) => component.kind));
      for (const kind of componentKinds) {
        const componentId = `component:${kind}`;
        pushEntity([componentId, 'component_kind', project.id, kind, inspirationPath]);
        pushRelation([inspiration.id, 'uses_component_kind', componentId, project.id, '']);
      }

      const topColors = inspiration.analysis.colors.slice(0, 12).map((color) => color.hex.toUpperCase());
      for (const color of topColors) {
        const colorId = `color:${color}`;
        pushEntity([colorId, 'color', project.id, color, inspirationPath]);
        pushRelation([inspiration.id, 'uses_color', colorId, project.id, '']);
      }
    }

    for (const outcome of project.outcomes) {
      const outcomePath = `projects/${project.id}/outcomes/${outcome.id}.md`;
      pushEntity([outcome.id, 'outcome', project.id, outcome.title, outcomePath]);
      pushRelation([project.id, 'has_outcome', outcome.id, project.id, '']);

      for (const sourceId of outcome.inspiredBy) {
        pushRelation([outcome.id, 'inspired_by', sourceId, project.id, '']);
      }
    }
  }

  return {
    entities: entityRows.join('\n') + '\n',
    relations: relationRows.join('\n') + '\n',
  };
}

export async function renderAll(rootDir: string, db: DesignBrainDatabase): Promise<void> {
  const root = brainRoot(rootDir);
  await fs.ensureDir(root);

  await fs.writeFile(path.join(root, 'README.md'), renderRootReadme(db));

  for (const project of db.projects) {
    const baseDir = projectDir(rootDir, project.id);
    const inspirationDir = path.join(baseDir, 'inspirations');
    const outcomeDir = path.join(baseDir, 'outcomes');
    const tokenDir = path.join(baseDir, 'tokens');

    await fs.ensureDir(inspirationDir);
    await fs.ensureDir(outcomeDir);
    await fs.ensureDir(tokenDir);

    await fs.writeFile(path.join(baseDir, 'README.md'), renderProjectReadme(project));

    for (const inspiration of project.inspirations) {
      await fs.writeFile(path.join(inspirationDir, `${inspiration.id}.md`), renderInspiration(inspiration, project.id));
    }

    for (const outcome of project.outcomes) {
      await fs.writeFile(path.join(outcomeDir, `${outcome.id}.md`), renderOutcome(project, outcome.id));
    }

    const tokenFiles = renderTokens(project);
    await fs.writeFile(path.join(tokenDir, 'colors.md'), tokenFiles.colors);
    await fs.writeFile(path.join(tokenDir, 'typography.md'), tokenFiles.typography);
    await fs.writeFile(path.join(tokenDir, 'components.md'), tokenFiles.components);
    await fs.writeFile(path.join(tokenDir, 'motion.md'), tokenFiles.motion);
    await fs.writeFile(path.join(tokenDir, 'layout.md'), tokenFiles.layout);

    const projectIndex = path.join(baseDir, 'index.md');
    const from = path.dirname(projectIndex);
    const links = [
      `[Project Wiki](${relPath(from, path.join(baseDir, 'README.md'))})`,
      `[Inspirations](${relPath(from, inspirationDir)})`,
      `[Outcomes](${relPath(from, outcomeDir)})`,
      `[Token Brain](${relPath(from, tokenDir)})`,
    ];
    await fs.writeFile(projectIndex, `# ${project.name} Index\n\n- ${links.join('\n- ')}\n`);
  }

  const graph = renderGraphFiles(db);
  await fs.writeFile(path.join(root, 'graph', 'entities.csv'), graph.entities);
  await fs.writeFile(path.join(root, 'graph', 'relations.csv'), graph.relations);
}
