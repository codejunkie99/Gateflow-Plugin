import path from 'node:path';
import os from 'node:os';
import fs from 'fs-extra';
import { runAgentBrowserJson } from './agentBrowser.js';
import type { DesignAnalysis } from './types.js';

const SESSION_NAME = 'design-brain-demo';

/* ─── Highlight injection script ─── */

const HIGHLIGHT_SCRIPT = String.raw`(() => {
  const style = document.createElement('style');
  style.id = 'design-brain-highlights';
  style.textContent = [
    '@keyframes db-pulse { 0%,100% { opacity: 0.7; } 50% { opacity: 1; } }',
    '.db-highlight-color { outline: 3px solid #00ff88 !important; animation: db-pulse 1s infinite; }',
    '.db-highlight-typo { text-decoration: underline wavy #ff6b00 !important; text-underline-offset: 4px; }',
    '.db-highlight-component { outline: 3px solid #6366f1 !important; outline-offset: 2px; box-shadow: 0 0 12px rgba(99,102,241,0.4) !important; }',
  ].join('\n');
  document.head.appendChild(style);

  const nodes = Array.from(document.querySelectorAll('body *')).slice(0, 500);
  let colorCount = 0, typoCount = 0, compCount = 0;

  nodes.forEach(el => {
    const s = getComputedStyle(el);
    const bg = s.backgroundColor;
    if (bg && bg !== 'rgba(0, 0, 0, 0)' && bg !== 'transparent' && colorCount < 15) {
      el.classList.add('db-highlight-color');
      colorCount++;
    }
    if (el.textContent?.trim().length > 3 && s.fontSize && parseInt(s.fontSize) >= 20 && typoCount < 10) {
      el.classList.add('db-highlight-typo');
      typoCount++;
    }
    const tag = el.tagName.toLowerCase();
    if ((tag === 'button' || tag === 'a' || el.getAttribute('role') === 'button') && compCount < 10) {
      el.classList.add('db-highlight-component');
      compCount++;
    }
  });

  return { colorCount, typoCount, compCount };
})()`;

/* ─── Cleanup script ─── */

const CLEANUP_SCRIPT = String.raw`(() => {
  document.getElementById('design-brain-highlights')?.remove();
  document.querySelectorAll('.db-highlight-color,.db-highlight-typo,.db-highlight-component')
    .forEach(el => el.classList.remove('db-highlight-color','db-highlight-typo','db-highlight-component'));
})()`;

/* ─── Scroll script ─── */

const SCROLL_SCRIPT = String.raw`(() => {
  window.scrollBy({ top: 400, behavior: 'smooth' });
  return { scrollY: window.scrollY };
})()`;

/* ─── Extraction script (same as extractFromUrl.ts) ─── */

const EXTRACTION_SCRIPT = String.raw`(() => {
  const maxNodes = 2000;
  const nodes = Array.from(document.querySelectorAll('body *')).slice(0, maxNodes);

  const colorMap = new Map();
  const typographyMap = new Map();
  const componentList = [];
  const motionList = [];
  const layoutList = [];
  const variableMap = {};

  const componentTags = new Set(['button', 'a', 'input', 'select', 'textarea', 'nav', 'header', 'footer', 'form']);
  const maxComponents = 220;
  const maxMotion = 220;

  function normalizeWhitespace(text) {
    return (text || '').replace(/\s+/g, ' ').trim();
  }

  function pushColor(value, sample) {
    if (!value || value === 'transparent' || value === 'rgba(0, 0, 0, 0)') return;
    const parsed = parseCssColor(value);
    if (!parsed) return;
    const key = parsed.toUpperCase();
    const entry = colorMap.get(key) || { hex: key, count: 0, samples: [] };
    entry.count += 1;
    if (sample && entry.samples.length < 5 && !entry.samples.includes(sample)) {
      entry.samples.push(sample);
    }
    colorMap.set(key, entry);
  }

  function parseCssColor(input) {
    if (!input) return null;
    const value = input.toString().trim().toLowerCase();
    if (value.startsWith('#')) {
      if (value.length === 4) return '#' + value[1] + value[1] + value[2] + value[2] + value[3] + value[3];
      if (value.length === 7) return value;
      return null;
    }
    const rgbMatch = value.match(/rgba?\(([^)]+)\)/);
    if (rgbMatch) {
      const parts = rgbMatch[1].split(',').map(p => p.trim());
      const r = Number(parts[0]), g = Number(parts[1]), b = Number(parts[2]);
      if ([r, g, b].some(n => Number.isNaN(n))) return null;
      const toHex = n => Math.max(0, Math.min(255, n)).toString(16).padStart(2, '0');
      return '#' + toHex(r) + toHex(g) + toHex(b);
    }
    return null;
  }

  function buildSelector(el) {
    const tag = el.tagName.toLowerCase();
    if (el.id) return tag + '#' + el.id;
    if (typeof el.className === 'string' && el.className.trim()) {
      const firstClass = el.className.trim().split(/\s+/).slice(0, 2).join('.');
      if (firstClass) return tag + '.' + firstClass;
    }
    return tag;
  }

  function addTypography(style) {
    const key = [style.fontFamily, style.fontSize, style.fontWeight, style.lineHeight].join('|');
    const existing = typographyMap.get(key) || {
      fontFamily: style.fontFamily, fontSize: style.fontSize,
      fontWeight: style.fontWeight, lineHeight: style.lineHeight, count: 0,
    };
    existing.count += 1;
    typographyMap.set(key, existing);
  }

  function shouldCaptureAsComponent(el, selector) {
    const tag = el.tagName.toLowerCase();
    if (componentTags.has(tag)) return true;
    const className = typeof el.className === 'string' ? el.className.toLowerCase() : '';
    if (className.includes('btn') || className.includes('button') || className.includes('card') || className.includes('hero')) return true;
    if (el.getAttribute('role') === 'button' || el.getAttribute('role') === 'navigation') return true;
    return selector.startsWith('section.') || selector.startsWith('div.card');
  }

  function inferComponentKind(el) {
    const tag = el.tagName.toLowerCase();
    const className = typeof el.className === 'string' ? el.className.toLowerCase() : '';
    if (tag === 'button' || className.includes('btn')) return 'button';
    if (tag === 'a') return 'link';
    if (tag === 'input' || tag === 'textarea' || tag === 'select') return 'form-control';
    if (tag === 'nav' || className.includes('nav')) return 'navigation';
    if (className.includes('card')) return 'card';
    if (tag === 'header') return 'header';
    if (tag === 'footer') return 'footer';
    if (className.includes('hero')) return 'hero';
    return tag;
  }

  nodes.forEach(el => {
    const style = window.getComputedStyle(el);
    if (style.display === 'none' || style.visibility === 'hidden' || Number(style.opacity) === 0) return;
    const selector = buildSelector(el);
    pushColor(style.color, selector + ':color');
    pushColor(style.backgroundColor, selector + ':background');
    if (style.borderColor && style.borderColor !== 'rgba(0, 0, 0, 0)') {
      pushColor(style.borderColor, selector + ':border');
    }
    const hasText = normalizeWhitespace(el.textContent || '').length > 0;
    if (hasText) addTypography(style);
    if (shouldCaptureAsComponent(el, selector) && componentList.length < maxComponents) {
      componentList.push({
        kind: inferComponentKind(el), tag: el.tagName.toLowerCase(), selector,
        text: normalizeWhitespace(el.textContent || '').slice(0, 90),
        className: typeof el.className === 'string' ? normalizeWhitespace(el.className) : '',
        styles: {
          color: style.color, backgroundColor: style.backgroundColor,
          borderRadius: style.borderRadius, border: style.border,
          padding: style.padding, margin: style.margin,
          fontSize: style.fontSize, fontWeight: style.fontWeight, boxShadow: style.boxShadow,
        },
      });
    }
    const hasTransition = style.transitionDuration && style.transitionDuration !== '0s';
    const hasAnimation = style.animationName && style.animationName !== 'none';
    const hasTransform = style.transform && style.transform !== 'none';
    if ((hasTransition || hasAnimation || hasTransform) && motionList.length < maxMotion) {
      motionList.push({ selector, transition: style.transition, animation: style.animation, transform: style.transform });
    }
  });

  const layoutSelectors = Array.from(document.querySelectorAll('header, nav, main, section, article, aside, footer')).slice(0, 160);
  layoutSelectors.forEach(el => {
    layoutList.push({ tag: el.tagName.toLowerCase(), selector: buildSelector(el), role: el.getAttribute('role') || '', children: el.children.length });
  });

  [document.documentElement, document.body].forEach(root => {
    if (!root) return;
    const style = window.getComputedStyle(root);
    for (const propertyName of style) {
      if (!propertyName.startsWith('--')) continue;
      const value = style.getPropertyValue(propertyName).trim();
      if (value) variableMap[propertyName] = value;
    }
  });

  const colors = Array.from(colorMap.values()).sort((a, b) => b.count - a.count).slice(0, 70);
  const typography = Array.from(typographyMap.values()).sort((a, b) => b.count - a.count).slice(0, 90);

  return {
    pageTitle: document.title, pageUrl: window.location.href,
    viewport: { width: window.innerWidth, height: window.innerHeight },
    colors, typography, components: componentList, motion: motionList,
    layout: layoutList, cssVariables: variableMap,
  };
})()`;

/* ─── Normalize extraction result ─── */

function normalizeResult(result: Record<string, unknown>): DesignAnalysis {
  return {
    pageTitle: (result.pageTitle as string | undefined) ?? undefined,
    pageUrl: (result.pageUrl as string | undefined) ?? undefined,
    viewport: (result.viewport as { width: number; height: number } | undefined) ?? undefined,
    colors: (result.colors as DesignAnalysis['colors']) ?? [],
    typography: (result.typography as DesignAnalysis['typography']) ?? [],
    components: (result.components as DesignAnalysis['components']) ?? [],
    motion: (result.motion as DesignAnalysis['motion']) ?? [],
    layout: (result.layout as DesignAnalysis['layout']) ?? [],
    cssVariables: (result.cssVariables as DesignAnalysis['cssVariables']) ?? {},
  };
}

/* ─── Theatrical scan sequence ─── */

export async function theatricalScan(url: string): Promise<{
  analysis: DesignAnalysis;
  screenshotPath: string;
}> {
  const screenshotDir = path.join(os.tmpdir(), 'design-brain-theatrical');
  await fs.ensureDir(screenshotDir);
  const screenshotPath = path.join(screenshotDir, `scan-${Date.now()}.png`);

  const browserOpts = { session: SESSION_NAME, headed: true };

  // 1. Open the URL in a visible browser
  await runAgentBrowserJson(['open', url], browserOpts);

  try {
    // 2. Wait for page to settle
    await runAgentBrowserJson(['wait', '1500'], browserOpts);

    // 3. Slow scroll — 4 steps, ~600ms between each
    for (let i = 0; i < 4; i++) {
      await runAgentBrowserJson(['eval', SCROLL_SCRIPT], browserOpts);
      await runAgentBrowserJson(['wait', '600'], browserOpts);
    }

    // Scroll back to top for highlight injection
    await runAgentBrowserJson(['eval', 'window.scrollTo({ top: 0, behavior: "smooth" })'], browserOpts);
    await runAgentBrowserJson(['wait', '800'], browserOpts);

    // 4. Inject highlight overlays
    await runAgentBrowserJson(['eval', HIGHLIGHT_SCRIPT], browserOpts);

    // 5. Pause for visual impact
    await runAgentBrowserJson(['wait', '2000'], browserOpts);

    // 6. Take screenshot with overlays visible
    await runAgentBrowserJson(['screenshot', screenshotPath, '--full'], browserOpts);

    // 7. Clean overlays
    await runAgentBrowserJson(['eval', CLEANUP_SCRIPT], browserOpts);
    await runAgentBrowserJson(['wait', '300'], browserOpts);

    // 8. Extract design tokens (real extraction on clean page)
    const extraction = await runAgentBrowserJson(['eval', EXTRACTION_SCRIPT], browserOpts);

    if (!extraction.success) {
      throw new Error(`Extraction failed: ${extraction.error ?? 'Unknown error'}`);
    }

    const analysis = normalizeResult(
      (extraction.data.result as Record<string, unknown>) ?? {}
    );

    return { analysis, screenshotPath };
  } finally {
    await runAgentBrowserJson(['close'], browserOpts).catch(() => undefined);
  }
}
