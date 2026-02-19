import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import { scanCssContent, collectFiles, detectFramework, scanDesignSystem } from '../dist/scan.js';

test('scanCssContent extracts hex colors', () => {
  const result = scanCssContent(`
    .btn { color: #ff0000; background: #00ff00; border: 1px solid #00F; }
  `);
  assert.ok(result.colors.includes('#ff0000'));
  assert.ok(result.colors.includes('#00ff00'));
  assert.ok(result.colors.includes('#0000ff')); // normalized from #00F
  assert.equal(result.colors.length, 3);
});

test('scanCssContent extracts rgb colors as hex', () => {
  const result = scanCssContent(`
    .card { color: rgb(255, 128, 0); background: rgba(0, 0, 255, 0.5); }
  `);
  assert.ok(result.colors.includes('#ff8000'));
  assert.ok(result.colors.includes('#0000ff'));
});

test('scanCssContent extracts font families', () => {
  const result = scanCssContent(`
    body { font-family: 'Inter', sans-serif; }
    h1 { font-family: "Georgia", serif; }
  `);
  assert.ok(result.fontFamilies.includes('inter'));
  assert.ok(result.fontFamilies.includes('sans-serif'));
  assert.ok(result.fontFamilies.includes('georgia'));
  assert.ok(result.fontFamilies.includes('serif'));
});

test('scanCssContent extracts font sizes', () => {
  const result = scanCssContent(`
    h1 { font-size: 2rem; }
    p { font-size: 16px; }
  `);
  assert.ok(result.fontSizes.includes('2rem'));
  assert.ok(result.fontSizes.includes('16px'));
});

test('scanCssContent extracts transitions and animations', () => {
  const result = scanCssContent(`
    .btn { transition: all 0.3s ease; }
    .card { animation: fadeIn 0.5s; }
  `);
  assert.equal(result.transitions.length, 2);
  assert.ok(result.transitions[0].includes('0.3s'));
  assert.ok(result.transitions[1].includes('fadeIn'));
});

test('scanCssContent extracts spacing values', () => {
  const result = scanCssContent(`
    .card { margin: 16px; padding: 8px 12px; gap: 24px; }
  `);
  assert.ok(result.spacingValues.length >= 3);
  assert.ok(result.spacingValues.some(v => v.includes('16px')));
  assert.ok(result.spacingValues.some(v => v.includes('24px')));
});

test('scanCssContent counts CSS variables', () => {
  const result = scanCssContent(`
    :root {
      --primary: #0055ff;
      --secondary: #ff5500;
      --spacing-sm: 8px;
    }
  `);
  assert.equal(result.cssVariableCount, 3);
});

test('scanCssContent deduplicates colors', () => {
  const result = scanCssContent(`
    .a { color: #ff0000; }
    .b { background: #FF0000; }
    .c { border-color: #ff0000; }
  `);
  assert.equal(result.colors.length, 1);
});

test('collectFiles skips node_modules and .git', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-collect-'));
  await fs.mkdir(path.join(tmpDir, 'src'));
  await fs.mkdir(path.join(tmpDir, 'node_modules', 'pkg'), { recursive: true });
  await fs.mkdir(path.join(tmpDir, '.git', 'objects'), { recursive: true });

  await fs.writeFile(path.join(tmpDir, 'src', 'app.css'), 'body { color: red; }');
  await fs.writeFile(path.join(tmpDir, 'node_modules', 'pkg', 'style.css'), '.nm { color: blue; }');
  await fs.writeFile(path.join(tmpDir, '.git', 'objects', 'file.css'), '.git { color: green; }');

  const files = collectFiles(tmpDir);
  assert.equal(files.length, 1);
  assert.ok(files[0].endsWith('app.css'));
});

test('detectFramework returns null for empty directory', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-fw-'));
  const fw = await detectFramework(tmpDir);
  assert.equal(fw, null);
});

test('detectFramework detects tailwind from package.json', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-fw-tw-'));
  await fs.writeFile(
    path.join(tmpDir, 'package.json'),
    JSON.stringify({ dependencies: { tailwindcss: '^3.0.0' } }),
  );
  const fw = await detectFramework(tmpDir);
  assert.equal(fw, 'tailwind');
});

test('detectFramework detects chakra from package.json', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-fw-ch-'));
  await fs.writeFile(
    path.join(tmpDir, 'package.json'),
    JSON.stringify({ dependencies: { '@chakra-ui/react': '^2.0.0' } }),
  );
  const fw = await detectFramework(tmpDir);
  assert.equal(fw, 'chakra');
});

test('detectFramework detects mui from package.json', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-fw-mui-'));
  await fs.writeFile(
    path.join(tmpDir, 'package.json'),
    JSON.stringify({ devDependencies: { '@mui/material': '^5.0.0' } }),
  );
  const fw = await detectFramework(tmpDir);
  assert.equal(fw, 'mui');
});

test('scanDesignSystem returns correct structure', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-full-'));
  await fs.mkdir(path.join(tmpDir, 'src'));
  await fs.writeFile(
    path.join(tmpDir, 'src', 'styles.css'),
    `
    :root {
      --primary: #0055ff;
      --bg: #ffffff;
    }
    body { font-family: Inter, sans-serif; font-size: 16px; color: var(--primary); }
    h1 { font-size: 2rem; }
    .btn { transition: all 0.2s ease; padding: 8px 16px; margin: 4px; }
    .card { padding: 24px; gap: 16px; background: #f5f5f5; }
    `,
  );

  const result = await scanDesignSystem(tmpDir);
  assert.equal(result.filesScanned, 1);
  assert.ok(result.tokens.colors.length >= 2);
  assert.ok(result.tokens.fontFamilies.includes('inter'));
  assert.ok(result.tokens.transitions.length >= 1);
  assert.ok(result.tokens.spacingValues.length >= 3);
  assert.equal(result.tokens.cssVariableCount, 2);
  assert.ok(result.score.total >= 0 && result.score.total <= 100);
  assert.ok(result.persona.name);
  assert.ok(result.persona.tagline);
  assert.ok(result.persona.reasoning);
});

test('score computation rewards disciplined design', async () => {
  const tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'scan-score-'));
  await fs.mkdir(path.join(tmpDir, 'src'));

  // A disciplined design: few colors, few fonts, grid spacing, CSS vars, transitions
  await fs.writeFile(
    path.join(tmpDir, 'src', 'theme.css'),
    `
    :root {
      --primary: #0055ff;
      --text: #333333;
      --bg: #ffffff;
      --border: #e0e0e0;
      --spacing-sm: 8px;
      --spacing-md: 16px;
    }
    body { font-family: Inter, sans-serif; font-size: 16px; color: #333333; }
    h1 { font-size: 24px; }
    h2 { font-size: 20px; }
    .btn { transition: all 200ms ease; padding: 8px 16px; margin: 8px; }
    .card { padding: 16px; gap: 8px; margin: 16px; }
    .modal { padding: 24px; gap: 16px; transition: opacity 200ms ease; }
    .input { padding: 8px 12px; margin: 4px 0; transition: border-color 200ms ease; }
    `,
  );

  const result = await scanDesignSystem(tmpDir);
  // A disciplined design should score reasonably high
  assert.ok(result.score.total >= 50, `Expected score >= 50 but got ${result.score.total}`);
  assert.ok(result.score.colorDiscipline >= 15, `Color discipline too low: ${result.score.colorDiscipline}`);
  assert.ok(result.score.typographySystem >= 15, `Typography system too low: ${result.score.typographySystem}`);
});
