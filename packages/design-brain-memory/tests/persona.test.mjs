import test from 'node:test';
import assert from 'node:assert/strict';
import { assignPersona } from '../dist/persona.js';

function makeTokens(overrides = {}) {
  return {
    colors: [],
    fontFamilies: [],
    fontSizes: [],
    transitions: [],
    spacingValues: [],
    cssVariableCount: 0,
    framework: null,
    ...overrides,
  };
}

test('monochrome with few fonts → Jony Ive or Dieter Rams', () => {
  const tokens = makeTokens({
    colors: ['#000000', '#333333', '#ffffff'],
    fontFamilies: ['sf-pro'],
    fontSizes: ['14px', '16px', '24px'],
    transitions: ['all 0.2s ease'],
    spacingValues: ['8px', '16px', '24px', '32px'],
    cssVariableCount: 5,
  });
  const result = assignPersona(tokens);
  assert.ok(
    result.name === 'Jony Ive' || result.name === 'Dieter Rams',
    `Expected Jony Ive or Dieter Rams but got ${result.name}`,
  );
});

test('high font variety + many colors → Paula Scher', () => {
  const tokens = makeTokens({
    colors: ['#ff0000', '#00ff00', '#0000ff', '#ffff00', '#ff00ff',
             '#00ffff', '#ff8800', '#8800ff', '#0088ff', '#ff0088',
             '#88ff00', '#00ff88', '#ff4400', '#4400ff', '#44ff00'],
    fontFamilies: ['cooper-black', 'futura', 'garamond', 'helvetica-neue', 'baskerville'],
    fontSizes: ['12px', '16px', '24px', '36px', '48px', '72px', '96px'],
    transitions: ['all 0.3s ease', 'transform 0.5s', 'opacity 0.3s', 'color 0.2s', 'scale 0.4s', 'rotate 0.6s'],
    spacingValues: ['10px', '15px', '30px', '45px'],
    cssVariableCount: 0,
  });
  const result = assignPersona(tokens);
  assert.equal(result.name, 'Paula Scher', `Expected Paula Scher but got ${result.name}`);
});

test('extreme minimalism + no framework + off-grid → Ye', () => {
  const tokens = makeTokens({
    colors: ['#000000', '#ffffff'],
    fontFamilies: ['arial'],
    fontSizes: ['16px'],
    transitions: [],
    spacingValues: ['10px', '25px', '50px'],  // off-grid: not 4px multiples
    cssVariableCount: 0,
    framework: null,
  });
  const result = assignPersona(tokens);
  assert.equal(result.name, 'Ye', `Expected Ye but got ${result.name}`);
});

test('very few fonts + systematic spacing → Massimo Vignelli', () => {
  const tokens = makeTokens({
    colors: ['#000000', '#333333', '#666666', '#ffffff', '#f0f0f0'],
    fontFamilies: ['helvetica'],
    fontSizes: ['12px', '16px', '24px', '48px'],
    transitions: [],
    spacingValues: ['4px', '8px', '16px', '24px', '32px', '48px'],
    cssVariableCount: 4,
  });
  const result = assignPersona(tokens);
  assert.ok(
    result.name === 'Massimo Vignelli' || result.name === 'Dieter Rams',
    `Expected Vignelli or Rams but got ${result.name}`,
  );
});

test('mixed fonts + off-grid spacing + many colors → Virgil Abloh', () => {
  const tokens = makeTokens({
    colors: ['#ff0000', '#00ff00', '#0000ff', '#ff8800', '#8800ff',
             '#00ffaa', '#ffaa00', '#aa00ff', '#0055ff', '#ff5500',
             '#55ff00', '#00ff55', '#5500ff', '#ff0055', '#ff00aa',
             '#aaff00', '#00aaff', '#aa00ff', '#ff00aa', '#00ffaa'],
    fontFamilies: ['futura', 'times-new-roman', 'comic-sans', 'impact', 'papyrus'],
    fontSizes: ['11px', '13px', '17px', '23px', '37px'],
    transitions: ['all 0.1s', 'color 0.5s', 'transform 1s', 'opacity 0.3s'],
    spacingValues: ['5px', '11px', '17px', '23px', '37px', '41px'],
    cssVariableCount: 0,
    framework: null,
  });
  const result = assignPersona(tokens);
  assert.equal(result.name, 'Virgil Abloh', `Expected Virgil Abloh but got ${result.name}`);
});

test('strong grid + few colors + CSS vars → Dieter Rams', () => {
  const tokens = makeTokens({
    colors: ['#1a1a1a', '#ffffff', '#666666'],
    fontFamilies: ['inter', 'monospace'],
    fontSizes: ['14px', '16px', '20px'],
    transitions: ['opacity 0.2s'],
    spacingValues: ['4px', '8px', '12px', '16px', '24px', '32px', '48px', '64px'],
    cssVariableCount: 10,
  });
  const result = assignPersona(tokens);
  assert.ok(
    result.name === 'Dieter Rams' || result.name === 'Jony Ive',
    `Expected Dieter Rams or Jony Ive but got ${result.name}`,
  );
});

test('assignPersona always returns valid PersonaMatch', () => {
  const tokens = makeTokens();
  const result = assignPersona(tokens);
  assert.ok(result.name);
  assert.ok(result.tagline);
  assert.ok(typeof result.score === 'number');
  assert.ok(result.score >= 0 && result.score <= 1);
  assert.ok(result.reasoning);
});
