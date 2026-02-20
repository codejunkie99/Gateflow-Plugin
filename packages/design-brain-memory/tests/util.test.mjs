import test from 'node:test';
import assert from 'node:assert/strict';
import { normalizeUrl, stableHash } from '../dist/util.js';

test('stableHash is deterministic', () => {
  const one = stableHash('abc');
  const two = stableHash('abc');
  const three = stableHash('abcd');

  assert.equal(one, two);
  assert.notEqual(one, three);
});

test('normalizeUrl removes hash fragment', () => {
  const result = normalizeUrl('https://example.com/path#section');
  assert.equal(result, 'https://example.com/path');
});
