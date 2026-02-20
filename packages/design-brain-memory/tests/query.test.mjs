import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import os from 'node:os';
import { searchDesignBrain } from '../dist/query.js';

async function makeFixtureRoot() {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), 'design-brain-query-'));
  const brain = path.join(root, '.design-brain');
  await fs.mkdir(path.join(brain, 'projects'), { recursive: true });
  await fs.mkdir(path.join(brain, 'assets'), { recursive: true });
  await fs.mkdir(path.join(brain, 'graph'), { recursive: true });

  const db = {
    version: 1,
    createdAt: new Date().toISOString(),
    updatedAt: new Date().toISOString(),
    projects: [
      {
        id: 'checkout',
        name: 'Checkout',
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        inspirations: [
          {
            id: 'inspo-a',
            name: 'Stripe CTA',
            sourceType: 'url',
            capturedAt: new Date().toISOString(),
            tags: ['button'],
            inspirationSummary: 'Bold primary button hierarchy',
            fingerprint: 'abc',
            version: 1,
            analysis: {
              colors: [{ hex: '#0055FF', count: 10, samples: [] }],
              typography: [],
              components: [{ kind: 'button', tag: 'button', selector: 'button.primary', text: 'Pay', className: 'primary', styles: {} }],
              motion: [],
              layout: [],
              cssVariables: {},
            },
          },
        ],
        outcomes: [
          {
            id: 'outcome-a',
            title: 'Checkout v1',
            description: 'Shipped primary CTA pattern',
            inspiredBy: ['inspo-a'],
            createdAt: new Date().toISOString(),
            tags: ['ship'],
          },
        ],
      },
    ],
  };

  await fs.writeFile(path.join(brain, 'database.json'), JSON.stringify(db, null, 2));
  return root;
}

test('searchDesignBrain returns inspiration and outcome matches', async () => {
  const root = await makeFixtureRoot();
  const results = await searchDesignBrain({ rootDir: root, query: 'button checkout', limit: 10 });

  assert.ok(results.length >= 2);
  assert.ok(results.some((item) => item.type === 'inspiration'));
  assert.ok(results.some((item) => item.type === 'outcome'));
});
