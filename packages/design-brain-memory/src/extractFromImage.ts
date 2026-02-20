import fs from 'fs-extra';
import sharp from 'sharp';
import { enrichImageWithLlmVision } from './llm.js';
import type { ColorToken, DesignAnalysis, LlmConfig } from './types.js';

function channelBucket(value: number): number {
  return Math.max(0, Math.min(255, Math.round(value / 16) * 16));
}

function toHex(value: number): string {
  return Math.max(0, Math.min(255, value)).toString(16).padStart(2, '0');
}

function collectTopColors(raw: Buffer, channels: number): ColorToken[] {
  const frequency = new Map<string, { hex: string; count: number; samples: string[] }>();

  for (let i = 0; i < raw.length; i += channels * 4) {
    const r = channelBucket(raw[i] ?? 0);
    const g = channelBucket(raw[i + 1] ?? 0);
    const b = channelBucket(raw[i + 2] ?? 0);
    const hex = `#${toHex(r)}${toHex(g)}${toHex(b)}`;

    const entry = frequency.get(hex) ?? { hex, count: 0, samples: [] };
    entry.count += 1;
    frequency.set(hex, entry);
  }

  return [...frequency.values()]
    .sort((a, b) => b.count - a.count)
    .slice(0, 30)
    .map((token) => ({
      hex: token.hex,
      count: token.count,
      samples: ['image-palette'],
    }));
}

export async function captureDesignFromImage(params: {
  imagePath: string;
  sourceName: string;
  notes?: string;
  llm?: LlmConfig;
}): Promise<DesignAnalysis> {
  await fs.access(params.imagePath);

  const image = sharp(params.imagePath);
  const metadata = await image.metadata();
  const resized = await image
    .resize({ width: 280, height: 280, fit: 'inside', withoutEnlargement: true })
    .removeAlpha()
    .raw()
    .toBuffer({ resolveWithObject: true });

  const colors = collectTopColors(resized.data, resized.info.channels);

  const base: DesignAnalysis = {
    pageTitle: metadata.format ? `Image source (${metadata.format})` : 'Image source',
    pageUrl: undefined,
    viewport: {
      width: metadata.width ?? 0,
      height: metadata.height ?? 0,
    },
    colors,
    typography: [],
    components: [],
    motion: [],
    layout: [],
    cssVariables: {},
    accessibilitySnapshot: undefined,
  };

  if (!params.llm) {
    return base;
  }

  const vision = await enrichImageWithLlmVision({
    llm: params.llm,
    imagePath: params.imagePath,
    sourceName: params.sourceName,
    notes: params.notes,
  });

  return {
    ...base,
    components: vision.components,
    typography: vision.typography,
    motion: vision.motion,
    layout: vision.layout,
  };
}
