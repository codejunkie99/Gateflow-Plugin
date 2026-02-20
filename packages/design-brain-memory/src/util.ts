import path from 'node:path';
import crypto from 'node:crypto';

export function nowIso(): string {
  return new Date().toISOString();
}

export function slugify(value: string): string {
  return value
    .toLowerCase()
    .trim()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/(^-|-$)/g, '')
    .slice(0, 64);
}

export function makeId(prefix: string, input: string): string {
  const slug = slugify(input);
  const hash = crypto.createHash('sha1').update(`${input}:${Date.now()}:${Math.random()}`).digest('hex').slice(0, 8);
  return `${prefix}-${slug || 'item'}-${hash}`;
}

export function unique<T>(items: T[]): T[] {
  return [...new Set(items)];
}

export function relPath(from: string, to: string): string {
  const relative = path.relative(from, to);
  return relative.startsWith('.') ? relative : `./${relative}`;
}

export function truncate(text: string, max = 120): string {
  if (text.length <= max) {
    return text;
  }
  return `${text.slice(0, max - 1)}...`;
}

export function csvEscape(value: string): string {
  if (value.includes(',') || value.includes('"') || value.includes('\n')) {
    return `"${value.replace(/"/g, '""')}"`;
  }
  return value;
}

export function stableHash(input: string): string {
  return crypto.createHash('sha1').update(input).digest('hex');
}

export function normalizeUrl(input: string): string {
  try {
    const parsed = new URL(input);
    parsed.hash = '';
    return parsed.toString();
  } catch {
    return input.trim();
  }
}
