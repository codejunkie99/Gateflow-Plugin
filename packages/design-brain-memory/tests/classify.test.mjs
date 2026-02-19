import test from 'node:test';
import assert from 'node:assert/strict';
import {
  classifyMotionIntent,
  detectPhysics,
  detectAnimationGroups,
  classifyGsapEasing,
} from '../dist/classify.js';

/* ─── classifyMotionIntent ─── */

test('classifyMotionIntent: opacity-only → fade', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { opacity: '0' } },
    { offset: 1, properties: { opacity: '1' } },
  ]);
  assert.equal(result, 'fade');
});

test('classifyMotionIntent: translateX → slide', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'translateX(-100px)' } },
    { offset: 1, properties: { transform: 'translateX(0px)' } },
  ]);
  assert.equal(result, 'slide');
});

test('classifyMotionIntent: translateY → slide', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'translateY(50px)' } },
    { offset: 1, properties: { transform: 'translateY(0px)' } },
  ]);
  assert.equal(result, 'slide');
});

test('classifyMotionIntent: scale → scale', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'scale(0)' } },
    { offset: 1, properties: { transform: 'scale(1)' } },
  ]);
  assert.equal(result, 'scale');
});

test('classifyMotionIntent: rotate → rotate', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { transform: 'rotate(0deg)' } },
    { offset: 1, properties: { transform: 'rotate(360deg)' } },
  ]);
  assert.equal(result, 'rotate');
});

test('classifyMotionIntent: backgroundColor → color-shift', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { backgroundColor: 'rgb(255,0,0)' } },
    { offset: 1, properties: { backgroundColor: 'rgb(0,0,255)' } },
  ]);
  assert.equal(result, 'color-shift');
});

test('classifyMotionIntent: clipPath → reveal', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { clipPath: 'inset(0 100% 0 0)' } },
    { offset: 1, properties: { clipPath: 'inset(0 0 0 0)' } },
  ]);
  assert.equal(result, 'reveal');
});

test('classifyMotionIntent: opacity + translate → complex', () => {
  const result = classifyMotionIntent([
    { offset: 0, properties: { opacity: '0', transform: 'translateY(20px)' } },
    { offset: 1, properties: { opacity: '1', transform: 'translateY(0px)' } },
  ]);
  assert.equal(result, 'complex');
});

test('classifyMotionIntent: empty keyframes → complex', () => {
  const result = classifyMotionIntent([]);
  assert.equal(result, 'complex');
});

/* ─── detectPhysics ─── */

test('detectPhysics: spring oscillation detected', () => {
  const keyframes = [
    { offset: 0, properties: { transform: 'translateX(0px)' } },
    { offset: 0.3, properties: { transform: 'translateX(115px)' } },
    { offset: 0.5, properties: { transform: 'translateX(95px)' } },
    { offset: 0.7, properties: { transform: 'translateX(102px)' } },
    { offset: 1, properties: { transform: 'translateX(100px)' } },
  ];
  const result = detectPhysics(keyframes, 'translateX');
  assert.ok(result);
  assert.equal(result.type, 'spring');
  assert.ok(result.oscillationCount >= 2);
  assert.ok(result.overshootPercent > 0);
});

test('detectPhysics: bounce detected (single overshoot)', () => {
  const keyframes = [
    { offset: 0, properties: { transform: 'translateY(0px)' } },
    { offset: 0.5, properties: { transform: 'translateY(110px)' } },
    { offset: 1, properties: { transform: 'translateY(100px)' } },
  ];
  const result = detectPhysics(keyframes, 'translateY');
  assert.ok(result);
  assert.equal(result.type, 'bounce');
});

test('detectPhysics: linear motion returns null', () => {
  const keyframes = [
    { offset: 0, properties: { transform: 'translateX(0px)' } },
    { offset: 0.5, properties: { transform: 'translateX(50px)' } },
    { offset: 1, properties: { transform: 'translateX(100px)' } },
  ];
  const result = detectPhysics(keyframes, 'translateX');
  assert.equal(result, null);
});

/* ─── classifyGsapEasing ─── */

test('classifyGsapEasing: elastic → spring', () => {
  const result = classifyGsapEasing('elastic.out(1, 0.3)');
  assert.ok(result);
  assert.equal(result.type, 'spring');
});

test('classifyGsapEasing: bounce → bounce', () => {
  const result = classifyGsapEasing('bounce.out');
  assert.ok(result);
  assert.equal(result.type, 'bounce');
});

test('classifyGsapEasing: back → spring', () => {
  const result = classifyGsapEasing('back.out(1.7)');
  assert.ok(result);
  assert.equal(result.type, 'spring');
});

test('classifyGsapEasing: power1 → null (not physics)', () => {
  const result = classifyGsapEasing('power1.out');
  assert.equal(result, null);
});

/* ─── detectAnimationGroups ─── */

test('detectAnimationGroups: staggered elements grouped', () => {
  const tokens = [
    {
      selector: '.item-1', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 0, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
    {
      selector: '.item-2', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 100, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
    {
      selector: '.item-3', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 200, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
  ];

  const result = detectAnimationGroups(tokens);
  assert.equal(result.length, 3);
  assert.equal(result[0].group.role, 'lead');
  assert.equal(result[1].group.role, 'follower');
  assert.equal(result[1].group.staggerDelay, 100);
  assert.equal(result[2].group.role, 'follower');
  assert.equal(result[2].group.staggerDelay, 200);
  assert.equal(result[0].group.groupId, result[1].group.groupId);
});

test('detectAnimationGroups: unrelated animations not grouped', () => {
  const tokens = [
    {
      selector: '.a', library: 'css', motionIntent: 'fade', trigger: 'load',
      timing: { duration: 300, delay: 0, easing: 'ease-out', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { opacity: '0' } }, { offset: 1, properties: { opacity: '1' } }],
    },
    {
      selector: '.b', library: 'gsap', motionIntent: 'slide', trigger: 'hover',
      timing: { duration: 600, delay: 0, easing: 'ease-in', iterations: 1, direction: 'normal', fillMode: 'none' },
      keyframes: [{ offset: 0, properties: { transform: 'translateX(0)' } }, { offset: 1, properties: { transform: 'translateX(100px)' } }],
    },
  ];

  const result = detectAnimationGroups(tokens);
  assert.equal(result.length, 2);
  assert.equal(result[0].group, undefined);
  assert.equal(result[1].group, undefined);
});
