import test from "node:test";
import assert from "node:assert/strict";

import {
  angleDelta,
  buildFrame,
  clipLineToFrame,
  createLayout,
  normalizeProgress,
  projectPoint,
} from "../../lib/windmill-demo.js";

test("normalizeProgress wraps negative and large values", () => {
  assert.equal(normalizeProgress(-0.25), 0.75);
  assert.equal(normalizeProgress(1.25), 0.25);
});

test("projectPoint handles degenerate spans", () => {
  const point = projectPoint(
    { x: 4, y: 4 },
    createLayout([{ x: 4, y: 4 }], 200, 20),
  );
  assert.equal(point.x, 100);
  assert.equal(point.y, 100);
});

test("angleDelta keeps motion in the next half-turn", () => {
  assert.equal(angleDelta(0.9 * Math.PI, 0.1 * Math.PI), 0.2 * Math.PI);
});

test("buildFrame resolves the expected step and pivot", () => {
  const points = [
    { x: 0, y: 0 },
    { x: 4, y: 0 },
    { x: 0, y: 3 },
  ];
  const cycle = [
    { prev: 0, curr: 1 },
    { prev: 1, curr: 2 },
    { prev: 2, curr: 0 },
  ];

  const frame = buildFrame(points, cycle, 0.4);
  assert.equal(frame.stepIndex, 1);
  assert.deepEqual(frame.state, cycle[1]);
  assert.deepEqual(frame.next, cycle[2]);
});

test("clipLineToFrame keeps the line inside the viewbox", () => {
  const line = clipLineToFrame({ x: 100, y: 100 }, Math.PI / 4, 200, 20);
  for (const point of [line.start, line.end]) {
    assert.ok(point.x >= 19.999 && point.x <= 180.001);
    assert.ok(point.y >= 19.999 && point.y <= 180.001);
  }
});
