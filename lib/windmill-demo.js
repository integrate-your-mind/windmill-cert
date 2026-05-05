export const VIEWBOX_SIZE = 920;
export const PADDING = 92;
export const FRAME_DURATION_MS = 14000;

export function lineAngle(from, to) {
  let angle = Math.atan2(to.y - from.y, to.x - from.x) % Math.PI;
  if (angle < 0) {
    angle += Math.PI;
  }
  return angle;
}

export function angleDelta(currentAngle, nextAngle) {
  return (nextAngle - currentAngle + Math.PI) % Math.PI;
}

export function normalizeProgress(progress) {
  return ((progress % 1) + 1) % 1;
}

export function pointBounds(points) {
  if (!points.length) {
    throw new Error("Expected at least one point.");
  }

  const xs = points.map((point) => point.x);
  const ys = points.map((point) => point.y);

  return {
    minX: Math.min(...xs),
    maxX: Math.max(...xs),
    minY: Math.min(...ys),
    maxY: Math.max(...ys),
  };
}

export function createLayout(points, size = VIEWBOX_SIZE, padding = PADDING) {
  const bounds = pointBounds(points);
  const rawWidth = bounds.maxX - bounds.minX;
  const rawHeight = bounds.maxY - bounds.minY;
  const width = Math.max(rawWidth, 1);
  const height = Math.max(rawHeight, 1);
  const usable = size - padding * 2;
  const scale = Math.min(usable / width, usable / height);
  const extraX = usable - rawWidth * scale;
  const extraY = usable - rawHeight * scale;

  return {
    bounds,
    scale,
    offsetX: padding + extraX / 2,
    offsetY: padding + extraY / 2,
    size,
    padding,
  };
}

export function projectPoint(point, layout) {
  return {
    x: layout.offsetX + (point.x - layout.bounds.minX) * layout.scale,
    y:
      layout.size -
      (layout.offsetY + (point.y - layout.bounds.minY) * layout.scale),
  };
}

function dedupePoints(points) {
  return points.filter((point, index) => {
    return (
      index ===
      points.findIndex(
        (candidate) =>
          Math.abs(candidate.x - point.x) < 0.001 &&
          Math.abs(candidate.y - point.y) < 0.001,
      )
    );
  });
}

function canonicalSegment(start, end) {
  if (start.x < end.x) {
    return { start, end };
  }
  if (start.x > end.x) {
    return { start: end, end: start };
  }
  if (start.y <= end.y) {
    return { start, end };
  }
  return { start: end, end: start };
}

export function clipLineToFrame(origin, theta, size = VIEWBOX_SIZE, inset = 28) {
  const dirX = Math.cos(theta);
  const dirY = -Math.sin(theta);
  const min = inset;
  const max = size - inset;
  const candidates = [];

  if (Math.abs(dirX) > 1e-8) {
    for (const edgeX of [min, max]) {
      const t = (edgeX - origin.x) / dirX;
      const y = origin.y + t * dirY;
      if (y >= min - 0.001 && y <= max + 0.001) {
        candidates.push({ x: edgeX, y, t });
      }
    }
  }

  if (Math.abs(dirY) > 1e-8) {
    for (const edgeY of [min, max]) {
      const t = (edgeY - origin.y) / dirY;
      const x = origin.x + t * dirX;
      if (x >= min - 0.001 && x <= max + 0.001) {
        candidates.push({ x, y: edgeY, t });
      }
    }
  }

  const unique = dedupePoints(candidates).sort((left, right) => left.t - right.t);
  if (unique.length >= 2) {
    return canonicalSegment(
      { x: unique[0].x, y: unique[0].y },
      { x: unique[unique.length - 1].x, y: unique[unique.length - 1].y },
    );
  }

  const fallbackLength = size * 0.84;
  return canonicalSegment(
    {
      x: origin.x - dirX * fallbackLength,
      y: origin.y - dirY * fallbackLength,
    },
    {
      x: origin.x + dirX * fallbackLength,
      y: origin.y + dirY * fallbackLength,
    },
  );
}

export function labelPlacement(projectedPoint, center, size = VIEWBOX_SIZE, inset = 44) {
  const dx = projectedPoint.x - center.x;
  const dy = projectedPoint.y - center.y;
  const length = Math.hypot(dx, dy) || 1;
  const preferredX = projectedPoint.x + (dx / length) * 28 + (dx >= 0 ? 10 : -10);
  const preferredY = projectedPoint.y + (dy / length) * 24 + (dy >= 0 ? 18 : -16);
  const clampedX = Math.min(size - inset, Math.max(inset, preferredX));
  const clampedY = Math.min(size - inset, Math.max(inset, preferredY));
  let anchor = clampedX >= projectedPoint.x ? "start" : "end";
  let finalY = clampedY - projectedPoint.y;

  if (clampedX >= size - inset - 16) {
    anchor = "end";
  } else if (clampedX <= inset + 16) {
    anchor = "start";
  }

  if (clampedY >= size - inset - 16) {
    finalY = -18;
  } else if (clampedY <= inset + 16) {
    finalY = 22;
  }

  return {
    x: clampedX - projectedPoint.x,
    y: finalY,
    anchor,
  };
}

export function buildFrame(points, cycle, progress) {
  if (!cycle.length) {
    throw new Error("Expected a non-empty windmill cycle.");
  }

  const layout = createLayout(points);
  const normalized = normalizeProgress(progress);
  const scaled = normalized * cycle.length;
  const stepIndex = Math.floor(scaled) % cycle.length;
  const localProgress = scaled - Math.floor(scaled);
  const state = cycle[stepIndex];
  const next = cycle[(stepIndex + 1) % cycle.length];
  const pivot = points[state.curr];
  const currentAngle = lineAngle(pivot, points[state.prev]);
  const nextAngle = lineAngle(pivot, points[next.curr]);
  const theta = (currentAngle + angleDelta(currentAngle, nextAngle) * localProgress) % Math.PI;
  const projectedPoints = points.map((point) => projectPoint(point, layout));
  const pivotPixel = projectedPoints[state.curr];
  const center = projectedPoints.reduce(
    (acc, point) => ({ x: acc.x + point.x, y: acc.y + point.y }),
    { x: 0, y: 0 },
  );
  center.x /= projectedPoints.length;
  center.y /= projectedPoints.length;

  return {
    layout,
    projectedPoints,
    center,
    state,
    next,
    stepIndex,
    localProgress,
    line: clipLineToFrame(pivotPixel, theta, layout.size, layout.padding / 2),
  };
}

export function formatProgressPercent(progress) {
  return `${Math.round(normalizeProgress(progress) * 100)}%`;
}
