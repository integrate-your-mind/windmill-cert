from __future__ import annotations

from dataclasses import asdict, dataclass
from functools import cmp_to_key
from itertools import combinations
import json
import math
from pathlib import Path
from random import Random
from typing import Callable, Iterable, Iterator, Sequence

from PIL import Image, ImageDraw, ImageFont


@dataclass(frozen=True, order=True)
class Point:
    x: int
    y: int


@dataclass(frozen=True)
class State:
    prev: int
    curr: int


@dataclass(frozen=True)
class Case:
    strategy: str
    size: int
    seed_tag: str
    points: tuple[Point, ...]


def area2(a: Point, b: Point, c: Point) -> int:
    return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)


def canonical_direction(a: Point, b: Point) -> tuple[int, int]:
    dx = b.x - a.x
    dy = b.y - a.y
    if dy < 0 or (dy == 0 and dx < 0):
        return (-dx, -dy)
    return (dx, dy)


def direction_cmp(u: tuple[int, int], v: tuple[int, int]) -> int:
    cross = u[0] * v[1] - u[1] * v[0]
    if cross == 0:
        raise ValueError("Degenerate direction comparison: two directions coincide.")
    return -1 if cross > 0 else 1


def line_angle_mod_pi(a: Point, b: Point) -> float:
    angle = math.atan2(b.y - a.y, b.x - a.x) % math.pi
    if math.isclose(angle, math.pi, abs_tol=1e-12):
        return 0.0
    return angle


def check_general_position(points: Iterable[Point]) -> tuple[Point, ...]:
    items = tuple(points)
    if len(items) < 2:
        raise ValueError("Need at least two points.")
    if len(set(items)) != len(items):
        raise ValueError("Duplicate points are not allowed.")
    for i in range(len(items)):
        for j in range(i + 1, len(items)):
            for k in range(j + 1, len(items)):
                if area2(items[i], items[j], items[k]) == 0:
                    raise ValueError("Input must satisfy: no three points are collinear.")
    return items


def no_three_collinear(points: Sequence[Point]) -> bool:
    for i, j, k in combinations(range(len(points)), 3):
        if area2(points[i], points[j], points[k]) == 0:
            return False
    return True


def order_around_pivot(points: tuple[Point, ...], pivot: int) -> list[int]:
    if not 0 <= pivot < len(points):
        raise IndexError("Pivot index out of range.")
    return sorted(
        [idx for idx in range(len(points)) if idx != pivot],
        key=cmp_to_key(
            lambda i, j: direction_cmp(
                canonical_direction(points[pivot], points[i]),
                canonical_direction(points[pivot], points[j]),
            )
        ),
    )


def next_state(points: tuple[Point, ...], state: State) -> State:
    if state.prev == state.curr:
        raise ValueError("State must contain two distinct points.")
    if len(points) == 2:
        return State(state.curr, state.prev)

    order = order_around_pivot(points, state.curr)
    position = order.index(state.prev)
    return State(state.curr, order[(position + 1) % len(order)])


def orbit_from(
    points: tuple[Point, ...], start: State
) -> tuple[list[State], int, list[State]]:
    seen: dict[State, int] = {}
    sequence: list[State] = []
    state = start
    while state not in seen:
        seen[state] = len(sequence)
        sequence.append(state)
        state = next_state(points, state)
    cycle_start = seen[state]
    return sequence, cycle_start, sequence[cycle_start:]


def coverage_witnesses(cycle: list[State], point_count: int) -> list[int]:
    witnesses = [-1] * point_count
    for index, state in enumerate(cycle):
        if witnesses[state.curr] == -1:
            witnesses[state.curr] = index
    if any(index == -1 for index in witnesses):
        raise ValueError("Cycle does not hit every point.")
    return witnesses


def certify_start(points: tuple[Point, ...], start: State) -> dict[str, object]:
    sequence, mu, cycle = orbit_from(points, start)
    pivots = {state.curr for state in cycle}
    works = len(pivots) == len(points)
    result: dict[str, object] = {
        "works": works,
        "preperiod_length": mu,
        "cycle_length": len(cycle),
        "cycle": cycle,
        "sequence": sequence,
        "cycle_pivots": sorted(pivots),
    }
    if works:
        result["cover"] = coverage_witnesses(cycle, len(points))
    return result


def find_any_certifying_start(points: tuple[Point, ...]) -> tuple[State, dict[str, object]]:
    for prev in range(len(points)):
        for curr in range(len(points)):
            if prev == curr:
                continue
            start = State(prev, curr)
            cert = certify_start(points, start)
            if cert["works"]:
                return start, cert
    raise RuntimeError("No certifying start found.")


def certify_instance(points: Sequence[Point]) -> tuple[bool, list[State] | None]:
    items = check_general_position(points)
    try:
        _, cert = find_any_certifying_start(items)
    except RuntimeError:
        return False, None
    cycle = cert["cycle"]
    assert isinstance(cycle, list)
    return bool(cert["works"]), cycle


def balanced_targets(total_points: int) -> set[tuple[int, int]]:
    if total_points % 2 == 1:
        half = (total_points - 1) // 2
        return {(half, half)}
    half = total_points // 2
    return {(half - 1, half), (half, half - 1)}


def side_counts_after_switch(points: tuple[Point, ...], state: State) -> tuple[int, int]:
    nxt = next_state(points, state)
    pivot = points[state.curr]
    current_angle = line_angle_mod_pi(pivot, points[state.prev])
    next_angle = line_angle_mod_pi(pivot, points[nxt.curr])
    delta = (next_angle - current_angle) % math.pi
    if math.isclose(delta, 0.0, abs_tol=1e-12):
        raise ValueError("Degenerate step: consecutive lines coincide.")
    theta = (current_angle + delta / 2.0) % math.pi
    dx = math.cos(theta)
    dy = math.sin(theta)
    left = 0
    right = 0
    for index, point in enumerate(points):
        if index == state.curr:
            continue
        sign = dx * (point.y - pivot.y) - dy * (point.x - pivot.x)
        if sign > 0:
            left += 1
        elif sign < 0:
            right += 1
        else:
            raise RuntimeError("Unexpected collinearity in side count computation.")
    return left, right


def find_balanced_certifying_state(
    points: tuple[Point, ...],
) -> tuple[State, tuple[int, int], dict[str, object]] | None:
    targets = balanced_targets(len(points))
    for prev in range(len(points)):
        for curr in range(len(points)):
            if prev == curr:
                continue
            state = State(prev, curr)
            counts = side_counts_after_switch(points, state)
            if counts not in targets:
                continue
            cert = certify_start(points, state)
            if cert["works"]:
                return state, counts, cert
    return None


def affine_transform(
    points: Iterable[Point],
    matrix: tuple[int, int, int, int],
    translation: tuple[int, int],
) -> tuple[Point, ...]:
    a, b, c, d = matrix
    tx, ty = translation
    return tuple(Point(a * p.x + b * p.y + tx, c * p.x + d * p.y + ty) for p in points)


def generate_convex_case(count: int, rng: Random) -> tuple[Point, ...]:
    if count < 3:
        raise ValueError("Convex cases need at least three points.")
    attempts = 0
    while True:
        attempts += 1
        xs = sorted(rng.sample(range(-4 * count, 4 * count + 1), count))
        base = [Point(x, x * x) for x in xs]
        while True:
            matrix = (
                rng.randint(-3, 3),
                rng.randint(-2, 2),
                rng.randint(-2, 2),
                rng.randint(-3, 3),
            )
            det = matrix[0] * matrix[3] - matrix[1] * matrix[2]
            if det != 0:
                break
        transformed = affine_transform(
            base,
            matrix=matrix,
            translation=(rng.randint(-40, 40), rng.randint(-40, 40)),
        )
        try:
            return check_general_position(transformed)
        except ValueError:
            if attempts > 200:
                raise


def random_distinct_ints(rng: Random, count: int, lo: int, hi: int) -> list[int]:
    if hi - lo + 1 < count:
        raise ValueError("Range too small for a distinct sample.")
    return rng.sample(range(lo, hi + 1), count)


def generate_parabola_case(rng: Random, count: int, xspan: int = 60) -> tuple[Point, ...]:
    xs = sorted(random_distinct_ints(rng, count, -xspan, xspan))
    a = rng.randint(-10, 10)
    b = rng.randint(-100, 100)
    return check_general_position(Point(x, x * x + a * x + b) for x in xs)


def generate_two_chain_case(
    rng: Random, count: int, xspan: int = 60, gap: int = 4000
) -> tuple[Point, ...]:
    xs = sorted(random_distinct_ints(rng, count, -xspan, xspan))
    split = rng.randint(1, count - 1)
    points: list[Point] = []
    for index, x in enumerate(xs):
        if index < split:
            points.append(Point(x, x * x))
        else:
            points.append(Point(x, gap - x * x))
    if no_three_collinear(points):
        return tuple(points)
    return generate_two_chain_case(rng, count, xspan=xspan, gap=gap + 1)


def generate_grid_case(count: int, rng: Random) -> tuple[Point, ...]:
    attempts = 0
    while True:
        attempts += 1
        points = tuple(
            Point(rng.randint(-60, 60), rng.randint(-60, 60)) for _ in range(count)
        )
        try:
            return check_general_position(points)
        except ValueError:
            if attempts > 400:
                raise


def generate_cluster_case(count: int, rng: Random) -> tuple[Point, ...]:
    attempts = 0
    while True:
        attempts += 1
        cluster_count = 2 if count < 7 else 3
        centers = [
            Point(rng.randint(-50, 50), rng.randint(-50, 50))
            for _ in range(cluster_count)
        ]
        points: list[Point] = []
        for _ in range(count):
            center = centers[rng.randrange(len(centers))]
            points.append(
                Point(
                    center.x + rng.randint(-12, 12),
                    center.y + rng.randint(-12, 12),
                )
            )
        try:
            return check_general_position(points)
        except ValueError:
            if attempts > 400:
                raise


def generate_near_collinear_case(
    rng: Random, count: int, xspan: int = 100
) -> tuple[Point, ...]:
    xs = sorted(random_distinct_ints(rng, count, -xspan, xspan))
    slope = rng.randint(-7, 7)
    intercept = rng.randint(-200, 200)
    noise = rng.sample(range(-8 * count, 8 * count + 1), count)
    points = tuple(
        Point(x, slope * x + intercept + noise[index]) for index, x in enumerate(xs)
    )
    if no_three_collinear(points):
        return points
    return generate_near_collinear_case(rng, count, xspan=xspan)


def generate_mixed_case(count: int, rng: Random) -> tuple[Point, ...]:
    if count < 5:
        raise ValueError("Mixed cases need at least five points.")
    attempts = 0
    while True:
        attempts += 1
        hull_count = max(4, count // 2 + 1)
        hull = list(generate_convex_case(hull_count, rng))
        center_x = sum(point.x for point in hull) // len(hull)
        center_y = sum(point.y for point in hull) // len(hull)
        points = hull[:]
        for _ in range(count - hull_count):
            points.append(
                Point(
                    center_x + rng.randint(-14, 14),
                    center_y + rng.randint(-14, 14),
                )
            )
        rng.shuffle(points)
        try:
            return check_general_position(points)
        except ValueError:
            if attempts > 400:
                raise


GENERATORS: dict[str, Callable[[int, Random], tuple[Point, ...]]] = {
    "convex": generate_convex_case,
    "grid": generate_grid_case,
    "cluster": generate_cluster_case,
    "mixed": generate_mixed_case,
}


STRESS_FAMILIES: tuple[tuple[str, Callable[[Random, int], tuple[Point, ...]]], ...] = (
    ("parabola", generate_parabola_case),
    ("two_chain", generate_two_chain_case),
    ("random_grid", lambda rng, count: generate_grid_case(count, rng)),
    ("near_collinear", generate_near_collinear_case),
    ("clustered", lambda rng, count: generate_cluster_case(count, rng)),
)


def exhaustive_grid_cases(width: int, height: int, count: int) -> Iterator[tuple[Point, ...]]:
    grid = tuple(Point(x, y) for x in range(width) for y in range(height))
    for combo in combinations(grid, count):
        if no_three_collinear(combo):
            yield combo


def generate_cases(
    *,
    seed: int,
    sizes: Iterable[int],
    cases_per_strategy: int,
) -> list[Case]:
    rng = Random(seed)
    cases: list[Case] = []
    for strategy, generator in GENERATORS.items():
        for size in sizes:
            for index in range(cases_per_strategy):
                cases.append(
                    Case(
                        strategy=strategy,
                        size=size,
                        seed_tag=f"{seed}:{strategy}:{size}:{index}",
                        points=generator(size, rng),
                    )
                )
    return cases


def pick_demo_case(seed: int = 20260422) -> tuple[Case, State, tuple[int, int], dict[str, object]]:
    rng = Random(seed)
    for strategy in ("mixed", "cluster", "convex", "grid"):
        generator = GENERATORS[strategy]
        for index in range(200):
            points = generator(7, rng)
            case = Case(
                strategy=strategy,
                size=len(points),
                seed_tag=f"demo:{strategy}:{index}",
                points=points,
            )
            balanced = find_balanced_certifying_state(points)
            if balanced is not None:
                state, counts, cert = balanced
                cycle = cert["cycle"]
                assert isinstance(cycle, list)
                for candidate in cycle:
                    state_counts = side_counts_after_switch(points, candidate)
                    if state_counts in balanced_targets(len(points)):
                        cycle_cert = certify_start(points, candidate)
                        if cycle_cert["works"]:
                            return case, candidate, state_counts, cycle_cert
                return case, state, counts, cert
    raise RuntimeError("Could not find a demo case with a balanced certifying state.")


def summarize_case(case: Case) -> dict[str, object]:
    start, cert = find_any_certifying_start(case.points)
    balanced = find_balanced_certifying_state(case.points)
    summary: dict[str, object] = {
        "strategy": case.strategy,
        "size": case.size,
        "seed_tag": case.seed_tag,
        "start": asdict(start),
        "cycle_length": cert["cycle_length"],
        "preperiod_length": cert["preperiod_length"],
        "works": cert["works"],
    }
    if balanced is not None:
        state, counts, _ = balanced
        summary["balanced_start"] = asdict(state)
        summary["balanced_counts"] = list(counts)
    return summary


def summarize_suite(cases: Iterable[Case]) -> dict[str, object]:
    summaries = [summarize_case(case) for case in cases]
    return {
        "case_count": len(summaries),
        "all_certified": all(summary["works"] for summary in summaries),
        "summaries": summaries,
    }


def stress_test(
    *,
    max_n: int = 10,
    exhaustive_grid_size: tuple[int, int] = (4, 4),
    exhaustive_up_to_n: int = 6,
    random_cases_per_family: int = 300,
    seed: int = 0,
) -> dict[str, object]:
    rng = Random(seed)
    total_tested = 0
    width, height = exhaustive_grid_size

    for count in range(2, max_n + 1):
        if count <= exhaustive_up_to_n:
            for points in exhaustive_grid_cases(width, height, count):
                total_tested += 1
                ok, cycle = certify_instance(points)
                if not ok:
                    return {
                        "ok": False,
                        "mode": "exhaustive_grid",
                        "n": count,
                        "points": as_jsonable_points(points),
                        "cycle": as_jsonable_states(cycle or []),
                        "tested": total_tested,
                    }

        for family_name, generator in STRESS_FAMILIES:
            for _ in range(random_cases_per_family):
                points = generator(rng, count)
                total_tested += 1
                ok, cycle = certify_instance(points)
                if not ok:
                    return {
                        "ok": False,
                        "mode": family_name,
                        "n": count,
                        "points": as_jsonable_points(points),
                        "cycle": as_jsonable_states(cycle or []),
                        "tested": total_tested,
                    }

    return {
        "ok": True,
        "tested": total_tested,
        "max_n": max_n,
        "exhaustive_grid_size": list(exhaustive_grid_size),
        "exhaustive_up_to_n": exhaustive_up_to_n,
        "random_cases_per_family": random_cases_per_family,
        "seed": seed,
    }


def as_jsonable_points(points: Iterable[Point]) -> list[dict[str, int]]:
    return [asdict(point) for point in points]


def as_jsonable_states(states: Iterable[State]) -> list[dict[str, int]]:
    return [asdict(state) for state in states]


def write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def render_gif(
    points: tuple[Point, ...],
    cycle: list[State],
    destination: Path,
    *,
    frame_size: int = 640,
    subframes: int = 10,
    hold_frames: int = 6,
) -> None:
    padding = 56
    min_x = min(point.x for point in points)
    max_x = max(point.x for point in points)
    min_y = min(point.y for point in points)
    max_y = max(point.y for point in points)
    span_x = max(max_x - min_x, 1)
    span_y = max(max_y - min_y, 1)
    usable = frame_size - 2 * padding
    scale = min(usable / span_x, usable / span_y)
    font = ImageFont.load_default()

    def to_pixel(point: Point) -> tuple[float, float]:
        x = padding + (point.x - min_x) * scale
        y = frame_size - (padding + (point.y - min_y) * scale)
        return x, y

    def draw_frame(state: State, nxt: State, theta: float, highlight_next: bool) -> Image.Image:
        image = Image.new("RGB", (frame_size, frame_size), "#fffaf0")
        draw = ImageDraw.Draw(image)
        for i in range(5):
            inset = padding - 20 + i * 5
            draw.rounded_rectangle(
                [inset, inset, frame_size - inset, frame_size - inset],
                radius=18,
                outline=(240 - i * 8, 224 - i * 5, 200 - i * 3),
            )

        pivot = points[state.curr]
        pivot_xy = to_pixel(pivot)
        direction = (math.cos(theta), math.sin(theta))
        line_length = frame_size * 0.8
        x1 = pivot_xy[0] - direction[0] * line_length
        y1 = pivot_xy[1] + direction[1] * line_length
        x2 = pivot_xy[0] + direction[0] * line_length
        y2 = pivot_xy[1] - direction[1] * line_length
        draw.line((x1, y1, x2, y2), fill="#105f5f", width=5)

        for index, point in enumerate(points):
            x, y = to_pixel(point)
            radius = 7
            fill = "#273043"
            outline = "#ffffff"
            if index == state.curr:
                radius = 11
                fill = "#c1121f"
            elif index == nxt.curr and highlight_next:
                radius = 11
                fill = "#fca311"
            draw.ellipse((x - radius, y - radius, x + radius, y + radius), fill=fill, outline=outline, width=2)
            draw.text((x + 10, y - 10), str(index), fill="#111827", font=font)

        draw.text(
            (padding - 8, 18),
            f"cycle step {cycle.index(state) + 1}/{len(cycle)} | pivot {state.curr} -> next {nxt.curr}",
            fill="#111827",
            font=font,
        )
        return image

    frames: list[Image.Image] = []
    for index, state in enumerate(cycle):
        nxt = cycle[(index + 1) % len(cycle)]
        current_angle = line_angle_mod_pi(points[state.curr], points[state.prev])
        next_angle = line_angle_mod_pi(points[state.curr], points[nxt.curr])
        delta = (next_angle - current_angle) % math.pi
        for subframe in range(subframes):
            fraction = subframe / max(subframes - 1, 1)
            theta = (current_angle + delta * fraction) % math.pi
            frames.append(draw_frame(state, nxt, theta, highlight_next=subframe == subframes - 1))
    for _ in range(hold_frames):
        frames.append(frames[-1].copy())
    frames[0].save(
        destination,
        save_all=True,
        append_images=frames[1:],
        optimize=False,
        duration=85,
        loop=0,
    )


def render_html(points: tuple[Point, ...], cycle: list[State], destination: Path) -> None:
    payload = {
        "points": as_jsonable_points(points),
        "cycle": as_jsonable_states(cycle),
    }
    destination.write_text(
        f"""<!doctype html>
<html lang="en">
<meta charset="utf-8">
<title>Windmill Demo</title>
<style>
  :root {{
    --paper: #fffaf0;
    --ink: #132238;
    --teal: #105f5f;
    --pivot: #c1121f;
    --next: #fca311;
    --dot: #273043;
  }}
  * {{ box-sizing: border-box; }}
  body {{
    margin: 0;
    font-family: ui-monospace, "SFMono-Regular", Menlo, monospace;
    background:
      radial-gradient(circle at top left, rgba(252, 163, 17, 0.12), transparent 35%),
      linear-gradient(180deg, #fffdf6 0%, #f7f0e5 100%);
    color: var(--ink);
    min-height: 100vh;
    display: grid;
    place-items: center;
    padding: 24px;
  }}
  .panel {{
    width: min(900px, 100%);
    background: rgba(255, 250, 240, 0.92);
    border: 1px solid rgba(19, 34, 56, 0.1);
    border-radius: 24px;
    box-shadow: 0 20px 60px rgba(19, 34, 56, 0.15);
    overflow: hidden;
  }}
  header {{
    padding: 18px 20px;
    border-bottom: 1px solid rgba(19, 34, 56, 0.08);
    display: flex;
    justify-content: space-between;
    gap: 12px;
    flex-wrap: wrap;
  }}
  canvas {{
    width: 100%;
    display: block;
    aspect-ratio: 1 / 1;
    background: var(--paper);
  }}
  .controls {{
    display: flex;
    gap: 12px;
    align-items: center;
    padding: 16px 20px 22px;
    flex-wrap: wrap;
  }}
  button {{
    border: 0;
    border-radius: 999px;
    padding: 10px 16px;
    background: var(--ink);
    color: white;
    font: inherit;
    cursor: pointer;
  }}
  input[type="range"] {{ flex: 1 1 220px; }}
</style>
<div class="panel">
  <header>
    <strong>Windmill cycle viewer</strong>
    <span id="status"></span>
  </header>
  <canvas id="view" width="900" height="900"></canvas>
  <div class="controls">
    <button id="toggle">Pause</button>
    <input id="slider" type="range" min="0" max="1" step="0.001" value="0">
  </div>
</div>
<script>
const DATA = {json.dumps(payload)};
const canvas = document.getElementById("view");
const ctx = canvas.getContext("2d");
const status = document.getElementById("status");
const slider = document.getElementById("slider");
const toggle = document.getElementById("toggle");
const points = DATA.points;
const cycle = DATA.cycle;
const padding = 80;
const minX = Math.min(...points.map(p => p.x));
const maxX = Math.max(...points.map(p => p.x));
const minY = Math.min(...points.map(p => p.y));
const maxY = Math.max(...points.map(p => p.y));
const scale = Math.min((canvas.width - padding * 2) / Math.max(maxX - minX, 1), (canvas.height - padding * 2) / Math.max(maxY - minY, 1));
let playing = true;

function toPixel(point) {{
  return {{
    x: padding + (point.x - minX) * scale,
    y: canvas.height - (padding + (point.y - minY) * scale)
  }};
}}

function lineAngle(a, b) {{
  let angle = Math.atan2(b.y - a.y, b.x - a.x) % Math.PI;
  if (angle < 0) angle += Math.PI;
  return angle;
}}

function draw(progress) {{
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = "#fffaf0";
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  const scaled = progress * cycle.length;
  const step = Math.floor(scaled) % cycle.length;
  const t = scaled - Math.floor(scaled);
  const state = cycle[step];
  const next = cycle[(step + 1) % cycle.length];
  const pivot = points[state.curr];
  const currentAngle = lineAngle(pivot, points[state.prev]);
  const nextAngle = lineAngle(pivot, points[next.curr]);
  const delta = (nextAngle - currentAngle + Math.PI) % Math.PI;
  const theta = (currentAngle + delta * t) % Math.PI;
  const pivotPixel = toPixel(pivot);
  const dx = Math.cos(theta);
  const dy = Math.sin(theta);
  const lineLength = canvas.width * 0.78;

  ctx.strokeStyle = "#105f5f";
  ctx.lineWidth = 6;
  ctx.beginPath();
  ctx.moveTo(pivotPixel.x - dx * lineLength, pivotPixel.y + dy * lineLength);
  ctx.lineTo(pivotPixel.x + dx * lineLength, pivotPixel.y - dy * lineLength);
  ctx.stroke();

  points.forEach((point, index) => {{
    const pixel = toPixel(point);
    let radius = 10;
    let fill = "#273043";
    if (index === state.curr) {{
      radius = 15;
      fill = "#c1121f";
    }} else if (index === next.curr && t > 0.85) {{
      radius = 15;
      fill = "#fca311";
    }}
    ctx.fillStyle = fill;
    ctx.beginPath();
    ctx.arc(pixel.x, pixel.y, radius, 0, Math.PI * 2);
    ctx.fill();
    ctx.strokeStyle = "white";
    ctx.lineWidth = 3;
    ctx.stroke();
    ctx.fillStyle = "#132238";
    ctx.font = '22px ui-monospace, SFMono-Regular, Menlo, monospace';
    ctx.fillText(String(index), pixel.x + 16, pixel.y - 12);
  }});

  status.textContent = `step ${{step + 1}}/${{cycle.length}} | pivot ${{state.curr}} -> next ${{next.curr}}`;
}}

let start = performance.now();
function frame(now) {{
  if (playing) {{
    const progress = ((now - start) / 1400) % 1;
    slider.value = progress.toFixed(3);
    draw(progress);
  }}
  requestAnimationFrame(frame);
}}

slider.addEventListener("input", () => {{
  playing = false;
  toggle.textContent = "Play";
  draw(Number(slider.value));
}});

toggle.addEventListener("click", () => {{
  playing = !playing;
  toggle.textContent = playing ? "Pause" : "Play";
  start = performance.now() - Number(slider.value) * 1400;
}});

draw(0);
requestAnimationFrame(frame);
</script>
</html>
""",
        encoding="utf-8",
    )


def lean_point_literal(point: Point) -> str:
    return f"{{ x := {point.x}, y := {point.y} }}"


def lean_state_literal(state: State) -> str:
    return f"{{ prev := {state.prev}, curr := {state.curr} }}"


def write_lean_certificate(
    points: tuple[Point, ...],
    cycle: list[State],
    cover: list[int],
    destination: Path,
    *,
    name: str = "exported",
) -> None:
    points_literal = ",\n    ".join(lean_point_literal(point) for point in points)
    cycle_literal = ",\n    ".join(lean_state_literal(state) for state in cycle)
    cover_literal = ", ".join(str(index) for index in cover)
    destination.write_text(
        f"""import Windmill.Certificate

namespace Windmill

def {name} : Certificate :=
  {{
    points := #[
      {points_literal}
    ]
    cycle := #[
      {cycle_literal}
    ]
    cover := #[{cover_literal}]
  }}

theorem {name}_valid : check {name} = true := by
  decide

theorem {name}_covers_points :
    ∀ i : Fin {name}.points.size, ∃ j : Fin {name}.cycle.size, ({name}.cycle[j]).curr = i.val := by
  decide

end Windmill
""",
        encoding="utf-8",
    )
