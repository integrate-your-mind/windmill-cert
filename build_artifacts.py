from __future__ import annotations

from pathlib import Path

from windmill import (
    as_jsonable_points,
    as_jsonable_states,
    pick_demo_case,
    render_gif,
    stress_test,
    write_json,
    write_lean_certificate,
)


ROOT = Path(__file__).resolve().parent
ARTIFACTS = ROOT / "artifacts"
LEAN_DIR = ROOT / "Windmill"


def main() -> None:
    ARTIFACTS.mkdir(exist_ok=True)
    LEAN_DIR.mkdir(exist_ok=True)

    suite_summary = stress_test(
        max_n=8,
        exhaustive_grid_size=(4, 4),
        exhaustive_up_to_n=5,
        random_cases_per_family=250,
        seed=20260422,
    )
    write_json(ARTIFACTS / "stress_report.json", suite_summary)

    case, state, counts, cert = pick_demo_case()
    cycle = cert["cycle"]
    cover = cert["cover"]
    assert isinstance(cycle, list)
    assert isinstance(cover, list)

    sample_payload = {
        "strategy": case.strategy,
        "size": case.size,
        "seed_tag": case.seed_tag,
        "balanced_start": {"prev": state.prev, "curr": state.curr},
        "balanced_counts": list(counts),
        "points": as_jsonable_points(case.points),
        "cycle": as_jsonable_states(cycle),
        "cover": cover,
    }
    write_json(ARTIFACTS / "sample_certificate.json", sample_payload)
    render_gif(case.points, cycle, ARTIFACTS / "windmill_demo.gif")
    write_lean_certificate(
        case.points,
        cycle,
        cover,
        LEAN_DIR / "Generated.lean",
        name="exported",
    )


if __name__ == "__main__":
    main()
