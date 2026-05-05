from __future__ import annotations

import unittest

from windmill import (
    Point,
    State,
    certify_start,
    check_general_position,
    find_any_certifying_start,
    find_balanced_certifying_state,
    generate_cases,
    next_state,
    stress_test,
)


class WindmillTests(unittest.TestCase):
    def test_triangle_cycle_hits_every_point(self) -> None:
        points = check_general_position((Point(0, 0), Point(4, 0), Point(1, 3)))
        start = State(0, 1)
        cert = certify_start(points, start)
        self.assertTrue(cert["works"])
        self.assertEqual(cert["cycle_length"], 3)
        self.assertEqual(cert["cover"], [2, 0, 1])

    def test_next_state_is_successor_in_angle_order(self) -> None:
        points = check_general_position(
            (
                Point(-5, -2),
                Point(2, -5),
                Point(6, 1),
                Point(0, 6),
                Point(-4, 4),
            )
        )
        self.assertEqual(next_state(points, State(0, 2)), State(2, 1))

    def test_procedural_cases_certify(self) -> None:
        cases = generate_cases(seed=12345, sizes=(5, 6), cases_per_strategy=1)
        for case in cases:
            start, cert = find_any_certifying_start(case.points)
            self.assertIsInstance(start, State)
            self.assertTrue(cert["works"], case.seed_tag)

    def test_balanced_state_exists_for_demo_sized_odd_case(self) -> None:
        cases = generate_cases(seed=777, sizes=(7,), cases_per_strategy=1)
        found = False
        for case in cases:
            balanced = find_balanced_certifying_state(case.points)
            if balanced is not None:
                found = True
                _, counts, cert = balanced
                self.assertTrue(cert["works"])
                self.assertEqual(counts[0], counts[1])
        self.assertTrue(found)

    def test_small_stress_harness(self) -> None:
        result = stress_test(
            max_n=5,
            exhaustive_grid_size=(3, 3),
            exhaustive_up_to_n=4,
            random_cases_per_family=10,
            seed=42,
        )
        self.assertTrue(result["ok"])


if __name__ == "__main__":
    unittest.main()
