from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_SOURCES = [ROOT / "Windmill.lean", *sorted((ROOT / "Windmill").rglob("*.lean"))]

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"\baxiom\b"),
    "constant": re.compile(r"\bconstant\b"),
    "opaque": re.compile(r"\bopaque\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
}


def audit_sources(paths: list[Path] = LEAN_SOURCES) -> list[str]:
    findings: list[str] = []
    for path in paths:
        text = path.read_text()
        for line_number, line in enumerate(text.splitlines(), start=1):
            for label, pattern in FORBIDDEN.items():
                if pattern.search(line):
                    rel = path.relative_to(ROOT)
                    findings.append(f"{rel}:{line_number}: forbidden Lean token `{label}`")
    return findings


def main() -> int:
    findings = audit_sources()
    if findings:
        print("Lean audit failed:")
        for finding in findings:
            print(finding)
        return 1
    print("Lean audit passed: no sorry/admit/axiom/constant/opaque/unsafe tokens in trusted Lean sources.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
