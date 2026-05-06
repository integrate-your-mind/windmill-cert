#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if command -v lake >/dev/null 2>&1; then
  LAKE="lake"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE="$HOME/.elan/bin/lake"
else
  echo "lake not found" >&2
  exit 127
fi

if ! command -v npm >/dev/null 2>&1; then
  for prefix in "$HOME/.nvm/versions/node/v24.13.0/bin" "/opt/homebrew/bin"; do
    if [[ -x "$prefix/npm" ]]; then
      export PATH="$prefix:$PATH"
      break
    fi
  done
fi

if ! command -v npm >/dev/null 2>&1; then
  echo "npm not found" >&2
  exit 127
fi

PYTHONDONTWRITEBYTECODE=1 python3 scripts/audit_lean.py
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests -v
PYTHONPYCACHEPREFIX="${TMPDIR:-/tmp}/windmill-pycache-check" \
  python3 -m py_compile windmill.py build_artifacts.py scripts/audit_lean.py tests/test_windmill.py tests/test_lean_audit.py
"$LAKE" build

AXIOM_CHECK="$(mktemp)"
trap 'rm -f "$AXIOM_CHECK"' EXIT
cat >"$AXIOM_CHECK" <<'LEAN'
import Windmill
#print axioms Windmill.exported_valid
#print axioms Windmill.exported_covers_points
#print axioms Windmill.check_covers
#print axioms Windmill.Real.orient_line_reversal
#print axioms Windmill.Real.GeneralPosition.orient_ne_zero
#print axioms Windmill.Real.Line.leftCount_reverse
#print axioms Windmill.Real.balanced_start_exists
#print axioms Windmill.Real.angle_nextPivot_exists
#print axioms Windmill.Real.angle_nextPivot_unique_of_param_injective
LEAN
AXIOM_OUTPUT="$("$LAKE" env lean "$AXIOM_CHECK")"
printf '%s\n' "$AXIOM_OUTPUT"
if grep -q 'sorryAx' <<<"$AXIOM_OUTPUT"; then
  echo "Lean axiom audit failed: sorryAx found" >&2
  exit 1
fi

npm run test:web
npm run lint
npm run build
