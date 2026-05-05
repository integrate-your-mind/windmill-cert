# Proof Status

## Current status

This workspace does **not** contain a full universal proof of the windmill theorem for all finite point sets in general position.

The Aristotle/Harmonic runs have completed and were reviewed. They do not change this status: both returned proof scaffolding with the central invariant, balanced-start, and full-coverage lemmas still unresolved by `sorry`.

What is currently proved:

- A computational certifier checks individual finite instances by building the full deterministic windmill state graph and finding a certifying cycle when one exists.
- A Lean checker verifies one exported finite certificate exactly.
- The demo visualizes that exported certified cycle.
- `scripts/audit_lean.py` guards the trusted Lean sources against `sorry`, `admit`, custom `axiom`, and `unsafe`.
- `Windmill/Universal/Primitives.lean` starts the universal proof stack with integer-coordinate geometry primitives and algebraic orientation/collinearity lemmas.
- `Windmill/Universal/Config.lean` adds finite indexed point configurations and general-position consequences.
- `Windmill/Universal/Side.lean` adds strict side predicates and orientation-reversal lemmas.
- `Windmill/Universal/TwoPoint.lean` proves the two-point alternating-pivot base case in a small discrete model.
- `Windmill/Universal/State.lean` adds the ordered-pair `WState` model and proves represented state lines are nondegenerate under distinct configurations.
- `Windmill/Universal/SideCount.lean` adds finite side-index lists/counts and line-reversal count lemmas.
- `Windmill/Real/Primitives.lean`, `Windmill/Real/Config.lean`, and `Windmill/Real/Side.lean` start a Mathlib-backed real-coordinate namespace for the eventual universal theorem.
- `Windmill/Real/State.lean` and `Windmill/Real/Balance.lean` add the real-coordinate state and balance interfaces, including physical line balance through one pivot and post-switch state counts.
- `Windmill/Real/Projection.lean` proves existence of a separating real direction for any finite distinct point configuration.
- `Windmill/Real/Median.lean` proves `balanced_start_exists` for every nonempty real general-position configuration using projection plus a finite median argument.
- `Windmill/Real/Arc.lean` and `Windmill/Real/Step.lean` add reviewed transition scaffolding definitions without claiming transition existence, uniqueness, or invariant preservation yet.

Important scope note:

- The current universal proof stack uses integer-coordinate points. This is useful for exact computational certificates and order-type work, but a final theorem over arbitrary real-plane configurations still needs either a real-coordinate version or a bridge from real configurations to an equivalent exact/order-type model.
- The real-coordinate namespace now proves the balanced-start layer. It is not yet the full universal windmill theorem.

What is **not** currently proved:

- The universal theorem for every `n`
- The full invariant argument inside Lean
- The statement that every point is hit infinitely often for all valid configurations

## Why this matters

A finite certificate is not the same thing as a universal proof.

The current code can honestly say:

- “this concrete instance is certified”
- “many generated instances were checked”

It cannot honestly say:

- “the theorem is proved for all `n`”

## What a real universal proof requires

To make the proof “perfect” in the sense you asked for, the project needs a full mathematical formalization, not more stress testing.

That formalization needs at least these ingredients:

1. A formal model of windmill states and pivot-switch transitions
2. A proof that the side-balance invariant is preserved at every pivot change
3. A proof that every point admits a balanced line through it
4. A proof that the balanced windmill sweeps all directions
5. A proof that therefore every point becomes a pivot infinitely often

## Honest next step

The correct next step is to build a new Lean development for the universal argument.

That is a substantial project. It should be treated as a fresh formalization task rather than a small patch to the current finite checker.
