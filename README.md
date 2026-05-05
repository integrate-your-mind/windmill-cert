# Windmill Certifier

This workspace now has three separate deliverables.

`windmill.py` is the computational layer. For each generated point set, it builds and checks the entire finite windmill state graph, not just one simulated start. A point set is certified when some eventual cycle uses every point as a pivot.

`Windmill/Generated.lean` is the Lean layer. It does not prove the IMO theorem in full generality. It proves that one exported finite certificate is valid: the generated points are in general position, the listed cycle is closed under the windmill transition rule, and every point appears on that cycle.

The Next.js app in `app/` is the presentation layer. It imports the exported JSON certificate and animates the certified cycle with React state plus a `useEffect`-driven animation loop. The static export lands in `artifacts/next-demo/`, and `artifacts/windmill_demo.html` redirects there for compatibility with the old artifact path.

The stress harness in `build_artifacts.py` is stronger than plain random testing:

- It exhaustively checks all general-position subsets of a small integer grid up to a chosen size.
- It also checks adversarial random families such as parabola, two-chain, near-collinear, grid, and clustered cases.
- For each sampled set, it inspects the whole deterministic state graph and asks whether any cycle covers all pivots.

The hard boundary is unchanged: this is still not a universal proof of the theorem for all configurations. The real universal proof is the invariant argument, or a full formalization in Lean/Coq. The closest purely computational route toward universality for fixed `n` would be to enumerate order types, because the windmill dynamics depend only on orientation data.

See [PROOF_STATUS.md](PROOF_STATUS.md) for the precise boundary between what is proved here and what is not.

The Aristotle/Harmonic outputs are reviewed in [ARISTOTLE_REVIEW.md](ARISTOTLE_REVIEW.md). Both runs are useful as scaffolding, but neither is a finished universal proof because the central geometric lemmas remain as `sorry`.

The planned universal proof architecture is mapped in [UNIVERSAL_PROOF_PLAN.md](UNIVERSAL_PROOF_PLAN.md).

## Run the visual

```sh
npm ci
npm run dev -- --hostname 127.0.0.1 --port 3000
```

Then open `http://127.0.0.1:3000/`.

The dev script intentionally uses Next's webpack dev server. In this workspace, the default Next 16 Turbopack dev server returned a root `404` even though the production build exported `/` correctly.

## Current formal proof status

The Real/Mathlib layer is under `Windmill/Real/`. It includes trusted primitives, configuration, side-count, state/balance, projection, median, arc, and step scaffolding modules. The currently proved Real theorem is `Windmill.Real.balanced_start_exists`; the full universal windmill theorem is still work in progress.
