# LeanGallery 🖼️

A curated, public **showcase** of formalized mathematics in **Lean 4 + Mathlib** — finished,
axiom-clean formalizations of notable results, with a soft spot for *solved-but-unformalized*
theorems and *no-formula / impossibility* meta-theorems.

This is a **publish-only** collection: every result here compiles cleanly with **no `sorry`** and
**no warnings** (warnings are errors), enforced by CI (a build plus a `#print axioms` gate). Active /
work-in-progress development happens in private repositories; only finished, axiom-clean results are
promoted in here.

## Contents

| Area | Result | Status |
|------|--------|--------|
| `Logic/Goodstein` | **Goodstein 1944** — every Goodstein sequence terminates (`∀ m, ∃ N, goodsteinSeq m N = 0`). Faithful hereditary-base bump, interpreted into ordinals below ε₀; strict ordinal descent + well-foundedness of `<` on `Ordinal`. | ✅ axiom-clean |

## What to audit (faithfulness)

The trust surface for each result is small and called out explicitly. For Goodstein:

- `LeanGallery/Logic/Goodstein/Basic.lean` — the **definition** of a Goodstein sequence (the
  hereditary-base bump + subtract-one process), plus `native_decide` anti-vacuity anchors: the
  definition *computes* the genuine trajectories (`m = 0..4`, including `4 = 2²`, the first seed
  that exercises the recursive exponent bump), so a vacuous definition can't pass. Read this
  against Goodstein 1944.
- `LeanGallery/Logic/Goodstein/Statement.lean` — the **headline** `goodstein_terminates`.

`Engine.lean` is the proof; `Basic.lean` + `Statement.lean` are the audit surface. CI re-checks
`#print axioms` so the published claim stays `[propext, Classical.choice, Quot.sound]`.

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Toolchain and Mathlib pin live in `lean-toolchain` / `lake-manifest.json` (Lean v4.31.0).

## References

- R. L. Goodstein, *On the restricted ordinal theorem*, Journal of Symbolic Logic **9** (1944),
  no. 2, 33–41. <https://doi.org/10.2307/2268019>

## License

[Apache License 2.0](LICENSE). Copyright 2026 Trevor Morris.
