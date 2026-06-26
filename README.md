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
| `Logic/Hydra` | **Kirby–Paris 1982** — Hercules always wins: every hydra dies (`hydra_terminates` — every battle reaches `leaf`). Faithful chop-a-head-regrow-at-the-grandparent move on finite rooted trees; the ε₀ Kirby–Paris ordinal `♯ ωᵒ⁽ᶜ⁾`, realized as a recursive multiset (path) order on `Mathlib/Logic/Hydra.lean`'s `CutExpand`; strict descent + well-foundedness. | ✅ axiom-clean |

## What to audit (faithfulness)

The trust surface for each result is small and called out explicitly. For Goodstein:

- `LeanGallery/Logic/Goodstein/Basic.lean` — the **definition** of a Goodstein sequence (the
  hereditary-base bump + subtract-one process), plus `native_decide` anti-vacuity anchors: the
  definition *computes* the genuine trajectories (`m = 0..4`, including `4 = 2²`, the first seed
  that exercises the recursive exponent bump), so a vacuous definition can't pass. Read this
  against Goodstein 1944.
- `LeanGallery/Logic/Goodstein/Statement.lean` — the **headline** `goodstein_terminates`.

For Kirby–Paris:

- `LeanGallery/Logic/Hydra/Basic.lean` — the **datatype** `Hydra` (a finite rooted tree) and the
  legal **move** `Step` (chop a head; if its parent is not the root, regrow `n + 1` copies of the
  cut node at the grandparent), with explicit one-move derivations as anti-vacuity anchors
  (including the regrowth that makes the hydra *bigger*, and the dead hydra being *terminal*). The
  game is on unordered trees — every statement is invariant under permuting children. Read this
  against Kirby–Paris 1982.
- `LeanGallery/Logic/Hydra/Statement.lean` — the **headline** `hydra_terminates` (every battle
  reaches `leaf`, over all head choices and all regrowth schedules).

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
- L. Kirby and J. Paris, *Accessible independence results for Peano arithmetic*, Bull. London
  Math. Soc. **14** (1982), no. 4, 285–293. <https://doi.org/10.1112/blms/14.4.285>

## License

[Apache License 2.0](LICENSE). Copyright 2026 Trevor Morris.
