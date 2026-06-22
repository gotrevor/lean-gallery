# LeanGallery 🖼️

A curated, public **showcase** of formalized mathematics in **Lean 4 + Mathlib** — finished,
axiom-clean formalizations of notable results, with a soft spot for *solved-but-unformalized*
theorems and *no-formula / impossibility* meta-theorems.

This is a **publish-only** collection: every result here compiles cleanly with **no `sorry`**,
enforced by CI (a build plus a `#print axioms` gate). Active / work-in-progress development
happens in private repositories; only finished, axiom-clean results are promoted in here.

## Contents

| Area | Result | Status |
|------|--------|--------|
| `Logic/Goodstein` | **Goodstein 1944** — every Goodstein sequence terminates (`∀ m, ∃ N, goodsteinSeq m N = 0`). Faithful hereditary-base bump, interpreted into ordinals below ε₀; strict ordinal descent + well-foundedness of `<` on `Ordinal`. | ✅ axiom-clean |

## What to audit (faithfulness)

The trust surface for each result is small and called out explicitly. For Goodstein:

- `LeanGallery/Logic/Goodstein/Defs.lean` — the **definition** of a Goodstein sequence (the
  hereditary-base bump + subtract-one process). Read this against Goodstein 1944.
- `LeanGallery/Logic/Goodstein/Statement.lean` — the **headline** `goodstein_terminates`.
- `LeanGallery/Logic/Goodstein/Anchors.lean` — `native_decide` anti-vacuity anchors: the
  definition *computes* the genuine trajectories (`m = 0..3`), so a vacuous definition can't pass.

`Engine.lean` is the proof; the definition + statement are the audit surface. CI re-checks
`#print axioms` so the published claim stays `[propext, Classical.choice, Quot.sound]`.

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Toolchain and Mathlib pin live in `lean-toolchain` / `lake-manifest.json` (Lean v4.31.0).

## License

[Apache License 2.0](LICENSE). Copyright 2026 Trevor Morris.
