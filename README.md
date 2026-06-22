# LeanGallery 🖼️

A curated, public **showcase** of formalized mathematics in **Lean 4 + Mathlib** — finished,
axiom-clean formalizations of notable results, with a soft spot for *solved-but-unformalized*
theorems and *no-formula / impossibility* meta-theorems.

This is a **publish-only** collection: every result here compiles cleanly with **no `sorry`**,
enforced by CI (a build plus a `#print axioms` gate). Active / work-in-progress development
happens in private repositories; only finished, axiom-clean results are promoted in here.

## Contents

_First result lands in the next commit._

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Toolchain and Mathlib pin live in `lean-toolchain` / `lake-manifest.json` (Lean v4.31.0).

## License

[Apache License 2.0](LICENSE). Copyright 2026 Trevor Morris.
