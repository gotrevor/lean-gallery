import LeanGallery.Logic.Goodstein.Basic
import LeanGallery.Logic.Goodstein.Engine
import LeanGallery.Logic.Goodstein.Statement
import LeanGallery.Logic.Hydra.Basic
import LeanGallery.Logic.Hydra.Engine
import LeanGallery.Logic.Hydra.Statement

/-!
# LeanGallery

A curated, public **showcase** of formalized mathematics in Lean 4 + Mathlib: finished,
axiom-clean formalizations of notable results, with a soft spot for *solved-but-unformalized*
theorems and *no-formula / impossibility* meta-theorems.

Publish-only: every result here compiles cleanly with no `sorry` (CI-enforced). Active,
work-in-progress development lives in private repositories; only finished, axiom-clean
results are promoted in here.

## Results
- `Logic/Goodstein` — Goodstein's theorem: every Goodstein sequence terminates (Goodstein 1944).
- `Logic/Hydra` — Kirby–Paris hydra: Hercules always wins / every hydra dies (termination, ε₀).
-/
