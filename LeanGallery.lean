import LeanGallery.Logic.Goodstein.Basic
import LeanGallery.Logic.Goodstein.Engine
import LeanGallery.Logic.Goodstein.Statement
import LeanGallery.Logic.Hydra.Basic
import LeanGallery.Logic.Hydra.Engine
import LeanGallery.Logic.Hydra.Statement
import LeanGallery.NumberTheory.Erdos403.Basic
import LeanGallery.NumberTheory.Erdos403.Engine
import LeanGallery.NumberTheory.Erdos403.Statement
import LeanGallery.Combinatorics.Erdos1213

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
- `NumberTheory/Erdos403` — Erdős #403: only finitely many powers of two are sums of distinct
  factorials; the largest is `2⁷ = 2! + 3! + 5! = 128` (Frankl / Shen Lin 1976).
- `Combinatorics/Erdos1213` — Erdős #1213 / Hegyvári Thm 3: a bounded-gap increasing sequence with
  all consecutive-block sums distinct has bounded last term, so `f(a,K)` is finite (Hegyvári 1986).
-/
