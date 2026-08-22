import Mathlib
import Mathlib.NumberTheory.Rayleigh

open scoped symmDiff

/-
GOAL (toward Stoll [St06] Cor 3.5): from Rayleigh's theorem (mathlib's
`Irrational.beattySeq_symmDiff_beattySeq_pos`), derive the EXPLICIT partition form Stoll quotes:
every positive integer lies in EXACTLY ONE of the two Beatty sequences `B⁺(1+√2)`, `B⁺(1+1/√2)`.

Background. `beattySeq r k = ⌊k·r⌋`.  For the Hölder-conjugate pair `r = 1+√2`, `s = 1+1/√2`
(`r⁻¹+s⁻¹ = 1`, `r` irrational), Rayleigh gives
  {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n}.
The symmetric difference being the full positive set is equivalent to: the two sets are DISJOINT and
their UNION is all positives — i.e. each `n > 0` is hit by exactly one sequence.  This is the form
Stoll uses to characterise the representable `m`.

TASK. Prove `st06_beatty_unique` below (replace the sorry).  You may take the two facts
`hpart` (Rayleigh, the symmDiff identity) and `hr`/`hs` as given hypotheses; the content is the
set-theoretic extraction of "exactly one" from "symmetric difference = univ on positives".
Pure `Set`/`symmDiff` manipulation (`Set.mem_symmDiff`), no analysis.
-/

theorem st06_beatty_unique
    (r s : ℝ)
    (hpart : {Int.floor (k * r) | k > (0 : ℤ)} ∆ {Int.floor (k * s) | k > (0 : ℤ)} = {n | 0 < n}) :
    ∀ n : ℤ, 0 < n →
      ((∃ k > (0 : ℤ), Int.floor (k * r) = n) ∧ ¬ (∃ k > (0 : ℤ), Int.floor (k * s) = n))
        ∨ (¬ (∃ k > (0 : ℤ), Int.floor (k * r) = n) ∧ (∃ k > (0 : ℤ), Int.floor (k * s) = n)) := by
  sorry
