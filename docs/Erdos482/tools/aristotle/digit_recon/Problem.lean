import Mathlib

open Real

/-
GOAL: connect St05's capstone digit output to the LITERAL mathlib base-`g` digit of the mantissa.

The repo's `thm13_digits` proves the recurrence output equals `Real.digits (t·g^{n−1}/g) g 0` (a valid
mathlib digit of the *shifted* quantity).  We want the cleaner form: this equals the `(n−2)`-th
mathlib base-`g` digit of the mantissa `t` itself, for `n ≥ 2`.  Then a √2-corollary can read
"`= Real.digits √2 g (n−2)` = the literal digit of √2".

Provided (this is `Erdos482.General.realDigits_eq_digitStep`, a PROVED repo lemma — use it as given):
  `realDigits_eq_digitStep : 0 ≤ y → ((Real.digits y g i : ℕ) : ℤ) = ⌊g·(y·g^i)⌋ − g·⌊y·g^i⌋`.

PROOF: apply it to both sides.
  LHS: `Real.digits (t·g^{n−1}/g) g 0` → `⌊g·(t·g^{n−1}/g · g^0)⌋ − g·⌊t·g^{n−1}/g · g^0⌋`
       `= ⌊g·(t·g^{n−1}/g)⌋ − g·⌊t·g^{n−1}/g⌋`.
  RHS: `Real.digits t g (n−2)` → `⌊g·(t·g^{n−2})⌋ − g·⌊t·g^{n−2}⌋`.
  Reduce both to equality via `t·g^{n−1}/g = t·g^{n−2}` (for `n ≥ 2`, `g ≠ 0`: `g^{n−1}/g = g^{n−2}`,
  using `n−1 = (n−2)+1` and `pow_succ`).  Need `0 ≤ t·g^{n−1}/g` and `0 ≤ t·g^{n−2}` for the lemma
  hypotheses (from `0 ≤ t`, `g ≥ 0`).  `[NeZero g]` is in scope.
-/

axiom realDigits_eq_digitStep (g : ℕ) [NeZero g] (y : ℝ) (hy : 0 ≤ y) (i : ℕ) :
    ((Real.digits y g i : ℕ) : ℤ) = ⌊(g : ℝ) * (y * (g : ℝ) ^ i)⌋ - g * ⌊y * (g : ℝ) ^ i⌋

theorem digit_recon (g : ℕ) [NeZero g] (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn : 2 ≤ n) :
    ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ)
      = ((Real.digits t g (n - 2) : ℕ) : ℤ) := by
  sorry
