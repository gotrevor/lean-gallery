import Mathlib

/-
GOAL (Stoll arXiv:0902.4168, faithfulness of Theorem 3.2): the binary digits of
`t = (α·√2 − β)/2^l` equal those of `α·√2`, shifted by `l`.  Formally, with `binDigit x n :=
⌊x·2^n⌋ − 2⌊x·2^(n-1)⌋`, for every `j ≥ 1`:  `binDigit t (j + l) = binDigit (α·√2) j`.

Replace the `sorry` with a complete Lean 4 proof. No `sorry`, no new axioms. End the file with
`#print axioms binDigit_div_pow`.

Strategy: `t·2^(j+l) = (α√2 − β)·2^j = α√2·2^j − β·2^j`, and `β·2^j : ℤ` so
`⌊t·2^(j+l)⌋ = ⌊α√2·2^j⌋ − β·2^j` (`Int.floor_sub_intCast`).  Likewise at `j+l-1` (using `j ≥ 1`,
so `j+l-1 = (j-1)+l` and the exponent on the `-β` term is `2^(j-1)`).  Substituting into `binDigit`,
the `β·2^j` and `2·β·2^(j-1)` cancel, leaving `⌊α√2·2^j⌋ − 2⌊α√2·2^(j-1)⌋ = binDigit (α√2) j`.
Numerically verified for (α,β,l) = (11,5,3),(45,19,5),(3,1,1),(181,75,7).
-/

noncomputable def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

theorem binDigit_div_pow (a b : ℤ) (l : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    binDigit (((a : ℝ) * Real.sqrt 2 - (b : ℝ)) / 2 ^ l) (j + l) = binDigit ((a : ℝ) * Real.sqrt 2) j := by
  sorry
