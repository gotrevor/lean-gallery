/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.Basic
import LeanGallery.NumberTheory.Erdos482.Induction
import LeanGallery.NumberTheory.Erdos482.Digits

namespace LeanGallery.NumberTheory.Erdos482
open Real

/-- **HEADLINE (Graham–Pollak, Erdős #482).**  For the sequence `u 0 = 1`,
`u (n+1) = ⌊√2·(u n + 1/2)⌋`, the quantity `u(2n+1) − 2·u(2n−1)` equals the `n`-th binary digit of
`√2` (in Stoll's floor-formula sense `binDigit`).  Verified numerically: the digits read
`0,1,1,0,1,…` matching `√2 = 1.0110101…₂`. -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := (gp_pair (m + 1)).1
  have h2 := (gp_pair m).1
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [e2, h1, h2]
  unfold binDigit
  rw [Nat.add_sub_cancel]
  ring

/-- **Canonical form.**  `u(2n+1) − 2·u(2n−1)` is literally the `(n−1)`-th base-2 digit of the
fractional part of `√2` under mathlib's `Real.digits` (equivalently, the `n`-th binary digit of
`√2` after the point). -/
theorem graham_pollak_digits (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ)
      = ((Real.digits (Int.fract (Real.sqrt 2)) 2 (n - 1) : ℕ) : ℤ) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have h2 : Real.sqrt 2 < 2 := by nlinarith [hs2, hsnn]
  rw [graham_pollak n hn, digit_bridge (Real.sqrt 2) h1 h2 (n - 1)]
  unfold binDigit
  rw [Nat.sub_add_cancel hn]

/-- **Canonical digit sequence (0-based).**  Reindexed `graham_pollak_digits`: for every `i`,
`u(2(i+1)+1) − 2·u(2(i+1)−1)` is exactly `Real.digits (Int.fract √2) 2 i`, the `i`-th binary digit
of the fractional part of `√2`.  So the whole Graham–Pollak difference sequence *is* the binary
expansion of `√2` after the point. -/
theorem gp_digit_seq (i : ℕ) :
    (u (2 * (i + 1) + 1) : ℤ) - 2 * (u (2 * (i + 1) - 1) : ℤ)
      = ((Real.digits (Int.fract (Real.sqrt 2)) 2 i : ℕ) : ℤ) := by
  simpa using graham_pollak_digits (i + 1) (by omega)

/-- **Faithfulness certificate.**  The first six Graham–Pollak digits are `0, 1, 1, 0, 1, 0`,
matching the binary expansion `√2 = 1.0110101…₂`.  Anchors the whole edifice to concrete numbers. -/
theorem binDigit_sqrt2_first_six :
    binDigit (Real.sqrt 2) 1 = 0 ∧ binDigit (Real.sqrt 2) 2 = 1 ∧
      binDigit (Real.sqrt 2) 3 = 1 ∧ binDigit (Real.sqrt 2) 4 = 0 ∧
      binDigit (Real.sqrt 2) 5 = 1 ∧ binDigit (Real.sqrt 2) 6 = 0 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have lo : (1.41:ℝ) < Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hi : Real.sqrt 2 < 1.42 := by nlinarith [hs2, hsnn]
  have f0 : ⌊Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f1 : ⌊Real.sqrt 2 * 2⌋ = 2 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f2 : ⌊Real.sqrt 2 * 4⌋ = 5 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f3 : ⌊Real.sqrt 2 * 8⌋ = 11 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f4 : ⌊Real.sqrt 2 * 16⌋ = 22 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f5 : ⌊Real.sqrt 2 * 32⌋ = 45 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f6 : ⌊Real.sqrt 2 * 64⌋ = 90 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold binDigit <;>
    norm_num [f0, f1, f2, f3, f4, f5, f6]

/-- **Closing the loop.**  The base-2 digit sequence reconstructs `Int.fract √2` via
`Real.ofDigits`.  Combined with `gp_digit_seq` (which identifies those digits with the
Graham–Pollak differences `u(2(i+1)+1) − 2u(2(i+1)−1)`), this says the Graham–Pollak sequence
recovers the entire binary expansion of `√2` after the point. -/
theorem gp_reconstructs_sqrt2 :
    Real.ofDigits (Real.digits (Int.fract (Real.sqrt 2)) 2) = Int.fract (Real.sqrt 2) :=
  Real.ofDigits_digits (by norm_num) ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The digit `1` occurs infinitely often.**  The Graham–Pollak difference
`u(2(i+1)+1) − 2u(2(i+1)−1)` is not eventually `0` — since `√2` is irrational its binary expansion
does not terminate.  (Each difference is a bit by `binDigit_mem_zero_one`, so "not eventually 0"
means "equal to 1 infinitely often".) -/
theorem gp_diff_one_infinitely :
    ¬ ∃ N, ∀ i, N ≤ i → (u (2 * (i + 1) + 1) : ℤ) - 2 * (u (2 * (i + 1) - 1) : ℤ) = 0 := by
  rintro ⟨N, hN⟩
  apply digits_sqrt2_not_eventually_zero
  refine ⟨N, fun i hi => ?_⟩
  have h := gp_digit_seq i
  rw [hN i hi] at h
  exact_mod_cast h.symm

end LeanGallery.NumberTheory.Erdos482

/-! # `LeanGallery.NumberTheory.Erdos482` (umbrella import) -/
