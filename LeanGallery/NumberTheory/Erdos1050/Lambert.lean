/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.RCLike.Basic

/-!
# Lambert-series identity for the Erdős #1050 aside

This file proves the standard Lambert-series rewrite used in Erdős's `2^n - 1` aside:
`∑ 1/(2^n - 1) = ∑ τ(n)/2^n`, where `τ(n)` is the number of divisors of `n`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- The Lambert-series identity
`∑_{n ≥ 1} 1/(2^n - 1) = ∑_{n ≥ 1} τ(n)/2^n`, with `τ(n)` represented as
`n.divisors.card`. The source's `n ≥ 1` indexing is encoded as `n + 1` over `ℕ`. -/
theorem two_pow_sub_one_eq_divisor_count_series :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) =
      ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1) := by
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) (k := 0) (r := (1 : ℝ) / 2)
    (by norm_num)
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    (n : ℝ) ^ 0 * ((1 : ℝ) / 2) ^ n / (1 - ((1 : ℝ) / 2) ^ n))] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    (ArithmeticFunction.sigma 0 n : ℝ) * ((1 : ℝ) / 2) ^ n)] at h
  calc
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1))
        = ∑' n : ℕ,
            (n + 1 : ℝ) ^ 0 * ((1 : ℝ) / 2) ^ (n + 1) /
              (1 - ((1 : ℝ) / 2) ^ (n + 1)) := by
          apply tsum_congr
          intro n
          have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := by
            have hlt : (1 : ℝ) < 2 ^ (n + 1) :=
              one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
            linarith
          have hden' : 1 - ((1 : ℝ) / 2) ^ (n + 1) ≠ 0 := by
            have hlt : ((1 : ℝ) / 2) ^ (n + 1) < 1 :=
              pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
            linarith
          field_simp [hden, hden', pow_succ]
          rw [sub_mul, one_mul, ← mul_pow]
          norm_num
    _ = ∑' n : ℕ, (ArithmeticFunction.sigma 0 (n + 1) : ℝ) * ((1 : ℝ) / 2) ^ (n + 1) := h
    _ = ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1) := by
          apply tsum_congr
          intro n
          simp [ArithmeticFunction.sigma_zero_apply, div_eq_mul_inv]

end LeanGallery.NumberTheory.Erdos1050
