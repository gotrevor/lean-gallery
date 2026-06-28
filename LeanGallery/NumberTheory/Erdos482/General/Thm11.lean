/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm12CaseI

/-!
# Stoll [St05] Theorem 1.1 (Rabinowitz–Gilbert 1991) — binary digits, the base case

Theorem 1.1 is the `j = 1`, `ε = ½` specialization of Case I (`a = 2(1 − 1/(t+2))`, `b = 2/a`): the
classical Rabinowitz–Gilbert binary recurrence whose `u₂ₙ₊₁ − 2u₂ₙ₋₁` reads off the binary digits of
`w`.  It falls out of `thm12_caseI_digits` since `½ ∈ [1/3, 2/3)` and `1 ≥ 1`.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **St05 Theorem 1.1 (Rabinowitz–Gilbert).**  `a = 2(1 − 1/(t+2))`, `b = 2/a`, offset `½`: the
recurrence `gv a b ½` extracts the binary digits of `w` (mantissa `1 ≤ t < 2`): for `n ≥ 1`,
`gv(2n) − 2·gv(2n−2) = Real.digits (t·2^{n−1}/2) 2 0`. -/
theorem thm11_rabinowitz_gilbert (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (n : ℕ) (hn : 1 ≤ n) :
    gv (2 * (1 - 1 / (t + 2))) (2 / (2 * (1 - 1 / (t + 2)))) (1 / 2) (2 * n)
        - 2 * gv (2 * (1 - 1 / (t + 2))) (2 / (2 * (1 - 1 / (t + 2)))) (1 / 2) (2 * n - 2)
      = ((Real.digits (t * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have ha : 2 * (1 - 1 / (t + 2)) = 2 * ((1 : ℕ) : ℝ) - 2 / (t + 2) := by push_cast; ring
  exact thm12_caseI_digits t ht1 ht2 1 (le_refl 1) (1 / 2) _ _ (by norm_num) (by norm_num) ha rfl n hn

end LeanGallery.NumberTheory.Erdos482.General
