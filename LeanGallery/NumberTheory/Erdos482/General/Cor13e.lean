/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm13Closed

/-!
# Showcase — base-3 digits of `e` (transcendental in an odd base)

A concrete instantiation of the unconditional general theorem `thm13_digits` at base `g = 3`,
`w = e`.  This is the signature object of Stoll's sharper companion **[St06]** (Acta Arith. 125
(2006), 89–100): zbMATH ties that paper to OEIS **A004594** = "expansion of `e` in base 3", a
*transcendental constant in an odd base*.  We do not have St06's text, but the result it showcases
is a direct corollary of our **own** machine-checked Theorem 1.3 — so we read off the ternary digits
of `e` honestly, without citing any unverified St06 closed form.

Stoll's coefficients for `g = 3`, `w = e` are `a = 3/((3−1)(e+3)) = 3/(2(e+3))` and
`b = (3−1)(e+3) = 6 + 2e` (so `a·b = 3`).  Since `1 ≤ e < 3` the base-3 mantissa is `t = e` itself
(`m = ⌊log₃ e⌋ = 0`), so the recurrence's Graham–Pollak difference reads off the **fractional ternary**
digits of `e = (2.2011011212…)₃` — i.e. `Real.digits e 3 k` is the `(k+1)`-th base-3 digit after the
point, `2, 0, 1, 1, 0, 1, 1, 2, …` (verified numerically against the high-precision expansion of `e`).
Any offset `ε ∈ [−1/3, 4/3)` works; we take `ε = 0`.

Axiom-clean (inherits `thm13_digits`'s `[propext, Classical.choice, Quot.sound]`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

private lemma exp_one_ge_one : (1 : ℝ) ≤ Real.exp 1 :=
  le_of_lt (by linarith [Real.exp_one_gt_d9])

/-- **Base-3 digits of `e` (mantissa form).**  The recurrence `gu 3 (3/(2(e+3))) (6+2e) 0` extracts
the ternary digits of `e`: for every `n ≥ 1`, `gu(2n) − 3·gu(2n−2)` equals the base-`3` digit
`Real.digits (e·3^{n−1}/3) 3 0`. -/
theorem cor13_ternary_exp_one (n : ℕ) (hn : 1 ≤ n) :
    gu 3 (3 / (2 * (Real.exp 1 + 3))) (6 + 2 * Real.exp 1) 0 (2 * n)
        - 3 * gu 3 (3 / (2 * (Real.exp 1 + 3))) (6 + 2 * Real.exp 1) 0 (2 * n - 2)
      = ((Real.digits (Real.exp 1 * (3 : ℝ) ^ (n - 1) / 3) 3 0 : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have hpos : (0 : ℝ) < Real.exp 1 + 3 := by have := exp_one_ge_one; linarith
  -- a = 3/((3−1)(e+3))
  have ha : (3 : ℝ) / (2 * (Real.exp 1 + 3))
      = (3 : ℝ) / (((3 : ℝ) - 1) * (Real.exp 1 + 3)) := by norm_num
  -- b = (3−1)(e+3)
  have hb : (6 + 2 * Real.exp 1) = ((3 : ℝ) - 1) * (Real.exp 1 + 3) := by ring
  exact thm13_digits 3 (by norm_num) (Real.exp 1) exp_one_ge_one Real.exp_one_lt_three
    0 (3 / (2 * (Real.exp 1 + 3))) (6 + 2 * Real.exp 1) ha hb
    (by norm_num) (by norm_num) n hn

/-- **Base-3 digits of `e`, literal-digit form.**  For `n ≥ 2`, the ternary recurrence output is
exactly the `(n−2)`-th mathlib base-3 digit of `e` itself: `gu(2n) − 3·gu(2n−2) = Real.digits e 3 (n−2)`. -/
theorem cor13_ternary_exp_one_literal (n : ℕ) (hn : 2 ≤ n) :
    gu 3 (3 / (2 * (Real.exp 1 + 3))) (6 + 2 * Real.exp 1) 0 (2 * n)
        - 3 * gu 3 (3 / (2 * (Real.exp 1 + 3))) (6 + 2 * Real.exp 1) 0 (2 * n - 2)
      = ((Real.digits (Real.exp 1) 3 (n - 2) : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [cor13_ternary_exp_one n (by omega)]
  exact digit_recon 3 (Real.exp 1) (le_of_lt (Real.exp_pos 1)) n hn

end LeanGallery.NumberTheory.Erdos482.General
