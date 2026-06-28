/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Erdos482General

/-!
# Erdős–Graham #482 — literal digits of *any* `w ≥ 1` (closing the mantissa shift)

`erdos482_resolution` reads off the digits of the **mantissa** `t = w/g^m` (`m = ⌊log_g w⌋`); its
output is `Real.digits (t·g^{n−1}/g) g 0`, the digit of `t`.  `erdos482_resolution_literal` then
matched mathlib's `Real.digits` only when `w` was already its own mantissa (`w ∈ [1, g)`, `m = 0`).

This file removes that restriction for every `w ≥ 1`.  Since `w = t·g^m` (scaling the mantissa back),
multiplying by `g^m` shifts the radix point `m` places, so `t`'s digit at fractional position `k`
becomes `w`'s digit at fractional position `k − m`.  Concretely (`realDigits_mantissa_shift`):
`Real.digits t g k = Real.digits w g (k − m)` for `k ≥ m`.  Composed with `digit_recon`, the
recurrence's `n`-th Graham–Pollak difference equals the genuine mathlib digit `Real.digits w g i` of
`w` itself, at `n = i + m + 2`.

The restriction `w ≥ 1` (so `m = ⌊log_g w⌋ ≥ 0`) is only to keep the index `m` a `ℕ`; `0 < w < 1`
is entirely analogous (`m < 0`, the point shifts the other way).  Axiom-clean (inherits
`thm13_digits` + an elementary `zpow` identity).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **Mantissa digit-shift bridge.**  For `w > 0`, base `g` (`NeZero g`), mantissa `t = w/g^m`
(`m = ⌊log_g w⌋`), and any `k ≥ m`, the `k`-th base-`g` digit of the mantissa equals the
`(k−m)`-th base-`g` digit of `w`: scaling `t` back to `w` by `g^m` shifts the radix point. -/
theorem realDigits_mantissa_shift (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w)
    (k : ℕ) (hk : ⌊Real.logb g w⌋ ≤ (k : ℤ)) :
    ((Real.digits (w / (g : ℝ) ^ (⌊Real.logb g w⌋)) g k : ℕ) : ℤ)
      = ((Real.digits w g (((k : ℤ) - ⌊Real.logb g w⌋).toNat) : ℕ) : ℤ) := by
  have hgN : (0 : ℕ) < g := Nat.pos_of_ne_zero (NeZero.ne g)
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgN
  set m : ℤ := ⌊Real.logb g w⌋ with hm
  set t : ℝ := w / (g : ℝ) ^ m with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  set j : ℕ := ((k : ℤ) - m).toNat with hj
  have hjeq : (j : ℤ) = (k : ℤ) - m := Int.toNat_of_nonneg (by omega)
  rw [realDigits_eq_digitStep g t ht0 k, realDigits_eq_digitStep g w (le_of_lt hw) j]
  -- both sides are `digitStep g (·)`; reduce to the real-number identity `t·g^k = w·g^j`
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hg0
  have key : t * (g : ℝ) ^ k = w * (g : ℝ) ^ j := by
    rw [ht, ← zpow_natCast (g : ℝ) k, ← zpow_natCast (g : ℝ) j, div_mul_eq_mul_div,
      mul_div_assoc, ← zpow_sub₀ hgne]
    congr 2
    omega
  rw [key]

/-- **Erdős–Graham #482 — literal digits of any `w ≥ 1`.**  With `m = ⌊log_g w⌋ ≥ 0`, there are St05
coefficients `a, b, ε` (`a·b = g`) so that the recurrence's Graham–Pollak difference reads off `w`'s
genuine mathlib base-`g` digits: for every `i`, at index `n = i + m + 2`,
`gu(2n) − g·gu(2n−2) = Real.digits w g i`.  (For `w ∈ [1, g)`, `m = 0` and this is
`erdos482_resolution_literal`.) -/
theorem erdos482_resolution_general_literal (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw1 : 1 ≤ w) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ i : ℕ,
        gu g a b ε (2 * (i + (⌊Real.logb g w⌋).toNat + 2))
            - g * gu g a b ε (2 * (i + (⌊Real.logb g w⌋).toNat + 2) - 2)
          = ((Real.digits w g i : ℕ) : ℤ) := by
  have hw : (0 : ℝ) < w := by linarith
  -- m ≥ 0 since w ≥ 1 ⟹ logb g w ≥ 0
  have hgr : (1 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hlogb : 0 ≤ Real.logb g w := Real.logb_nonneg hgr hw1
  have hm0 : 0 ≤ ⌊Real.logb g w⌋ := Int.le_floor.mpr (by exact_mod_cast hlogb)
  set m : ℤ := ⌊Real.logb g w⌋ with hm
  obtain ⟨a, b, ε, hab, hrec⟩ := erdos482_resolution g hg w hw
  refine ⟨a, b, ε, hab, fun i => ?_⟩
  set t : ℝ := w / (g : ℝ) ^ m with ht
  set n : ℕ := i + m.toNat + 2 with hn
  have hn1 : 1 ≤ n := by omega
  -- the recurrence reads off the mantissa digit `Real.digits (t·g^{n−1}/g) g 0`
  have hstep := hrec n hn1
  rw [hstep]
  -- mantissa digit → literal digit of `t` (`digit_recon`, n ≥ 2) → digit of `w` (shift by m)
  rw [digit_recon g t (by rw [ht]; positivity) n (by omega)]
  -- `Real.digits t g (n−2) = Real.digits w g ((n−2) − m) = Real.digits w g i`
  have hk : m ≤ ((n - 2 : ℕ) : ℤ) := by
    have : ((n - 2 : ℕ) : ℤ) = (i : ℤ) + m := by
      rw [hn]; push_cast [Int.toNat_of_nonneg hm0]; omega
    omega
  rw [realDigits_mantissa_shift g w hw (n - 2) hk]
  -- the resulting index `(n−2) − m` is exactly `i`
  have hidx : (((n - 2 : ℕ) : ℤ) - m).toNat = i := by
    have h : ((n - 2 : ℕ) : ℤ) - m = (i : ℤ) := by
      have hn2 : n - 2 = i + m.toNat := by omega
      rw [hn2]; push_cast [Int.toNat_of_nonneg hm0]; ring
    rw [h, Int.toNat_natCast]
  rw [hidx]

end LeanGallery.NumberTheory.Erdos482.General
