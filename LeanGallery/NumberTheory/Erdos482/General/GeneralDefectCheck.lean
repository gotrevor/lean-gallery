/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.GeneralDefect
import LeanGallery.NumberTheory.Erdos482.General.CubicDefect
import LeanGallery.NumberTheory.Erdos482.General.QuarticDefect

/-!
# Faithfulness: the cubic engine is the `d = 3` instance of the general one

The general degree-`d` defect engine (`GeneralDefect.lean`) is meant to subsume the hand-rolled,
independently-verified cubic engine (`CubicDefect.lean`).  This file machine-checks that subsumption on
the *map* level: the explicit three-fold-nested floor `cubicV3` is literally `dStepV … 3` for the
schedule `(c₀,c₁,c₂)`, and consequently the abstract `dStep_defect_identity` instantiates to the
already-proven cubic identity `cubicV3_sub_eq`.  This is a genuine cross-check (not a re-proof): it
validates that the general statement is the correct generalization of the verified special case.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

/-- The schedule `ℕ → ℝ` extending the cubic offsets `(c₀,c₁,c₂)`. -/
def cubicSched (c0 c1 c2 : ℝ) : ℕ → ℝ := fun k => if k = 0 then c0 else if k = 1 then c1 else c2

/-- **The cubic three-step map is the `d = 3` instance of the general `dStepV`.** -/
theorem cubicV3_eq_dStepV (α c0 c1 c2 : ℝ) (u : ℤ) :
    ((cubicV3 α c0 c1 c2 u : ℤ) : ℝ) = dStepV α (cubicSched c0 c1 c2) u 3 := by
  simp only [cubicV3, dStepV, cubicSched]
  norm_num

/-- The general schedule constant at `d = 3` is the cubic `C = 2c₀ + α²c₁ + αc₂` (using `α³ = 2`). -/
theorem cubic_dStepC_eq (α c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) :
    dStepC α (cubicSched c0 c1 c2) 3 = 2 * c0 + α ^ 2 * c1 + α * c2 := by
  have s0 : cubicSched c0 c1 c2 0 = c0 := rfl
  have s1 : cubicSched c0 c1 c2 1 = c1 := rfl
  have s2 : cubicSched c0 c1 c2 2 = c2 := rfl
  unfold dStepC
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    s0, s1, s2]
  simp only [Nat.sub_zero, Nat.reduceSub, pow_one, zero_add]
  linear_combination c0 * hα

/-- The general combined defect at `d = 3` is the cubic `cubicDefect`. -/
theorem cubic_dStepDefect_eq (α c0 c1 c2 : ℝ) (u : ℤ) :
    dStepDefect α (cubicSched c0 c1 c2) u 3 = cubicDefect α c0 c1 c2 u := by
  simp only [dStepDefect, dStepF, dStepV, cubicDefect, cubicSched, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

/-- **Faithfulness capstone: the general defect identity reproduces the cubic `cubicV3_sub_eq`.**  The
abstract `dStep_defect_identity` at `d = 3` is exactly the independently-proven cubic identity
`cubicV3 − 2u = (2c₀+α²c₁+αc₂) − cubicDefect`. -/
theorem cubicV3_sub_eq_via_general (α c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) (u : ℤ) :
    ((cubicV3 α c0 c1 c2 u : ℤ) : ℝ) - 2 * (u : ℝ)
      = (2 * c0 + α ^ 2 * c1 + α * c2) - cubicDefect α c0 c1 c2 u := by
  have hid := dStep_defect_identity α (cubicSched c0 c1 c2) u 3 hα
  rw [cubicV3_eq_dStepV, hid, cubic_dStepC_eq α c0 c1 c2 hα, cubic_dStepDefect_eq]; ring

/-- The schedule `ℕ → ℝ` extending the quartic offsets `(c₀,c₁,c₂,c₃)`. -/
def quarticSched (c0 c1 c2 c3 : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else c3

/-- **The quartic four-step map is the `d = 4` instance of the general `dStepV`.** -/
theorem quarticV4_eq_dStepV (α c0 c1 c2 c3 : ℝ) (u : ℤ) :
    ((quarticV4 α c0 c1 c2 c3 u : ℤ) : ℝ) = dStepV α (quarticSched c0 c1 c2 c3) u 4 := by
  simp only [quarticV4, dStepV, quarticSched]
  norm_num

/-- The general schedule constant at `d = 4` is the quartic `C = 2c₀ + α³c₁ + α²c₂ + αc₃` (`α⁴ = 2`). -/
theorem quartic_dStepC_eq (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) :
    dStepC α (quarticSched c0 c1 c2 c3) 4 = 2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3 := by
  have s0 : quarticSched c0 c1 c2 c3 0 = c0 := rfl
  have s1 : quarticSched c0 c1 c2 c3 1 = c1 := rfl
  have s2 : quarticSched c0 c1 c2 c3 2 = c2 := rfl
  have s3 : quarticSched c0 c1 c2 c3 3 = c3 := rfl
  unfold dStepC
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, s0, s1, s2, s3]
  simp only [Nat.sub_zero, Nat.reduceSub, pow_one, zero_add]
  linear_combination c0 * hα

/-- The general combined defect at `d = 4` is the quartic `quarticDefect`. -/
theorem quartic_dStepDefect_eq (α c0 c1 c2 c3 : ℝ) (u : ℤ) :
    dStepDefect α (quarticSched c0 c1 c2 c3) u 4 = quarticDefect α c0 c1 c2 c3 u := by
  simp only [dStepDefect, dStepF, dStepV, quarticDefect, quarticSched, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

/-- **Faithfulness capstone (quartic): the general defect identity reproduces `quarticV4_sub_eq`.** -/
theorem quarticV4_sub_eq_via_general (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ) :
    ((quarticV4 α c0 c1 c2 c3 u : ℤ) : ℝ) - 2 * (u : ℝ)
      = (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) - quarticDefect α c0 c1 c2 c3 u := by
  have hid := dStep_defect_identity α (quarticSched c0 c1 c2 c3) u 4 hα
  rw [quarticV4_eq_dStepV, hid, quartic_dStepC_eq α c0 c1 c2 c3 hα, quartic_dStepDefect_eq]; ring

end LeanGallery.NumberTheory.Erdos482.General
