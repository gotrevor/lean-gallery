/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm13Closed
import LeanGallery.NumberTheory.Erdos482.General.Mantissa
import LeanGallery.NumberTheory.Erdos482.General.St06Example
import LeanGallery.NumberTheory.Erdos482.General.St06Thm31
import LeanGallery.NumberTheory.Erdos482.General.St06Thm33
import LeanGallery.NumberTheory.Erdos482.General.St06Thm34
import LeanGallery.NumberTheory.Erdos482.General.St06Cor35
import LeanGallery.NumberTheory.Erdos482.General.SelfRefWall
import LeanGallery.NumberTheory.Erdos482.General.CubicDefect
import LeanGallery.NumberTheory.Erdos482.General.DoublingOrbit
import LeanGallery.NumberTheory.Erdos482.General.WeylDoubling
import LeanGallery.NumberTheory.Erdos482.General.BaseGWeyl
import LeanGallery.NumberTheory.Erdos482.General.Equidistribution
import LeanGallery.NumberTheory.Erdos482.General.DELEngine
import LeanGallery.NumberTheory.Erdos482.General.DoublingEquidist
import LeanGallery.NumberTheory.Erdos482.General.BaseGEquidist
import LeanGallery.NumberTheory.Erdos482.General.MultidimWeyl
import LeanGallery.NumberTheory.Erdos482.General.EquidistDense
import LeanGallery.NumberTheory.Erdos482.General.CubicTorusEquidist
import LeanGallery.NumberTheory.Erdos482.General.CubicDefectLink
import LeanGallery.NumberTheory.Erdos482.General.CubicFinish
import LeanGallery.NumberTheory.Erdos482.General.QuarticDefect
import LeanGallery.NumberTheory.Erdos482.General.QuarticDefectLink
import LeanGallery.NumberTheory.Erdos482.General.QuarticFinish
import LeanGallery.NumberTheory.Erdos482.General.RpowLinIndep
import LeanGallery.NumberTheory.Erdos482.General.RpowWindow
import LeanGallery.NumberTheory.Erdos482.General.GeneralDefect
import LeanGallery.NumberTheory.Erdos482.General.GeneralDefectCheck
import LeanGallery.NumberTheory.Erdos482.General.GeneralOrbit
import LeanGallery.NumberTheory.Erdos482.General.GeneralTorusEquidist
import LeanGallery.NumberTheory.Erdos482.General.BaseGTorusEquidist
import LeanGallery.NumberTheory.Erdos482.General.GaryExpansion
import LeanGallery.NumberTheory.Erdos482.General.GeneralTorusFinish
import LeanGallery.NumberTheory.Erdos482.General.BaseGFinish
import LeanGallery.NumberTheory.Erdos482.General.BaseGSubsumes
import LeanGallery.NumberTheory.Erdos482.General.GeneralSubsumes

/-!
# Erdős–Graham #482 — the general resolution (any `w > 0`, any base `g ≥ 2`)

The headline deliverable of the St05 track, packaged as one statement.  Given any real `w > 0` and any
integer base `g ≥ 2`, there is an explicit floor-recurrence `gu g a b ε` (with `a·b = g`, built from the
base-`g` mantissa `t = w / g^{⌊log_g w⌋} ∈ [1, g)`) whose Graham–Pollak difference
`gu(2n) − g·gu(2n−2)` is exactly the `n`-th base-`g` digit of `w` (as the mathlib digit
`Real.digits (t·g^{n−1}/g) g 0`).  This is Erdős–Graham's "similar results for √m and other algebraic
numbers" — made fully explicit and machine-checked.  Inherits `thm13_digits`: axiom-clean.

We take the offset `ε = −1/g`, which lies in St05's admissible range `[−1/g, (g+1)(g−2)/g)` for **every**
`g ≥ 2` (at `g = 2` the range is `[−1/2, 0)`, so `ε = 0` would fail — `ε = −1/g` is the safe uniform
witness).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **Erdős–Graham #482, resolved in full generality.**  For any `w > 0` and integer base `g ≥ 2`,
with mantissa `t = w/g^{⌊log_g w⌋}`, there exist coefficients `a, b, ε` (with `a·b = g`) so that the
recurrence `gu g a b ε` reads off the base-`g` digits of `w`:
`gu(2n) − g·gu(2n−2) = Real.digits (t·g^{n−1}/g) g 0` for every `n ≥ 1`. -/
theorem erdos482_resolution (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 1 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits
              (w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by positivity
  have hg1 : (g : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  set t : ℝ := w / (g : ℝ) ^ (⌊Real.logb g w⌋) with ht
  obtain ⟨ht1, ht2⟩ := mantissa_mem g hg w hw
  have htg : t + (g : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ t := ht1; positivity
  refine ⟨(g : ℝ) / (((g : ℝ) - 1) * (t + g)), ((g : ℝ) - 1) * (t + g), -1 / (g : ℝ), ?_, ?_⟩
  · field_simp
  · intro n hn
    have hε0 : -1 / (g : ℝ) ≤ -1 / (g : ℝ) := le_refl _
    have hg2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have hε1 : -1 / (g : ℝ) < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g := by
      rw [div_lt_div_iff_of_pos_right hgpos]
      nlinarith [hg2, mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 2 by linarith)
        (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)]
    exact thm13_digits g hg t ht1 ht2 (-1 / (g : ℝ))
      ((g : ℝ) / (((g : ℝ) - 1) * (t + g))) (((g : ℝ) - 1) * (t + g)) rfl rfl hε0 hε1 n hn

/-- **Erdős–Graham #482 — literal-digit form for `w ∈ [1, g)`.**  When `w` is already its own base-`g`
mantissa (`1 ≤ w < g`), the recurrence reads off `w`'s genuine mathlib base-`g` digits:
`gu(2n) − g·gu(2n−2) = Real.digits w g (n−2)` for every `n ≥ 2`. -/
theorem erdos482_resolution_literal (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ)
    (hw1 : 1 ≤ w) (hw2 : w < (g : ℝ)) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 2 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits w g (n - 2) : ℕ) : ℤ) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by positivity
  have hg2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (g : ℝ) - 1 ≠ 0 := by linarith
  have htg : w + (g : ℝ) ≠ 0 := by positivity
  refine ⟨(g : ℝ) / (((g : ℝ) - 1) * (w + g)), ((g : ℝ) - 1) * (w + g), -1 / (g : ℝ), by field_simp, ?_⟩
  intro n hn
  have hε1 : -1 / (g : ℝ) < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g := by
    rw [div_lt_div_iff_of_pos_right hgpos]
    nlinarith [hg2, mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 2 by linarith)
      (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)]
  rw [thm13_digits g hg w hw1 hw2 (-1 / (g : ℝ)) _ _ rfl rfl (le_refl _) hε1 n (by omega)]
  exact digit_recon g w (by linarith) n hn

end LeanGallery.NumberTheory.Erdos482.General
