/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Base-`g` mantissa (Stoll [St05], §1)

For a real `w > 0` and integer base `g ≥ 2`, the mantissa `t = w / g^m` with `m = ⌊log_g w⌋` lies in
`[1, g)`.  This is the normalisation feeding St05's recurrences (`General/Thm13`, `Thm12`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **The base-`g` mantissa lies in `[1, g)`.**  `m = ⌊log_g w⌋`, `t = w/g^m`, then `1 ≤ t < g`. -/
theorem mantissa_mem (g : ℕ) (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    1 ≤ w / (g : ℝ) ^ (⌊Real.logb g w⌋) ∧
      w / (g : ℝ) ^ (⌊Real.logb g w⌋) < (g : ℝ) := by
  set b : ℝ := (g : ℝ) with hbdef
  have hb1 : (1 : ℝ) < b := by rw [hbdef]; exact_mod_cast hg
  have hbpos : (0 : ℝ) < b := by linarith
  have hbne1 : b ≠ 1 := by linarith
  set m : ℤ := ⌊Real.logb b w⌋ with hm
  have hpow_pos : (0 : ℝ) < b ^ m := zpow_pos hbpos m
  -- b^m ≤ w
  have hle : b ^ m ≤ w := by
    have h1 : b ^ (m : ℝ) ≤ b ^ Real.logb b w :=
      (Real.rpow_le_rpow_left_iff hb1).mpr (Int.floor_le _)
    rwa [Real.rpow_intCast, Real.rpow_logb hbpos hbne1 hw] at h1
  -- w < b^(m+1)
  have hlt : w < b ^ (m + 1) := by
    have h2 : b ^ Real.logb b w < b ^ ((m : ℝ) + 1) :=
      (Real.rpow_lt_rpow_left_iff hb1).mpr (Int.lt_floor_add_one _)
    rw [Real.rpow_logb hbpos hbne1 hw] at h2
    have hcast : b ^ ((m : ℝ) + 1) = b ^ (m + 1) := by
      rw [← Real.rpow_intCast b (m + 1)]; push_cast; ring_nf
    rwa [hcast] at h2
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpow_pos]; linarith
  · rw [div_lt_iff₀ hpow_pos]
    have hsplit : b ^ (m + 1) = b * b ^ m := by rw [zpow_add_one₀ (by linarith)]; ring
    rw [hsplit] at hlt; linarith

/-- **Mantissa reconstruction.**  `t · g^m = w` (`m = ⌊log_g w⌋`, `t = w/g^m`): the mantissa scaled
back by `g^m` recovers `w`.  So `w` and `t` have the same base-`g` digits up to the shift by `m`. -/
theorem mantissa_reconstruct (g : ℕ) (hg : 2 ≤ g) (w : ℝ) :
    w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (⌊Real.logb g w⌋) = w := by
  have hbpos : (0 : ℝ) < (g : ℝ) := by positivity
  exact div_mul_cancel₀ w (zpow_ne_zero _ (ne_of_gt hbpos))

end LeanGallery.NumberTheory.Erdos482.General
