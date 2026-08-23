import Mathlib

/-
GOAL: the base-g mantissa lies in [1, g).  For an integer base g ≥ 2 and a real w > 0, set
m = ⌊log_g w⌋ and t = w / g^m.  Then 1 ≤ t < g.  (St05 §1: t is `w`'s base-g mantissa.)

Strategy: with b := (g:ℝ) > 1 and m := ⌊Real.logb b w⌋,
* g^m ≤ w : since m ≤ logb b w (Int.floor_le) and b>1, b^(m:ℝ) ≤ b^(logb b w) = w
  (Real.rpow_le_rpow_left_iff, Real.rpow_logb); convert b^(m:ℝ) to the zpow b^m via Real.rpow_intCast.
* w < g^(m+1) : since logb b w < m+1 (Int.lt_floor_add_one) and b>1, w = b^(logb b w) < b^((m:ℝ)+1)
  = b^(m+1).
Then 1 ≤ w/b^m ⟺ b^m ≤ w (le_div_iff₀, b^m>0 by zpow_pos), and w/b^m < g ⟺ w < b·b^m = b^(m+1).
-/

theorem mantissa_mem (g : ℕ) (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    1 ≤ w / (g : ℝ) ^ (⌊Real.logb g w⌋) ∧
      w / (g : ℝ) ^ (⌊Real.logb g w⌋) < (g : ℝ) := by
  sorry
