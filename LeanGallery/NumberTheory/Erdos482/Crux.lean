/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

namespace LeanGallery.NumberTheory.Erdos482
open Real

/-- The crux universal inequality (Stoll eq (7), generalized): for every real `x`,
`0 ≤ {x} − √2·{x/2} + √2/2 < 1`.  Proof: case-split on parity of `⌊x⌋` (so `{x} = 2{x/2}` or
`2{x/2} − 1`), then `nlinarith` with `√2² = 2`, `1 ≤ √2 ≤ 3/2`.  No mathlib lemma supplies this. -/
theorem crux (x : ℝ) :
    0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 < 1 := by
  -- √2 facts
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  set s := Real.sqrt 2 with hsdef
  -- fract facts
  set f := Int.fract x with hf
  set g := Int.fract (x / 2) with hg
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  have hg0 : 0 ≤ g := Int.fract_nonneg (x / 2)
  have hg1 : g < 1 := Int.fract_lt_one (x / 2)
  -- parity integer m := ⌊x⌋ - 2⌊x/2⌋, with f = 2g - m
  set m : ℤ := ⌊x⌋ - 2 * ⌊x / 2⌋ with hm
  have key : f = 2 * g - (m : ℝ) := by
    rw [hf, hg, hm]
    push_cast
    rw [← Int.self_sub_floor x, ← Int.self_sub_floor (x / 2)]
    ring
  -- m ∈ {0,1}
  have hmval : (m : ℝ) = 2 * g - f := by linarith [key]
  have hub : (m : ℝ) < 2 := by rw [hmval]; linarith
  have hlb : (-1 : ℝ) < (m : ℝ) := by rw [hmval]; linarith
  have hm01 : m = 0 ∨ m = 1 := by
    have a1 : m < 2 := by exact_mod_cast hub
    have a2 : (-1 : ℤ) < m := by exact_mod_cast hlb
    omega
  rcases hm01 with h | h
  · -- m = 0 : f = 2g, so g < 1/2
    rw [h] at key
    push_cast at key
    have key' : f = 2 * g := by linarith [key]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - s) hg0, hs1, hs32]
    · nlinarith [mul_pos (by linarith : (0:ℝ) < 2 - s) (by linarith : (0:ℝ) < 1 / 2 - g), hs1, hs32]
  · -- m = 1 : f = 2g - 1, so g ≥ 1/2
    rw [h] at key
    push_cast at key
    have key' : f = 2 * g - 1 := by linarith [key]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - s) (by linarith : (0:ℝ) ≤ g - 1 / 2), hs1, hs32]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - s) (by linarith : (0:ℝ) ≤ g - 1 / 2), hs1, hs32]

end LeanGallery.NumberTheory.Erdos482

/-! # `LeanGallery.NumberTheory.Erdos482` (umbrella import) -/
