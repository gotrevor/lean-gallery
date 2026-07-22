import Mathlib
open Real

/-
GOAL: The self-referential digit crux fails for every base g ≥ 3.  For each integer g ≥ 3 and each
real offset c, exhibit a real x violating  0 ≤ {x} − √g·{x/g} + c·√g < 1  (Int.fract = {·}).
(For g=2, c=1/2 this inequality DOES hold for all x — the Graham–Pollak crux — so g=2 is special.)

RECIPE: set s = √g, with s^2 = g (Real.sq_sqrt), s>0 (Real.sqrt_pos), and from g≥3 derive 1<s and
s<g (nlinarith; for s<g use s>1 ⇒ s<s^2=g). `by_contra h; push_neg at h` gives h : ∀ x, (crux x).
Two witnesses:
  • x = g−1 :  Int.fract (g−1) = 0  (it's a nat cast: Int.fract_natCast), and
    Int.fract ((g−1)/g) = (g−1)/g  (Int.fract_eq_self, since 0 ≤ (g−1)/g < 1).
    Lower bound ⇒  s·((g−1)/g) ≤ c·s ; clear /g via div_le_iff₀ to get  s·(g−1) ≤ c·s·g.
  • x = 1/2 :  Int.fract (1/2) = 1/2, Int.fract ((1/2)/g) = (1/2)/g (both Int.fract_eq_self).
    Upper bound ⇒  1/2 − s·((1/2)/g) + c·s < 1 ; multiply by 2g (mul_lt_mul_of_pos_right) and
    simplify (field_simp) to  g − s + 2·(c·s·g) < 2g.
Combine: from the two, linearly,  2·(s·g) − 3s − g < 0.  Substitute g = s^2 and use s>0 to get
2g − s − 3 < 0 (i.e. multiply through by s: s·(2g−s−3) < 0).  But for g≥3, s<g gives
2g − s − 3 > g − 3 ≥ 0 — contradiction.  Finish with nlinarith [..., hs2, s<g, 3≤g].
-/

theorem selfref_crux_fails_of_three_le (g : ℕ) (hg : 3 ≤ g) (c : ℝ) :
    ∃ x : ℝ, ¬ (0 ≤ Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g ∧
        Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g < 1) := by
  sorry
