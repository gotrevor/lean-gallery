import Mathlib
open Real

/-
GOAL: For base g=2 the self-referential offset is unique: if  0 ≤ {x} − √2·{x/2} + c·√2 < 1  holds
for ALL real x (Int.fract = {·}), then c = 1/2.  (This is the offset-uniqueness companion to the
fact that the self-referential digit crux is solvable iff the base is 2.)

RECIPE: s=√2, s^2=2 (Real.sq_sqrt), s>0, 1≤s≤3/2 (nlinarith).
Lower bound c ≥ 1/2 : apply hc at x=1.  Int.fract 1 = 0 (Int.fract_natCast via 1=((1:ℕ):ℝ)),
  Int.fract (1/2) = 1/2 (Int.fract_eq_self).  Then hc(1).1 : 0 ≤ 0 − s·(1/2) + c·s, nlinarith with s>0.
Upper bound c ≤ 1/2 : le_of_forall_pos_le_add; fix ε>0, set K=(1−s/2)/s>0, t=min(ε/K)(1/2)>0, t<1.
  Apply hc at x = 1−t.  Int.fract (1−t) = 1−t and Int.fract ((1−t)/2) = (1−t)/2 (Int.fract_eq_self,
  since 0<1−t<1 and 0<(1−t)/2<1/2).  hc(1−t).2 ⇒  c·s < s/2 + t·(1 − s/2).  Show t·(1−s/2) ≤ ε·s
  (from t ≤ ε/K and K=(1−s/2)/s, via div_div_eq_mul_div / div_mul_cancel₀), then nlinarith ⇒ c ≤ 1/2+ε.
Conclude c = 1/2 by linarith from the two bounds.
-/

theorem selfref_crux_offset_unique (c : ℝ)
    (hc : ∀ x : ℝ, 0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + c * Real.sqrt 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + c * Real.sqrt 2 < 1) :
    c = 1 / 2 := by
  sorry
