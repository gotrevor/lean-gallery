import Mathlib
open Real

/-
GOAL: For the single-internal-floor, divide-by-2 digit crux with multiplier β ∈ (0,2), the offset
c = 1/2 is FORCED.  I.e. if for ALL real x we have 0 ≤ {x} − β·{x/2} + c·β < 1 (Int.fract = {·}),
then c = 1/2.  (Existence of such c for β<2 is known: c=1/2 works; this is the uniqueness half.)

RECIPE (mirrors the √2 case `selfref_crux_offset_unique`):
  • Lower bound c ≥ 1/2 from x = 1:  Int.fract 1 = 0 (cast: Int.fract_intCast, or 1=((1:ℤ):ℝ)),
    Int.fract (1/2) = 1/2 (Int.fract_eq_self).  Lower crux ⇒ 0 ≤ 0 − β/2 + c·β ⇒ c·β ≥ β/2 ⇒ c ≥ 1/2
    (divide by β>0).
  • Upper bound c ≤ 1/2 from the family x = 1 − t, t ↓ 0 (use `le_of_forall_pos_le_add`):
    for 0 < t ≤ 1/2, Int.fract (1−t) = 1−t and Int.fract ((1−t)/2) = (1−t)/2 (Int.fract_eq_self,
    both in [0,1) since 1/2 ≤ 1−t < 1 and 1/4 ≤ (1−t)/2 < 1/2).  Upper crux ⇒
    (1−t) − β(1−t)/2 + c·β < 1 ⇒ c·β < t + β(1−t)/2 − 0 ... rearrange to  c·β < β/2 + t·(1 − β/2).
    Pick t = min (ε·β / (1 − β/2)) (1/2)-ish so the slack t·(1−β/2) ≤ ε·β, giving c·β ≤ β/2 + ε·β,
    hence c ≤ 1/2 + ε for every ε>0, so c ≤ 1/2.  (Need 1 − β/2 > 0 from β < 2.)
  • Conclude c = 1/2 by le_antisymm / linarith.
-/

theorem onefloor_div2_offset_unique (β : ℝ) (hβ0 : 0 < β) (hβ2 : β < 2) (c : ℝ)
    (hc : ∀ x : ℝ, 0 ≤ Int.fract x - β * Int.fract (x / 2) + c * β ∧
        Int.fract x - β * Int.fract (x / 2) + c * β < 1) :
    c = 1 / 2 := by
  sorry
