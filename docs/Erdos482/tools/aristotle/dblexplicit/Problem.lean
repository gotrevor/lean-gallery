import Mathlib

/-
GOAL: the explicit branch form of the doubling map on a fractional value.

For `f ∈ [0,1)`, `Int.fract (2*f)` is `2*f` when `f < ½` and `2*f − 1` when `f ≥ ½`.
This makes the pair-5 band recurrence concrete (case split on the next binary digit):
the band bracket `{√2·2^j} − √2·{√2·2^{j−1}} + √2·ε` with `{√2·2^j} = fract(2·{√2·2^{j−1}})`
becomes, writing `f = {√2·2^{j−1}}`, either `(2−√2)f + √2ε`  (f<½) or `(2−√2)f − 1 + √2ε` (f≥½).

Hints: `Int.fract x = x − ⌊x⌋`; on `[0,1)`, `⌊2f⌋ = 0` iff `f < ½` and `= 1` iff `½ ≤ f`.
Use `Int.floor_eq_iff` / `Int.fract_eq_self` and the bounds.
-/

theorem fract_two_mul_branch (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    (f < 1 / 2 → Int.fract (2 * f) = 2 * f) ∧
      (1 / 2 ≤ f → Int.fract (2 * f) = 2 * f - 1) := by
  sorry
