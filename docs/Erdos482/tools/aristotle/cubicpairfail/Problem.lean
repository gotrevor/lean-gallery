import Mathlib
open Real

/-
GOAL: Conditional cubic impossibility. With the three-step cubic map's defect identity GIVEN as a
hypothesis (digit = C − defect), prove that if two starts' combined defects differ by more than 1, the
two digits cannot both be base-2 digits {0,1}.

This is the honest "ceiling" theorem: the cubic three-step digit map fails to read base-2 digits along
any orbit that realises a defect spread > 1.

RECIPE: from hd, hd' the two integer digits d, d' satisfy (d:ℝ) = C − Df, (d':ℝ) = C − Df'.  Then
(d:ℝ) − (d':ℝ) = Df' − Df, whose |·| > 1 (hwide, up to abs_sub_comm).  Cast: the integer gap
((d - d':ℤ):ℝ) has |·| > 1.  But if d,d' ∈ {0,1} then d - d' ∈ {-1,0,1}, contradiction (rcases the four
cases, `norm_num`/`omega`).
-/

theorem cubic_pair_fail (C Df Df' : ℝ) (d d' : ℤ)
    (hd  : (d  : ℝ) = C - Df)
    (hd' : (d' : ℝ) = C - Df')
    (hwide : 1 < |Df - Df'|) :
    ¬ ((d = 0 ∨ d = 1) ∧ (d' = 0 ∨ d' = 1)) := by
  sorry
