import Mathlib
open Real

/-
GOAL: {1, α, α²} are linearly independent over ℤ for α = 2^{1/3}.  Concretely: for integers a b c,
if (a : ℝ) + b·α + c·α² = 0 then a = 0 ∧ b = 0 ∧ c = 0.  This is the degree-3 fact (α has minimal
polynomial X³ − 2 over ℚ) that underpins Weyl equidistribution of the pair ({α·u}, {α²·u}) over the
integers — a prerequisite on the cubic self-referential frontier (Erdős #482 / Stoll St06 extension).

α := (2 : ℝ) ^ ((1:ℝ)/3), so α^3 = 2 and α is irrational.

ELEMENTARY RECIPE (avoids minpoly machinery — pure algebra + irrationality of 2^{1/3}):
Assume cα² + bα + a = 0 with α³ = 2.
  (1) cα² + bα + a = 0.
  (2) Multiply (1) by α and use α³ = 2:  bα² + aα + 2c = 0.
  Take b·(1) − c·(2):  (b² − ca)·α + (ab − 2c²) = 0.
  • If b² − ca ≠ 0 then α = (2c² − ab)/(b² − ca) ∈ ℚ, contradicting Irrational α.  So b² = ca and ab = 2c².
  • From b² = ca and ab = 2c²:  b³ = a·b·c = 2c³ (multiply b²=ca by b, and ab=2c² by c).  So b³ = 2c³
    in ℤ.  Then c = 0 (else (b/c)³ = 2 makes 2^{1/3} rational — contradiction; or use 2-adic valuation
    3·v₂(b) = 1 + 3·v₂(c), impossible mod 3).  With c = 0: b² = 0 so b = 0, then a = 0.
Useful: `Irrational ((2:ℝ) ^ ((1:ℝ)/3))` via `irrational_nrt_of_notint_nrt 3 2`; α^3 = 2 via
`Real.rpow_natCast`/`Real.rpow_mul`.  For b³ = 2c³ ⇒ c = 0, casting to ℝ gives (b:ℝ)³ = 2(c:ℝ)³, and if
c ≠ 0 then ((b:ℝ)/c)³ = 2 contradicts irrationality of the cube root of 2.
-/

theorem cubic_lin_indep_int (a b c : ℤ)
    (h : (a : ℝ) + b * ((2:ℝ) ^ ((1:ℝ)/3)) + c * ((2:ℝ) ^ ((1:ℝ)/3)) ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  sorry
