import Mathlib

open Real

/-
GOAL: St06 Corollary 3.5 ENGINE — the Graham–Pollak recurrence started at the Beatty value
m = r + ⌊r√2/2⌋ reads off the binary digits of r·√2.  This generalizes the classical Graham–Pollak
`gp_pair` (the r=1 case) by a free factor r ∈ ℕ.

Recurrence (0-indexed): su 0 = m, su (n+1) = ⌊√2·(su n + 1/2)⌋ (UNIFORM — both parities identical).
Start m = (r : ℤ) + ⌊(r:ℝ)·√2/2⌋ = ⌊r(1+1/√2)⌋ (the Beatty sequence value).

CLOSED FORMS (prove ∀ j by induction):
  (Odd_j)  su (2j+1) = ⌊√2·r·2^j⌋ + r·2^j
  (Even_j) su (2j+2) = ⌊√2·r·2^j⌋ + r·2^(j+1)

Two universal floor facts are provided as axioms (both proved elementarily in the host repo from
√2·√2 = 2 and 1 ≤ √2 ≤ 3/2):
  crux  x : 0 ≤ {x} − √2·{x/2} + √2/2 < 1                      (Int.fract)
  eqA   w (0≤w<1) : 0 ≤ w·(1−√2) + √2/2 < 1

PROOF RECIPE:
* su_succ collapses to `su (n+1) = ⌊√2·(su n + 1/2)⌋` for all n (the if-branches are identical).
* BASE su1: su 1 = ⌊√2·r⌋ + r.  From su 0 = r + ⌊√2 r/2⌋, write
    √2·((↑(r+⌊√2 r/2⌋))+1/2) = ↑(⌊√2 r⌋+r) + ({√2 r} − √2·{√2 r/2} + √2/2)
  (algebra: uses √2·√2=2; {√2 r/2}=√2 r/2−⌊√2 r/2⌋, {√2 r}=√2 r−⌊√2 r⌋).  The bracket is in [0,1)
  by `crux (√2·r)` (note (√2 r)/2 = √2 r/2).  Then Int.floor_intCast_add + Int.floor_eq_zero_iff.
* floorA p :  ⌊√2·((↑(⌊√2 r 2^p⌋ + r·2^p))+1/2)⌋ = ⌊√2 r 2^p⌋ + r·2^(p+1).   [odd→even]
    Algebra: √2·(⌊√2 r 2^p⌋ + r 2^p + 1/2) = ↑(⌊√2 r 2^p⌋+r2^(p+1)) + ({√2 r 2^p}·(1−√2)+√2/2).
    Bracket in [0,1) by `eqA {√2 r 2^p}`.  (su 2 is floorA at p=0.)
* floorB p :  ⌊√2·((↑(⌊√2 r 2^p⌋ + r·2^(p+1)))+1/2)⌋ = ⌊√2 r 2^(p+1)⌋ + r·2^(p+1).  [even→odd]
    Algebra: = ↑(⌊√2 r 2^(p+1)⌋+r2^(p+1)) + ({√2 r 2^(p+1)} − √2·{√2 r 2^p} + √2/2);
    bracket in [0,1) by `crux (√2 r 2^(p+1))` (note √2 r 2^(p+1)/2 = √2 r 2^p).
* Induction on j: base j=0 = (su1, floorA 0); step uses floorB p=j (→ Odd_{j+1}) then floorA p=j+1
  (→ Even_{j+1}).  Index bookkeeping: 2*(j+1)+1 = (2j+2)+1, etc.  Casts ℤ→ℝ via the IH equalities.
-/

axiom crux (x : ℝ) :
    0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 < 1

axiom eqA {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) :
    0 ≤ w * (1 - Real.sqrt 2) + Real.sqrt 2 / 2 ∧
      w * (1 - Real.sqrt 2) + Real.sqrt 2 / 2 < 1

theorem cor35_pair (r : ℕ) (su : ℕ → ℤ)
    (hsu0 : su 0 = (r : ℤ) + ⌊(r : ℝ) * Real.sqrt 2 / 2⌋)
    (hrec : ∀ n, su (n + 1) = ⌊Real.sqrt 2 * ((su n : ℝ) + 1 / 2)⌋) :
    ∀ j : ℕ,
      su (2 * j + 1) = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ + (r : ℤ) * 2 ^ j ∧
      su (2 * j + 2) = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ + (r : ℤ) * 2 ^ (j + 1) := by
  sorry
