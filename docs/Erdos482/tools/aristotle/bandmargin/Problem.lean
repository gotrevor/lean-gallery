import Mathlib

/-
Context: in our repo we have proven (kernel-verified, axiom-clean) that √2 is badly approximable
with explicit constant.  We inline it here as an axiom so this problem is self-contained:
-/
axiom sqrt2_badly_approximable (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) / (3 * q) ≤ |(q : ℝ) * Real.sqrt 2 - p|

/-
GOAL: quantitative band-avoidance for √2's binary orbit.

The pair-5 ε-step (Stoll's "A fancy way…", §4) is governed by how close `{√2·2^n}` comes to `½`.
This lemma gives an explicit lower bound on the distance from `√2·2^n` to EVERY half-integer
`p + ½` (`p : ℤ`):

    1 / (3 · 2^(n+2))  ≤  |√2·2^n − (p + ½)|.

Proof: apply `sqrt2_badly_approximable` with `q = 2^(n+1)` (so `q ≥ 1`) and numerator `2p+1`:
`1/(3·2^(n+1)) ≤ |2^(n+1)·√2 − (2p+1)|`.  Since `2^(n+1)·√2 − (2p+1) = 2·(√2·2^n − (p+½))`,
the RHS is `2·|√2·2^n − (p+½)|`; divide by 2.  Watch the casts: `((2:ℕ)^(n+1) : ℝ) = 2^(n+1)`.
-/

theorem sqrt2_pow_far_from_halfint (n : ℕ) (p : ℤ) :
    (1 : ℝ) / (3 * 2 ^ (n + 2)) ≤ |Real.sqrt 2 * 2 ^ n - ((p : ℝ) + 1 / 2)| := by
  sorry
