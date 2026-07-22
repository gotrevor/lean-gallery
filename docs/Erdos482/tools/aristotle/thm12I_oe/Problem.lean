import Mathlib

open Real

/-
GOAL: ODD→EVEN step of St05 Theorem 1.2 **Case I** (binary, family j ≥ 1, ε-INTERVAL [1/3, 2/3)).

Setup: g = 2, mantissa 1 ≤ t < 2, j ≥ 1, ε with 1/3 ≤ ε < 2/3.  a = 2j − 2/(t+2), b = 2/a.
Note a = (2j(t+2) − 2)/(t+2) = 2(j(t+2) − 1)/(t+2), so b = (t+2)/Den1 with Den1 := j(t+2) − 1 (≥ 2 > 0).
Let m := ⌊t·2^k/2⌋, p := ⌊t·2^k⌋;  from 2m ≤ t·2^k < 2m+2 one gets p ∈ {2m, 2m+1}.
At odd index 2k+1 the recurrence value is the Case-I even closed form
  C := 2^k + p + (j−1)·(2^{k+1} + 2m + 1).
The step computes ⌊b·(C + ε)⌋ and the claim is it equals the next odd-index value
  2^{k+1} + ⌊t·2^{k+1}/2⌋   (= 2^{k+1} + p, since ⌊t·2^{k+1}/2⌋ = ⌊t·2^k⌋ = p).

PROOF (worked out — port it; the digit extraction is ε-uniform):
KEY: Den1·(b·(C+ε) − (2^{k+1}+p)) = −t·2^k + p + (j−1)(t+2)(2m − p) + (t+2)(j−1) + (t+2)ε.
(Den1·b = t+2; expand C; the 2^{k+1} terms collapse to −t·2^k via 2 − (t+2) = −t.)
Case split on p:
  • p = 2m  (so t·2^k ∈ [2m, 2m+1), i.e. 2m ≤ t·2^k < p+1):  2m − p = 0, so
    Den1·err = (2m − t·2^k) + (t+2)(j−1) + (t+2)ε.
      ≥ 0: (t+2)ε ≥ (t+2)/3 ≥ 1 (t ≥ 1), and 2m − t·2^k > −1, (t+2)(j−1) ≥ 0.
      < Den1 = j(t+2)−1: since 2m − t·2^k ≤ 0 and (t+2)(j−1+ε) < j(t+2) − 1 ⟺ (t+2)(1−ε) > 1,
        which holds as 1−ε > 1/3 and t+2 ≥ 3.
  • p = 2m+1  (so t·2^k ∈ [2m+1, 2m+2), i.e. p ≤ t·2^k < p+1):  2m − p = −1, the (j−1)(t+2) terms
    cancel, Den1·err = (2m+1 − t·2^k) + (t+2)ε = (p − t·2^k) + (t+2)ε.
      ≥ 0: (t+2)ε ≥ 1, p − t·2^k > −1.
      < Den1: (t+2)ε < (t+2)·2/3 ≤ (t+2) − 1 ≤ Den1 (since (t+2)/3 ≥ 1, i.e. (1/3)(t+2) ≥ 1).
Conclude ⌊b·(C+ε)⌋ = 2^{k+1}+p via `Int.floor_eq_iff` (ℤ, no side hyp); clear Den1 > 0 before
`nlinarith`.  Use `t·2^{k+1}/2 = t·2^k` and `2 ≤ t+2`, `Den1 ≥ 2`.
-/

theorem thm12_caseI_oe (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (ε a b : ℝ) (hε0 : 1 / 3 ≤ ε) (hε1 : ε < 2 / 3)
    (ha : a = 2 * (j : ℝ) - 2 / (t + 2)) (hb : b = 2 / a) (k : ℕ) :
    ⌊b * ((((2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k⌋
            + ((j : ℤ) - 1) * (2 ^ (k + 1) + 2 * ⌊t * (2 : ℝ) ^ k / 2⌋ + 1) : ℤ) : ℝ) + ε)⌋
      = (2 : ℤ) ^ (k + 1) + ⌊t * (2 : ℝ) ^ (k + 1) / 2⌋ := by
  sorry
