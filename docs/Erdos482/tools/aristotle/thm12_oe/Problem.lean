import Mathlib

open Real

/-
GOAL: the ODD→EVEN step of St05 Theorem 1.2 **Case II** (binary, family parameter j ≥ 1).

Setup (g = 2, mantissa 1 ≤ t < 2, j ≥ 1, ε = 1/2):  a = 2j − t/(t+2), b = 2/a.
Note a = ((2j−1)t + 4j)/(t+2), so b = 2(t+2)/((2j−1)t + 4j).  Write Den := (2j−1)t + 4j (≥ 5 > 0).
At odd index 2k+1 the recurrence value is the Case-II even-index closed form
  Q := j·2^{k+1} + (2j−1)·⌊t·2^k/2⌋ + (j−1).
The step computes ⌊b·(Q + 1/2)⌋ and the claim is it equals the next odd-index closed form
  2^{k+1} + ⌊t·2^{k+1}/2⌋   (= 2^{k+1} + ⌊t·2^k⌋).

PROOF (worked out — port it; a case split on the fractional part is needed):
Let m := ⌊t·2^k/2⌋ and f := t·2^k/2 − m ∈ [0,1).  Then t·2^k = 2(m+f), so
  ⌊t·2^{k+1}/2⌋ = ⌊t·2^k⌋ = 2m + ⌊2f⌋,  with ⌊2f⌋ ∈ {0,1}  (0 if f<1/2, 1 if f≥1/2).
KEY ERROR IDENTITY:  b·(Q + 1/2) − (2^{k+1} + 2m + ⌊2f⌋) = 1 − ⌊2f⌋ + (4f − 2)/Den.
  (Derivation: b·(Q+1/2) = 2(t+2)(Q+1/2)/Den; expand Q; the j·2^{k+1} and (2j−1)m terms combine with
   Den = (2j−1)t+4j so that, after subtracting 2^{k+1}+2m, only 1 − ⌊2f⌋ + (4f−2)/Den remains.)
Bounds (⌊·⌋ via `Int.floor_eq_iff`, ℤ, no side hyp), Den > 0, two cases:
  • f < 1/2 (⌊2f⌋ = 0): error = 1 + (4f−2)/Den.  < 1 since 4f−2 < 0; ≥ 0 since 4f−2 ≥ −2 ≥ −Den.
  • f ≥ 1/2 (⌊2f⌋ = 1): error = (4f−2)/Den.  ≥ 0 since 4f−2 ≥ 0; < 1 since 4f−2 < 2 ≤ Den.
Use `Den ≥ 5` (from j ≥ 1, t ≥ 1: (2j−1)t+4j ≥ 1·1+4).  Clear Den > 0 before `nlinarith`.
You may find it easiest to first establish the two floor facts about ⌊t·2^k/2⌋ and ⌊t·2^{k+1}/2⌋
(`Int.floor_le`, `Int.lt_floor_add_one`, and `t·2^{k+1} = 2·t·2^k`), then split on `f < 1/2`.
-/

theorem thm12_caseII_oe (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (a b : ℝ) (ha : a = 2 * (j : ℝ) - t / (t + 2)) (hb : b = 2 / a) (k : ℕ) :
    ⌊b * (((((j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1)) : ℤ) : ℝ)
        + 1 / 2)⌋
      = (2 : ℤ) ^ (k + 1) + ⌊t * (2 : ℝ) ^ (k + 1) / 2⌋ := by
  sorry
