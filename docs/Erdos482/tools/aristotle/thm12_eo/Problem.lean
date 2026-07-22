import Mathlib

open Real

/-
GOAL: the EVEN→ODD step of St05 Theorem 1.2 **Case II** (binary, family parameter j ≥ 1).

Setup (g = 2, mantissa 1 ≤ t < 2, j ≥ 1, ε = 1/2 forced):  a = 2j − t/(t+2).
At even index 2k the recurrence value is the odd-index closed form  V_k := 2^k + ⌊t·2^k/2⌋
(written with /2, not 2^{k−1}, to avoid a negative exponent at k=0; same convention as Thm 1.3).
The step computes  ⌊a·(V_k + 1/2)⌋  and the claim is it equals the Case-II even-index closed form
  Q_k := j·2^{k+1} + (2j−1)·⌊t·2^k/2⌋ + (j−1).

PROOF (fully worked out — port it; the family parameter j CANCELS in the error term):
Let m := ⌊t·2^k/2⌋ and f := t·2^k/2 − m ∈ [0,1)  (`Int.floor_le`, `Int.lt_floor_add_one`).
Put P := 2^k + m + 1/2.  KEY: a·P − Q_k = 1 − (2f + t/2)/(t+2).
  a·P = 2j·P − t·P/(t+2);  2j·P = j·2^{k+1} + 2jm + j;  and
  t·P = t·2^k + t·m + t/2 = 2(m+f) + tm + t/2 = m(t+2) + 2f + t/2  (using t·2^k = 2·(t·2^k/2) = 2(m+f)),
  so t·P/(t+2) = m + (2f + t/2)/(t+2);  subtract Q_k = j·2^{k+1} + (2j−1)m + (j−1) — the j·2^{k+1}
  and 2jm terms cancel, leaving a·P − Q_k = m + 1 − (m + (2f+t/2)/(t+2)) = 1 − (2f+t/2)/(t+2).
Bounds (so ⌊a·P⌋ = Q_k via `Int.floor_eq_iff`, ℤ version, NO side hypothesis):
  • a·P − Q_k < 1  ⟺ (2f+t/2)/(t+2) > 0 : numerator ≥ t/2 > 0 (t ≥ 1), denom t+2 > 0.
  • a·P − Q_k ≥ 0  ⟺ (2f+t/2)/(t+2) ≤ 1 ⟺ 2f ≤ t/2 + 2 : f < 1 so 2f < 2 ≤ t/2 + 2.
Clear the denominator t+2 > 0 before `nlinarith`; casts ℕ→ℤ→ℝ carefully; use `t·2^k = 2·(t·2^k/2)`.
-/

theorem thm12_caseII_eo (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (a : ℝ) (ha : a = 2 * (j : ℝ) - t / (t + 2)) (k : ℕ) :
    ⌊a * ((((2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ : ℤ) : ℝ) + 1 / 2)⌋
      = (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1) := by
  sorry
