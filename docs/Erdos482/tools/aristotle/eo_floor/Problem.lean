import Mathlib

open Real

/-
GOAL: the EVEN→ODD step of St05 Theorem 1.3's closed-form joint induction.

Setup (base g ≥ 2, t = base-g mantissa, 1 ≤ t < g):
  a = g / ((g-1)(t+g)),  ε with  -1/g ≤ ε < (g+1)(g-2)/g.
At even index 2k the recurrence value is the explicit integer
  V_k := g^k + ⌊t·g^k / g⌋          (= u_{2k+1}).
The step computes  gu(2k+1) = ⌊a·(V_k + ε)⌋  and the claim is that this equals the geometric
sum (g^k − 1)/(g−1); phrased without integer division as
  (g−1) · ⌊a·(V_k + ε)⌋ = g^k − 1.

PROOF (fully worked out — port it):
Let m := ⌊t·g^k/g⌋ = ⌊t·g^{k−1}⌋ and f := t·g^k/g − m ∈ [0,1)  (`Int.fract_nonneg`,
`Int.fract_lt_one`; note t·g^k/g = t·g^{k-1}).  Then V_k = g^k + m and
  a·(V_k + ε) = g·(g^k + m + ε) / ((g−1)(t+g)).
Multiply by (g−1) (> 0): KEY ALGEBRAIC IDENTITY
  (g−1)·a·(V_k + ε) = g·(g^k + m + ε)/(t+g) = g^k + g·(ε − f)/(t+g).
(Because g·(g^k + m + ε) = g·(g^k + t·g^k/g − f + ε) = g^k·(t+g) + g·(ε − f).)
So with Q := g^k + g·(ε − f)/(t+g):  a·(V_k+ε) ∈ [S, S+1)  ⟺  Q ∈ [g^k − 1, g^k + g − 2)
where S := (g^k−1)/(g−1).  The two bounds on g·(ε−f)/(t+g):
  LOWER  ≥ −1 :  g(ε−f) ≥ −(t+g).  Since gε ≥ −1 (from ε ≥ −1/g) and −gf > −g (from f < 1),
                 gε − gf > −1 − g ≥ −(t+g) because t ≥ 1.
  UPPER  < g−2 : g(ε−f) < (g−2)(t+g).  Since −gf ≤ 0 (f ≥ 0) and gε < (g+1)(g−2)
                 (from ε < (g+1)(g−2)/g), and (g+1)(g−2) ≤ (g−2)(t+g) because (g−2)(1−t) ≤ 0
                 (g ≥ 2, t ≥ 1).
Conclude with `Int.floor_eq_iff` (the ℤ version takes NO side hypothesis): show the floor equals S,
then multiply by (g−1).  Use `t + g > 0`, `g − 1 ≥ 1`, casts ℕ→ℤ→ℝ carefully.
-/

theorem eo_floor (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) (k : ℕ) :
    ((g : ℤ) - 1) * ⌊a * ((((g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ : ℤ) : ℝ) + ε)⌋
      = (g : ℤ) ^ k - 1 := by
  sorry
