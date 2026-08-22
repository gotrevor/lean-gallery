import Mathlib

open Real

/-
GOAL: the real-analysis CORE of St05 Thm 1.3's even→odd step — two inequalities, NO floor in the
conclusion (so this is pure inequality manipulation).

Setup: g ≥ 2, 1 ≤ t < g, a = g/((g-1)(t+g)), -1/g ≤ ε < (g+1)(g-2)/g.
`m : ℤ` is an arbitrary integer and `f : ℝ` its companion with the ONLY assumptions
  hf0 : 0 ≤ f,  hf1 : f < 1,  and  hmf : (m : ℝ) = t * (g:ℝ)^k / g - f
(i.e. m = ⌊t·g^k/g⌋, f its fractional part — but we only need these three facts).
CLAIM: with  V := (g:ℝ)^k + m,
  (g:ℝ)^k - 1 ≤ (((g:ℝ) - 1) * a) * (V + ε)   ∧   (((g:ℝ) - 1) * a) * (V + ε) < (g:ℝ)^k + (g:ℝ) - 2.

PROOF: KEY IDENTITY  ((g-1)·a)·(V+ε) = g·(g^k + m + ε)/(t+g) = g^k + g·(ε − f)/(t+g)
(substitute m = t·g^k/g − f; note t·g^k/g·g = t·g^k, and g^k·(t+g) cancels into g^k).
Then both bounds reduce to bounds on g·(ε−f)/(t+g):
  ≥ −1 :  gε ≥ −1 (ε ≥ −1/g),  −gf > −g (f < 1),  so gε − gf > −1 − g ≥ −(t+g) since t ≥ 1.
  < g−2 : −gf ≤ 0 (f ≥ 0),  gε < (g+1)(g−2) (ε bound),  (g+1)(g−2) ≤ (g−2)(t+g) since
          (g−2)(1−t) ≤ 0 (g ≥ 2, t ≥ 1).
Need t + g > 0 and g − 1 ≥ 1 (both from g ≥ 2, t ≥ 1).  `nlinarith`/`field_simp` friendly.
-/

theorem eo_ineq (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g)
    (k : ℕ) (m : ℤ) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1)
    (hmf : (m : ℝ) = t * (g : ℝ) ^ k / g - f) :
    (g : ℝ) ^ k - 1 ≤ (((g : ℝ) - 1) * a) * (((g : ℝ) ^ k + (m : ℝ)) + ε) ∧
      (((g : ℝ) - 1) * a) * (((g : ℝ) ^ k + (m : ℝ)) + ε) < (g : ℝ) ^ k + (g : ℝ) - 2 := by
  sorry
