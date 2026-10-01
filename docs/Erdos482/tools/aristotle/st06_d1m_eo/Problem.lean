/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

open Real

/-
GOAL: the real-analysis CORE of Stoll [St06] (Acta Arith. 125 (2006)) Theorem 3.1's even→odd step for
subcone 𝒟₁⁻ (cone 𝒜₁: l < 0; sign k < 0).  NO floor in the conclusion — pure inequality manipulation.

This is the `l < 0` companion to the already-formalized 𝒟₂ cores.  The even→odd induction step of St06
Thm 3.1 reduces (after substituting the two closed forms) to a two-sided bound on `l/(g−1) + a·(ε − f)`,
`f ∈ [0,1)` the fractional part, `a` the odd-step coefficient.

Setup (subcone 𝒟₁⁻):  g ≥ 3, 1 ≤ t < g, integers m ≥ 1, l < 0, k < 0, and
`a = klg/((g−1)(t+mg))`.  Here `kl > 0` so `a > 0`.  The St06 ε-interval for 𝒟₁⁻ (corrected — the
upper endpoint has NO "+1"; verified numerically over ~30k points, see notes/ST06-THM31-ERRATUM.md) is
  1 − (m+1)/k  ≤  ε  <  (g−l−1)(mg+1)/(klg).

CLAIM: for every f with 0 ≤ f < 1,
  0 ≤ (l:ℝ)/((g:ℝ)−1) + a·(ε − f)   ∧   (l:ℝ)/((g:ℝ)−1) + a·(ε − f) < 1.

PROOF SKETCH.  `a > 0`, so the expression is decreasing in f; check the two endpoints f=0 and f→1.
Multiply the core by `(g−1)(t+mg) > 0` to get `l(t+mg) + klg(ε−f)`; the bound reduces to:
  • lower (f→1, the inf): `0 ≤ l(t+mg) + klg(ε−1)`, using `ε ≥ 1 − (m+1)/k` ⟹ `klg(ε−1) ≥ klg·(−(m+1)/k) = −(m+1)lg`, and `l(t+mg) − (m+1)lg = l(t − g) ≥ 0` since `l < 0`, `t < g`.
  • upper (f=0, the sup): `l(t+mg) + klg·ε < (g−1)(t+mg)`, using `ε < (g−l−1)(mg+1)/(klg)` ⟹ `klg·ε < (g−l−1)(mg+1)`, and `l(t+mg) + (g−l−1)(mg+1) ≤ (g−1)(t+mg)` ⟺ `(g−l−1)(mg+1) ≤ (g−1−l)(t+mg)` ⟺ `(g−1−l)(1−t) ≤ 0` (true: `g−1−l > 0` since `l<0`, `1−t ≤ 0`).
Need `t+mg > 0` (from m ≥ 1, t ≥ 1), `g − 1 ≥ 2`, `k ≤ −1`, `l ≤ −1`.  `field_simp`/`nlinarith` friendly.
-/

theorem st06_d1m_eo (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : l < 0) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  sorry
