/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

open Real

/-
GOAL: the real-analysis CORE of Stoll [St06] (Acta Arith. 125 (2006)) Theorem 3.1's even→odd step,
for the subcone 𝒟₂⁻ (the cone that contains the showcase Example 1.1 — the ternary digits of e).
NO floor in the conclusion: this is pure inequality manipulation.

Background. St06 Thm 3.1 generalizes St05 to a 3-parameter (m,l,k) family of floor recurrences whose
Graham–Pollak differences read off the base-g digits of any w>0.  The even→odd induction step reduces
(after substituting the two closed forms u_{2n+1}=m·gⁿ+⌊t·g^{n−1}⌋ and u_{2n}=l(k·gⁿ−1)/(g−1)) to a
single two-sided bound on the quantity  l/(g−1) + a·(ε − f),  where f∈[0,1) is the fractional part of
t·gᵏ/g and a is the odd-step coefficient.  This lemma is exactly that bound for 𝒟₂⁻.

Setup (subcone 𝒟₂⁻):  g ≥ 3 (St06 Thm 3.1 excludes binary g=2), 1 ≤ t < g, integers m ≥ 1,
0 < l ≤ g−1, k < 0, and  a = klg/((g−1)(t+mg)).  The St06 ε-interval for 𝒟₂⁻ is
  1 + (g−l−1)(mg+1)/(klg)  ≤  ε  <  −(mg+1)/(kg).
(NOTE: numerically verified — the upper endpoint is −(mg+1)/(kg) with NO extra "+1"; an earlier
transcription of Def 2.4 erroneously wrote "ε < 1 + δ₂⁻".  Verified over ~1M (g,m,l,k,t,ε,f) points.)

CLAIM: for every f with 0 ≤ f < 1,
  0 ≤ (l:ℝ)/((g:ℝ)−1) + a·(ε − f)   ∧   (l:ℝ)/((g:ℝ)−1) + a·(ε − f) < 1.

PROOF SKETCH.  Note a < 0 (k<0, l>0, g≥3, t+mg>0), so `l/(g−1) + a(ε−f)` is increasing in f.
  • Lower (min at f=0):  l/(g−1) + aε ≥ 0.  Using the substitution a = klg/((g−1)(t+mg)) and the
    UPPER ε-bound ε < −(mg+1)/(kg), one gets aε > a·(−(mg+1)/(kg)) (a<0 flips), and
    a·(−(mg+1)/(kg)) = −(mg+1)l/((g−1)(t+mg)) ≥ −l/(g−1) since (mg+1)/(t+mg) ≤ 1 (t≥1).
  • Upper (sup at f→1, not attained):  l/(g−1) + a(ε−1) ≤ 1.  Using the LOWER ε-bound
    ε ≥ 1 + (g−l−1)(mg+1)/(klg), i.e. ε−1 ≥ (g−l−1)(mg+1)/(klg), and a<0:
    a(ε−1) ≤ a·(g−l−1)(mg+1)/(klg) = (g−l−1)(mg+1)/((g−1)(t+mg)) ≤ (g−1−l)/(g−1) = 1 − l/(g−1),
    again via (mg+1)/(t+mg) ≤ 1.
  Need t+mg > 0, g−1 ≥ 2, k ≤ −1, l ≥ 1 — all from the hypotheses.  `field_simp`/`nlinarith` friendly
  once a is substituted and the divisions by (t+mg)>0, (g−1)>0, (kg)<0 are cleared.
-/

theorem st06_d2m_eo (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  sorry
