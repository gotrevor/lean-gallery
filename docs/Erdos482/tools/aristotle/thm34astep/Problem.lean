import Mathlib
open Real

/-
GOAL: St06 Theorem 3.4 GENUINE a-step floor crux at general ε (Stoll's actual 3.4, ε on the a-step).
For 1≤t<2, integer s≥1, integers m≥1, 1≤l≤m, k≥0, integer B with B ≤ t·s/2 < B+1, real a with
  a = (2k+1) + 2l/(t+2m), and real ε in Stoll's symmetric interval
  ½ − (m−l+½)/D₁ ≤ ε < ½ + (m−l+½)/D₁,  D₁ = (2m+1)(2k+1)+2l,
prove  ⌊a·((ms+B) + ε)⌋ = (2k+1)(ms+B) + k + l·s   (uniform over all such t — no Diophantine input).

RECIPE: D₁>0 by nlinarith. Clear the interval denominator:
  ½ − (m−l+½)/D₁ = ((2m+1)k+2l)/D₁  and  ½ + (m−l+½)/D₁ = (2m+1)(k+1)/D₁
(prove via eq_div_iff; ring), giving clean bounds  (2m+1)k+2l ≤ ε·D₁ < (2m+1)(k+1).
Two consequences (each: show 0 ≤ D₁·X by nlinarith with hlo'/hhi' scaled by (2k+1), then
  mul_nonneg_iff_of_pos_left):  hek : 0 ≤ (2k+1)ε − k   and   hek2 : 0 ≤ (k+1) − (2k+1)ε.
Then `rw [Int.floor_eq_iff]`. Let E = (2k+1)(ms+B)+k+l·s. Key identity (field_simp; ring after rw[ha]):
  (t+2m)·(a·((ms+B)+ε) − E) = ((t+2m)(2k+1)+2l)·ε − (t+2m)·k + l·(2B − t·s).
So a·((ms+B)+ε) − E = q := [that numerator]/(t+2m). Need 0 ≤ q < 1:
  • 0 ≤ numerator:  it equals  l·(2B+2 − t·s) + (t−1)·((2k+1)ε − k) + (ε·D₁ − ((2m+1)k+2l)) ≥ 0,
    nlinarith hints: hlo', mul_nonneg (0≤t−1) hek, mul_nonneg (0≤l) (0≤2B+2−t·s).
  • numerator < t+2m:  (t+2m) − numerator = l·(t·s−2B) + (t−1)·((k+1)−(2k+1)ε) + ((2m+1)(k+1) − ε·D₁) > 0,
    nlinarith hints: hhi', mul_nonneg (0≤t−1) hek2, mul_nonneg (0≤l) (0≤t·s−2B).
Finish ⟨by linarith, by linarith⟩ from q's bounds. The two interval endpoints are the independent
worst cases (t→1, 2B−t·s→−2) and (t→1, 2B−t·s→0), both binding at t=1 — that is why D₁ uses t=1.
-/

theorem st06_thm34_astep_eps
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (s : ℤ) (hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (a : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l)) :
    ⌊a * (((m * s + B : ℤ) : ℝ) + ε)⌋ = (2 * k + 1) * (m * s + B) + k + l * s := by
  sorry
