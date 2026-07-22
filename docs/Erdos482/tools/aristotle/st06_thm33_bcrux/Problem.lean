import Mathlib

open Real

/-
GOAL: the real-analysis CORE of Stoll [St06] (Acta Arith. 125 (2006)) Theorem 3.3's even→odd step
(the BINARY g=2 family, NOT covered by Thm 3.1).  NO floor in the conclusion: pure inequality.

Background.  St06 Thm 3.3 is a binary floor recurrence  u₁=m,
  u_{n+1}=⌊a(uₙ+½)⌋ (n odd),  u_{n+1}=⌊b(uₙ+ε)⌋ (n even),
with  a = 2k+1 + (t+2l)/(t+2m),  b = 2/a,  t∈[1,2) the binary mantissa of w, and the offset interval
  ½ − (2l+1)/(2(2m+1))  ≤  ε  <  ½ + (2l+1)/(2(2m+1))     (independent of k).
Its two closed forms are  u_{2n+1} = m·2ⁿ + ⌊t·2^{n−1}⌋  (odd index)  and
  u_{2n+2} = 2k(m·2ⁿ+⌊t·2^{n−1}⌋) + (m+l)·2ⁿ + ⌊t·2ⁿ⌋ + k     (even index).
The even→odd ("b") step  u_{2n+2} ↦ u_{2n+3}=⌊b(u_{2n+2}+ε)⌋  must land on the next odd value
  u_{2n+3} = m·2^{n+1} + ⌊t·2ⁿ⌋ = 2m·2ⁿ + ⌊t·2ⁿ⌋.
After Int.floor_eq_iff this is exactly the bound below (with s=2ⁿ; we keep s as a general integer ≥1
since only the floor/doubling relation 2B ≤ C ≤ 2B+1 is used — `B=⌊t·s/2⌋`, `C=⌊t·s⌋`).

PROOF SKETCH.  Write x := t·s/2 − B ∈ [0,1), y := t·s − C ∈ [0,1); from t·s = 2·(t·s/2) one gets
y = 2x − d where d := C − 2B ∈ {0,1} (the binary digit).  Let A := m·s + B (= u_{2n+1}).  The "a"
step gives  ⌊a(A+½)⌋ = E := 2kA+(m+l)s+C+k  with fractional part ρ = (a(A+½) − E) ∈ [0,1), and one
computes  ρ = [(m−l)y + (1−d)(l+m+t)] / (t+2m).  Since b = 2/a,
  b(E+ε) − (2ms+C) = (1−d) − b(ρ − ε).
Case d=0 (so y=2x, ρ=[(m−l)y+l+m+t]/(t+2m)):  the claim is  0 ≤ 1 − b(ρ−ε) < 1, i.e.
  0 < ρ − ε ≤ a/2;  the ε-interval (worst case t=1) gives exactly this.
Case d=1 (y=2x−1, ρ=(m−l)y/(t+2m)):  the claim is 0 ≤ b(ε−ρ) < 1, i.e. 0 ≤ ε − ρ < a/2.
All four sub-bounds bind at t=1 to the stated ε-endpoints; for t>1 they are strict with room.
`field_simp` (a>0, t+2m>0) then `nlinarith` with the floor bounds + the digit case split closes it.
-/

theorem st06_thm33_bcrux
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (s : ℤ) (hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (hk : 0 ≤ k)
    (B C : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (hC : (C : ℝ) ≤ t * s) (hC' : t * s < C + 1)
    (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - (2 * l + 1) / (2 * (2 * m + 1)) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + (2 * l + 1) / (2 * (2 * m + 1)))
    (a b : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) (hb : b = 2 / a) :
    0 ≤ b * (((2 * k * (m * s + B) + (m + l) * s + C + k : ℤ) : ℝ) + ε) - ((2 * m * s + C : ℤ) : ℝ)
      ∧ b * (((2 * k * (m * s + B) + (m + l) * s + C + k : ℤ) : ℝ) + ε) - ((2 * m * s + C : ℤ) : ℝ) < 1 := by
  sorry
