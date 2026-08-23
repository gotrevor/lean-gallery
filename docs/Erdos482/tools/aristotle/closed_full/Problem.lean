import Mathlib

open Real

/-
GOAL: St05 Theorem 1.3's two closed forms from the recurrence, FROM SCRATCH (no helper axioms).
This duplicates `closed_assembly` but inlines the two single-step proofs, so it is a fully
independent second shot.  ALL arithmetic is worked out below — port it, do not re-derive.

Recurrence (0-indexed, gu 0 = 1; step from index n uses (a,ε) when n EVEN, (b,1/(g-1)) when n ODD),
a = g/((g-1)(t+g)), b = (g-1)(t+g) [so a·b = g], 1 ≤ t < g, -1/g ≤ ε < (g+1)(g-2)/g, g ≥ 2.
Closed forms:  (A_k) gu(2k) = g^k + ⌊t·g^k/g⌋ ;  (B_k) (g-1)·gu(2k+1) = g^k − 1.

Prove `∀ k, A_k ∧ B_k` by induction on k.

BASE A_0: gu 0 = 1; g^0 + ⌊t·g^0/g⌋ = 1 + ⌊t/g⌋ = 1 (since 1 ≤ t < g ⟹ ⌊t/g⌋ = 0).

STEP A_k ⟹ B_k  (index 2k Even, so gu(2k+1) = ⌊a·(gu 2k + ε)⌋, and gu 2k = g^k + m, m := ⌊t·g^k/g⌋):
  Let f := t·g^k/g − m ∈ [0,1).  KEY: (g−1)·a·(g^k + m + ε) = g^k + g·(ε−f)/(t+g)
  (since g·(g^k + t·g^k/g − f + ε) = g^k(t+g) + g(ε−f), divided by (t+g)).
  Bounds: −1 ≤ g(ε−f)/(t+g) < g−2  ⟹  a·(g^k+m+ε) ∈ [(g^k−1)/(g−1), …+1)  ⟹
  ⌊a·(g^k+m+ε)⌋ = (g^k−1)/(g−1), i.e. (g−1)·gu(2k+1) = g^k − 1.  [`Int.floor_eq_iff`, ℤ, no side hyp]
  • lower −1: gε ≥ −1, −gf > −g, gε−gf > −1−g ≥ −(t+g) since t ≥ 1.
  • upper g−2: −gf ≤ 0, gε < (g+1)(g−2) ≤ (g−2)(t+g) since (g−2)(1−t) ≤ 0.

STEP B_k ⟹ A_{k+1}  (index 2k+1 Odd, so gu(2k+2) = ⌊b·(gu(2k+1) + 1/(g−1))⌋):
  This step is EXACT (no inequality).  From (g−1)·gu(2k+1) = g^k−1, gu(2k+1) = (g^k−1)/(g−1), so
  b·(gu(2k+1) + 1/(g−1)) = (g−1)(t+g)·((g^k−1)/(g−1) + 1/(g−1)) = (t+g)·g^k = g^{k+1} + t·g^k.
  Hence ⌊b·(…)⌋ = g^{k+1} + ⌊t·g^k⌋ = g^{k+1} + ⌊t·g^{k+1}/g⌋  (`Int.floor_add_int`; t·g^{k+1}/g = t·g^k).

Index bookkeeping: `Even (2*k)`, `¬Even (2*k+1)`, `2*(k+1) = (2*k+1)+1`, `2*k+1 = (2*k)+1`.
Casts ℕ→ℤ→ℝ; t+g > 0; g−1 ≥ 1.
-/

theorem thm13_closed (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a b : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hb : b = ((g : ℝ) - 1) * (t + g))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g)
    (gu : ℕ → ℤ) (hu0 : gu 0 = 1)
    (hrec : ∀ n, gu (n + 1)
      = if Even n then ⌊a * ((gu n : ℝ) + ε)⌋ else ⌊b * ((gu n : ℝ) + 1 / ((g : ℝ) - 1))⌋) :
    (∀ k, gu (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋) ∧
      (∀ k, ((g : ℤ) - 1) * gu (2 * k + 1) = (g : ℤ) ^ k - 1) := by
  sorry
