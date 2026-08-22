import Mathlib

open Real

/-
GOAL: assemble St05 Theorem 1.3's two closed forms by joint induction on k, GIVEN the two single
steps as axioms (`step_eo`, `step_oe` below).  This is pure induction wiring.

Recurrence (0-indexed, gu 0 = 1; step from index n uses (a,ε) when n EVEN, (b, 1/(g-1)) when n ODD):
  hrec : ∀ n, gu (n+1) = if Even n then ⌊a*(gu n + ε)⌋ else ⌊b*(gu n + 1/(g-1))⌋
Closed forms (k ≥ 0):
  (A_k)  gu (2k)     = g^k + ⌊t·g^k/g⌋
  (B_k)  (g-1)·gu (2k+1) = g^k − 1

INDUCTION SHAPE:
  A_0 is the base: gu 0 = 1 and g^0 + ⌊t·g^0/g⌋ = 1 + ⌊t/g⌋ = 1 since 1 ≤ t < g (so ⌊t/g⌋ = 0).
  A_k ⟹ B_k via `step_eo` (index 2k is Even ⟹ gu(2k+1) = ⌊a·(gu 2k + ε)⌋; rewrite gu 2k by A_k).
  B_k ⟹ A_{k+1} via `step_oe` (index 2k+1 is Odd ⟹ gu(2k+2) = ⌊b·(gu(2k+1) + 1/(g-1))⌋;
        step_oe consumes the B_k hypothesis (g-1)·v = g^k−1 with v = gu(2k+1)).
Prove `∀ k, A_k ∧ B_k` by `Nat.rec`: at k+1 use (A_k∧B_k) → B_k (step_eo) and B_k → A_{k+1}
(step_oe).  Then split into the two ∀-statements.  Watch `Even (2*k)`/`¬ Even (2*k+1)`,
`2*k+1 = 2*k+1`, `2*(k+1) = (2*k+1)+1`.
-/

axiom step_eo (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) (k : ℕ) :
    ((g : ℤ) - 1) * ⌊a * ((((g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ : ℤ) : ℝ) + ε)⌋
      = (g : ℤ) ^ k - 1

axiom step_oe (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t)
    (b : ℝ) (hb : b = ((g : ℝ) - 1) * (t + g)) (k : ℕ) (v : ℤ)
    (hv : ((g : ℤ) - 1) * v = (g : ℤ) ^ k - 1) :
    ⌊b * ((v : ℝ) + 1 / ((g : ℝ) - 1))⌋ = (g : ℤ) ^ (k + 1) + ⌊t * (g : ℝ) ^ (k + 1) / g⌋

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
