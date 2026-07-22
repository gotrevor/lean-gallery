import Mathlib

open Real

/-
GOAL: prove Stoll [St05] Theorem 1.3's closed forms by joint induction on the recurrence.

Setup (St05 Thm 1.3, base g≥2, t = base-g mantissa of w so 1≤t<g):
  a = g/((g-1)(t+g)),  b = (g-1)(t+g)   [note a·b = g],  even-offset 1/(g-1), odd-offset ε,
  with -1/g ≤ ε < (g+1)(g-2)/g.
Recurrence (0-indexed `gu n = u_{n+1}`, u₁=1): step from index n uses (a,ε) when n is EVEN
(original odd index) and (b, 1/(g-1)) when n is ODD.

Closed forms to prove (k ≥ 0):
  gu(2k)   = g^k + ⌊t·g^k / g⌋        (= u_{2k+1}; at k=0 this is 1+⌊t/g⌋ = 1 since 1≤t<g)
  (g-1)·gu(2k+1) = g^k − 1            (= u_{2k+2} = (g^k−1)/(g-1), the geometric sum 1+g+…+g^{k-1})

PROOF STRATEGY (elementary, the heart of St05). Joint induction on k.
* Each step is a single `⌊real⌋ = integer` claim, reduced via `Int.floor_eq_iff` to two
  inequalities `W ≤ (expr) < W+1`.
* The fractional-part / digit-tail bound `0 ≤ t·g^k − g·⌊t·g^{k-1}⌋ < g` (from
  `0 ≤ ⌊g·x⌋ − g⌊x⌋ < g`) is what closes each step; combine with the parameter bounds on a,b,ε,t.
* Use a·b = g and 1 ≤ t < g freely.  No field theory, no badly-approximable input.
Take care with casts ℕ→ℤ→ℝ and with `g - 1` (use `2 ≤ g` so `g - 1 ≥ 1`, nonzero).
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
