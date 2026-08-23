import Mathlib

/-
GOAL: A digit-recurrence integer orbit is a base-2 expansion. If orbit(n+1) = v(orbit n) and every
"digit" v(orbit n) - 2*orbit n ∈ {0,1}, then 2^n*orbit 0 ≤ orbit n ≤ 2^n*orbit 0 + (2^n - 1)
(i.e. orbit n = ⌊W·2^n⌋ for W = orbit 0 + 0.d0d1…). This is the rigorous "the block orbit doubles
(base 2)" fact underlying the cubic digit-map analysis.

RECIPE: induction on n. Base: simp. Step: let d := v(orbit k) - 2*orbit k; rewrite orbit(k+1)=v(orbit k)
= 2*orbit k + d; provide the relations 2^(k+1) = 2*2^k and 2^(k+1)*orbit 0 = 2*(2^k*orbit 0) as
hypotheses (so `omega` can treat 2^k*orbit 0 as an atom), rcases the bit hypothesis, then `omega` with
the inductive bounds closes both inequalities.
-/
theorem block_orbit_base_two (orbit : ℕ → ℤ) (v : ℤ → ℤ)
    (hstep : ∀ n, orbit (n + 1) = v (orbit n))
    (hbit : ∀ n, v (orbit n) - 2 * orbit n = 0 ∨ v (orbit n) - 2 * orbit n = 1) :
    ∀ n, 2 ^ n * orbit 0 ≤ orbit n ∧ orbit n ≤ 2 ^ n * orbit 0 + (2 ^ n - 1) := by
  intro n;
  induction' n with n ih;
  · norm_num;
  · cases hbit n <;> simp_all +decide [ pow_succ', mul_assoc ] <;> constructor <;> linarith