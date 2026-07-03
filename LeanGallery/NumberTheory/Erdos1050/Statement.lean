/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.Lemma3

/-!
# Erdős #1050 — the designated statement (AUDIT SURFACE)

**If you are checking that this repository proves the right thing, read THIS file.**

Everything else (`Criterion.lean`, `Approximants.lean`) is the proof engine. The theorems below are
the load-bearing statements; the headline `erdos_1050_literal` is stated on the **literal** series
`∑_{n ≥ 0} 1/(2ⁿ − 3)` exactly as posed, so there is nothing to reconcile against the source.

The claim: the real number `∑_{n ≥ 0} 1/(2ⁿ − 3)` is irrational.

* **Problem source.** P. Erdős & R. Graham, relayed at <https://www.erdosproblems.com/1050>
  ("Is `∑ 1/(2ⁿ − 3)` irrational?", answer yes).
* **Resolving theorem.** P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory
  **37** (1991) 253–259 (and the cleaner *On the irrationality of certain series*, Math. Proc. Camb.
  Phil. Soc. **112** (1992) 141–146), specialized to `q = 2, r = −3`.
* **Well-definedness.** `2ⁿ − 3` is never `0` (`2ⁿ = 3` has no solution), so every term `1/(2ⁿ − 3)`
  is a genuine real; the `n = 0, 1` terms are the (finite, rational) values `−1/2` and `−1`.

The proof engine works with the positive-denominator tail `S = ∑_{n ≥ 0} 1/(2^(n+2) − 3)` (see
`Basic.lean`); the headline reduces the literal series to it by
`(∑_{n ≥ 0} 1/(2ⁿ − 3)) = -3/2 + S` — the first two terms `1/(2⁰−3) + 1/(2¹−3) = -1/2 + -1 = -3/2`
are rational, and irrationality is invariant under adding a rational, so the two statements are
equivalent (`erdos_1050_literal ↔ erdos_1050`). This equivalence is *proved*, not asserted.

When proven, `#print axioms erdos_1050_literal` should end at `[propext, Classical.choice, Quot.sound]`
(kernel-pure; no `native_decide`, no custom axioms).
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- The literal Erdős–Graham series `∑_{n ≥ 0} 1/(2ⁿ − 3)`, exactly as posed on erdosproblems.com. -/
noncomputable def Sliteral : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ n - 3)

/-- The literal series is the positive-denominator tail `S` shifted by the two rational low terms:
`∑_{n ≥ 0} 1/(2ⁿ − 3) = -3/2 + S`, since `1/(2⁰−3) + 1/(2¹−3) = -1/2 + -1 = -3/2`. -/
theorem Sliteral_eq : Sliteral = -3 / 2 + S := by
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ n - 3)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ n - 3)) 2)
    exact h.mp (by simpa using S_summable)
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ n - 3)) 2 hsummable
  have hfin : (∑ i ∈ Finset.range 2, (1 : ℝ) / ((2 : ℝ) ^ i - 3)) = -3 / 2 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [hfin] at hsplit
  simp only [Sliteral, S]
  rw [← hsplit]

/-- **Erdős Problem #1050.** The series `∑_{n ≥ 0} 1/(2ⁿ − 3)` (literal form) is irrational. -/
theorem erdos_1050_literal : Irrational Sliteral := by
  rw [Sliteral_eq, show (-3 / 2 : ℝ) + S = S + ((-3 / 2 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff]
  exact erdos_1050

/-- **Erdős Problem #1050** (positive-denominator tail form, used by the proof engine). -/
theorem erdos_1050_irrational : Irrational S := erdos_1050

/-! ### Non-vacuity anchors

Executable evidence that the series computes as intended, so the irrationality claim is not an
artifact of a mis-stated series. (The claim is already self-certifying against the worst failure
mode: mathlib sets a non-summable `tsum` to `0`, and `Irrational 0` is false — so
`erdos_1050_literal` is provable only because the series genuinely converges to a non-rational real,
never vacuously.) -/

/-- Well-definedness: no term is a junk `1/0`, since the denominator `2ⁿ − 3` is never zero. -/
example (n : ℕ) : (2 : ℝ) ^ n - 3 ≠ 0 := by
  rcases lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num
  · have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    intro hc; nlinarith

/-- The first four terms compute to the expected values (the `n = 0, 1` terms are the rationals
`−1/2, −1`; the series first goes positive at `n = 2`). -/
example : (1 : ℝ) / (2 ^ 0 - 3) = -1 / 2 := by norm_num
example : (1 : ℝ) / (2 ^ 1 - 3) = -1 := by norm_num
example : (1 : ℝ) / (2 ^ 2 - 3) = 1 := by norm_num
example : (1 : ℝ) / (2 ^ 3 - 3) = 1 / 5 := by norm_num

/-- The rational shift connecting the literal series to the engine's tail `S`: the two low terms sum
to exactly `−3/2` (this is the content of `Sliteral_eq`). -/
example : (∑ i ∈ Finset.range 2, (1 : ℝ) / (2 ^ i - 3)) = -3 / 2 := by
  simp [Finset.sum_range_succ]; norm_num

end LeanGallery.NumberTheory.Erdos1050
