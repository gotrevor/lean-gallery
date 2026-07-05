/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.GeneralAssembly

/-!
# Erdős Problem #1050 — related solved variants

Below the boxed question, erdosproblems.com/1050 records two *solved* related irrationality results.
Both fall out of the general Borwein machinery this repository proves (`GeneralAssembly.lean`), so we
expose them here under problem-facing names as axiom-clean corollaries — verbatim delegations, adding
nothing to the trusted base. This file is the `formal_proof` target the `formal-conjectures` variants
`erdos_1050.variants.two_pow_sub_one` and `erdos_1050.variants.borwein` link to.

(A third related item — Erdős's conjecture [Er88c] that `∑ 1/(2ⁿ + t)` is *transcendental* for
`t ≠ 0` — is strictly stronger than irrationality and remains **open**; it lives only as a statement
in `formal-conjectures`, not here, since this repository holds finished proofs.)

## References
* [Er48] P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. (N.S.) 12
  (1948) 63–66.
* [Bo91] P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory 37 (1991) 253–259.
-/

namespace LeanGallery.NumberTheory.Erdos1050

/-- **Erdős [Er48].** The Erdős–Borwein-type series `∑_{n ≥ 1} 1/(2ⁿ − 1)` is irrational — the
`q = 2, r = −1` case of Borwein's theorem below. (Erdős's identity `∑ 1/(2ⁿ−1) = ∑ τ(n)/2ⁿ`, with `τ`
the divisor function, is its Lambert-series form.) Same `n ↦ n + 1` reindex as `erdos_1050`. -/
theorem erdos_1050_lambert : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) :=
  irrational_sum_two_pow_sub_one_abs

/-- **Borwein [Bo91], the general theorem.** For every integer `q` with `2 ≤ |q|` and every nonzero
rational `r` whose translates never vanish (`qⁿ⁺¹ + r ≠ 0` for all `n`), the series `∑_{n ≥ 1} 1/(qⁿ + r)`
is irrational. Problem #1050 is the `q = 2, r = −3` case; Erdős [Er48] is `q = 2, r = −1`. -/
theorem erdos_1050_borwein_general (q : ℤ) (hq : 2 ≤ |q|) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (r : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) :=
  borwein_thm1_abs q hq r hr hne

end LeanGallery.NumberTheory.Erdos1050
