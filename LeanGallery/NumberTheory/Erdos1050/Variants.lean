/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.GeneralAssembly
import LeanGallery.NumberTheory.Erdos1050.Lambert
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Erdős Problem #1050 — the below-the-box variants

Below the boxed question, erdosproblems.com/1050 records two *solved* related irrationality
results and one *open* transcendence conjecture. The theorem names here match the
`formal-conjectures` declarations one-for-one (`erdos_1050.variants.*` — FC's naming convention
for below-the-box variants), so statements can be diffed across the two repos by name.

* `erdos_1050.variants.two_pow_sub_one` **[Er48]** — `∑_{n ≥ 1} 1/(2ⁿ − 1)` is irrational.
  Proved: the `q = 2, r = −1` case of the Borwein machinery (`GeneralAssembly.lean`). Erdős's
  Lambert-series identity `∑ 1/(2ⁿ − 1) = ∑ τ(n)/2ⁿ` is proved too
  (`…two_pow_sub_one.eq_divisor_count_series`, engine in `Lambert.lean`), together with the
  irrationality of the `τ` form — the full [Er48] sentence as quoted on erdosproblems.com.
* `erdos_1050.variants.borwein` **[Bo91]** — Borwein's general theorem, stated *verbatim* as in
  `formal-conjectures` (`2 ≤ q`, non-vanishing phrased in `ℚ`). Proved: a specialization of this
  repository's stronger `erdos_1050_borwein_general` (`2 ≤ |q|`, non-vanishing phrased in `ℝ`).
* `erdos_1050.variants.transcendental` **[Er88c]** — Erdős's conjecture that `∑ 1/(2ⁿ + t)` is
  *transcendental* for every integer `t ≠ 0`. **Open**: stated with `sorry` as a mirror of the FC
  statement (FC wraps the same body in `answer(sorry) ↔`). It is deliberately NOT in
  `scripts/AxiomCheck.lean` — the audit file certifies finished headlines only, and every headline
  there is pinned to the clean triple, so this `sorry` can never silently become load-bearing.
  Three *proved* sanity anchors evidence that the statement is a faithful rendering of the intent:
  * `…transcendental.value_at_t_zero` — at the excluded `t = 0` the series is exactly `1`,
    which is algebraic, so the `t ≠ 0` exclusion is forced (`…t_zero_not_transcendental`);
  * `…transcendental.junk_term_at_excluded_t` — at an excluded `t = −2ⁿ` a denominator vanishes
    and Lean's junk value `1/0 = 0` silently deletes that term, so the `t ≠ −2ⁿ` guard is forced;
  * `…transcendental.implies_erdos_1050` — specialized to `t = −3`, the conjecture implies the
    proved headline `erdos_1050` (transcendence over `ℚ` is strictly stronger than irrationality).

## References
* [Er48] P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. (N.S.) 12
  (1948) 63–66.
* [Bo91] P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory 37 (1991) 253–259.
* [Er88c] P. Erdős, *On the irrationality of certain series: problems and results*, in New advances
  in transcendence theory (Durham, 1986), 102–109, Cambridge Univ. Press, 1988.
-/

namespace LeanGallery.NumberTheory.Erdos1050

/-- **Erdős [Er48].** The Erdős–Borwein-type series `∑_{n ≥ 1} 1/(2ⁿ − 1)` is irrational — the
`q = 2, r = −1` case of Borwein's theorem below. (Erdős's identity `∑ 1/(2ⁿ−1) = ∑ τ(n)/2ⁿ`, with `τ`
the divisor function, is its Lambert-series form.) Same `n ↦ n + 1` reindex as `erdos_1050`.
Statement and name match `formal-conjectures`' `erdos_1050.variants.two_pow_sub_one` exactly. -/
theorem erdos_1050.variants.two_pow_sub_one :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) :=
  irrational_sum_two_pow_sub_one_abs

/-- **[Er48], the Lambert-series identity.** The series `∑_{n ≥ 1} 1/(2ⁿ − 1)` *equals* the
Lambert series `∑_{n ≥ 1} τ(n)/2ⁿ`, with `τ(n) = n.divisors.card` the divisor-counting function
(engine proof in `Lambert.lean`). Together with `erdos_1050.variants.two_pow_sub_one` this
formalizes the full [Er48] sentence quoted on erdosproblems.com/1050 — the irrationality *and*
the `τ`-series form it is stated for. -/
theorem erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) =
      ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1) :=
  two_pow_sub_one_eq_divisor_count_series

/-- Corollary: the Lambert series `∑_{n ≥ 1} τ(n)/2ⁿ` itself is irrational — the exact shape
`∑ τ(n)/2ⁿ` in which [Er48] is quoted. -/
theorem erdos_1050.variants.two_pow_sub_one.divisor_count_series_irrational :
    Irrational (∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  rw [← erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series]
  exact erdos_1050.variants.two_pow_sub_one

/-- **Borwein [Bo91], the general theorem.** For every integer `q` with `2 ≤ |q|` and every nonzero
rational `r` whose translates never vanish (`qⁿ⁺¹ + r ≠ 0` for all `n`), the series `∑_{n ≥ 1} 1/(qⁿ + r)`
is irrational. Problem #1050 is the `q = 2, r = −3` case; Erdős [Er48] is `q = 2, r = −1`. -/
theorem erdos_1050_borwein_general (q : ℤ) (hq : 2 ≤ |q|) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (r : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) :=
  borwein_thm1_abs q hq r hr hne

/-- **Borwein [Bo91], as stated in `formal-conjectures`.** For every integer `q ≥ 2` and nonzero
rational `r` with `r ≠ −qⁿ` for all `n ≥ 1`, the series `∑_{n ≥ 1} 1/(qⁿ + r)` is irrational.
Statement and name match `formal-conjectures`' `erdos_1050.variants.borwein` exactly; it is a
specialization of the stronger `erdos_1050_borwein_general` above (`2 ≤ |q|`). -/
theorem erdos_1050.variants.borwein (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) :=
  erdos_1050_borwein_general q (hq.trans (le_abs_self q)) r hr fun n h0 =>
    hne (n + 1) n.succ_pos (by
      have hr' : (r : ℝ) = -(q : ℝ) ^ (n + 1) := by linarith
      exact_mod_cast hr')

/-- error: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
/-- **Erdős [Er88c] — open.** Erdős conjectured that `∑_{n ≥ 1} 1/(2ⁿ + t)` is *transcendental*
for every integer `t ≠ 0` (with `t ≠ −2ⁿ` so no denominator vanishes) — strictly stronger than
the irrationality Borwein proved. The `sorry` IS the open conjecture; the anchors below are
proved and certify the statement is the intended one. The body matches `formal-conjectures`'
`erdos_1050.variants.transcendental` (there wrapped in `answer(sorry) ↔`).

The `#guard_msgs` pin consumes the expected `sorry` diagnostic (elevated to an error by the
repo's warnings-as-errors), so the build stays green — and if the conjecture is ever proved,
the now-missing diagnostic trips the pin loudly. -/
theorem erdos_1050.variants.transcendental :
    ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
      Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + (t : ℝ))) := by
  sorry

/-- Anchor 1 (why `t = 0` is excluded): at `t = 0` the series is the geometric series
`∑_{n ≥ 1} 2⁻ⁿ`, exactly `1`. -/
theorem erdos_1050.variants.transcendental.value_at_t_zero :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + ((0 : ℤ) : ℝ))) = 1 := by
  have h : (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + ((0 : ℤ) : ℝ)))
      = ∑' n : ℕ, (1 : ℝ) / 2 / 2 ^ n :=
    tsum_congr fun n => by push_cast; rw [pow_succ, add_zero, div_div]; ring
  rw [h]
  exact tsum_geometric_two' 1

/-- Anchor 1′: … and `1` is algebraic, so the `t = 0` instance is *not* transcendental — the
`t ≠ 0` exclusion in the statement is forced, exactly as erdosproblems.com presumes. -/
theorem erdos_1050.variants.transcendental.t_zero_not_transcendental :
    ¬ Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + ((0 : ℤ) : ℝ))) := by
  rw [erdos_1050.variants.transcendental.value_at_t_zero]
  exact fun h => h isAlgebraic_one

/-- Anchor 2 (why `t = −2ⁿ` is excluded): at `t = −4 = −2²` the `n = 1` summand's denominator
vanishes, and Lean's junk value `1/0 = 0` silently deletes the term — the formal `tsum` would no
longer denote the informal series. The `t ≠ −2ⁿ` guard in the statement is forced. -/
theorem erdos_1050.variants.transcendental.junk_term_at_excluded_t :
    (1 : ℝ) / ((2 : ℝ) ^ (1 + 1) + ((-4 : ℤ) : ℝ)) = 0 := by
  norm_num

/-- Anchor 3 (consistency with the proved layer): specialized to `t = −3`, the conjecture implies
the proved headline `erdos_1050` — transcendence over `ℚ` is strictly stronger than irrationality
(`Transcendental.irrational`). The open statement and the theorem it strengthens are formally
linked. -/
theorem erdos_1050.variants.transcendental.implies_erdos_1050
    (h : ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
      Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + (t : ℝ)))) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
  have hguard : ∀ n : ℕ, 1 ≤ n → (-3 : ℤ) ≠ -(2 : ℤ) ^ n := by
    intro n hn hEq
    have h3 : (2 : ℤ) ^ n = 3 := by linarith
    have hdvd : (2 : ℤ) ∣ (2 : ℤ) ^ n := dvd_pow_self 2 (by omega)
    rw [h3] at hdvd
    norm_num at hdvd
  have ht := (h (-3) (by norm_num) hguard).irrational
  have hc : ((-3 : ℤ) : ℝ) = -3 := by norm_num
  rw [hc] at ht
  simpa [sub_eq_add_neg] using ht

end LeanGallery.NumberTheory.Erdos1050
