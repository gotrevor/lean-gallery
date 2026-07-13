/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #1050 — comparator CHALLENGE (the trusted audit surface)

This file is the **thing a human audits.** It imports *only* Mathlib, defines every notion used
in the headline statements, and states them with `sorry`. `Solution.lean` (which imports the real
development) must prove *these exact statements*, and `comparator` machine-checks that it did:
every declaration appearing in a statement here must be **identical** in the solution environment,
the proofs must be accepted by the Lean kernel, and they may use no axioms beyond
`propext`, `Quot.sound`, `Classical.choice`.

So the trust chain is: *read this file, and only this file* — then comparator certifies the rest.

⚠️ Deliberately **no definition holes** (`definition_names`). Comparator only checks a hole's name,
type and universe, which is a gameable surface (its own README: a hole "can be gamed without
additional oversight"). The single definition below (`S`) carries its real body, so it is covered by
the strict statement-identity check instead.

## The problem

Erdős #1050 asks: is `∑_{n ≥ 1} 1/(2ⁿ − 3)` irrational? The answer is yes (Borwein 1991/1992).

`Lean`'s `∑' n : ℕ` ranges over `n ≥ 0`, so the source's `n ≥ 1` sum is encoded by the standard
reindex `n ↦ n + 1`: the tsum's `n = 0` summand is the source's first term `1/(2¹ − 3) = −1`. That
shift is the only thing to reconcile against erdosproblems.com/1050, and it is transparent.

## What is stated here

The headline set is exactly the one pinned by `scripts/AxiomCheck.lean` (the repo's axiom audit):

* `erdos_1050` — the problem itself, in pure Mathlib terms.
* `erdos_1050_irrational` — the same fact for the positive-denominator tail `S` (defined below).
* `borwein_thm1_abs` / `erdos_1050_borwein_general` — the general engine theorem: `∑ 1/(qⁿ + c)` is
  irrational for every integer `q` with `2 ≤ |q|` and every nonzero rational `c` with non-vanishing
  translates. (Two names for the same statement: the engine's and the re-export's. #1050 is
  `q = 2, c = −3`.)
* `erdos_1050.variants.*` — the *solved* below-the-box variants recorded on erdosproblems.com:
  Erdős [Er48] (`∑ 1/(2ⁿ − 1)`, its Lambert `∑ τ(n)/2ⁿ` form, and that form's irrationality) and
  Borwein [Bo91] as stated in `formal-conjectures`.
* `erdos_1050.variants.transcendental.implies_erdos_1050` — a *proved* implication: Erdős's open
  transcendence conjecture, taken as a **hypothesis**, gives the headline.

## What is deliberately NOT stated here

Erdős's [Er88c] transcendence conjecture (`∑_{n ≥ 1} 1/(2ⁿ + t)` is transcendental for every integer
`t ≠ 0`) is **open**. In the development it lives as `erdos_1050.variants.transcendental`, a
deliberately-`sorry`ed mirror of the `formal-conjectures` statement, pinned by `#guard_msgs` and
excluded from `scripts/AxiomCheck.lean`. It is excluded here too: a challenge may contain only
statements the solution actually **proves**. What *is* included is the proved implication above,
which takes that conjecture as a hypothesis and therefore asserts nothing about its truth.
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

namespace Erdos1050

/-- The positive-denominator tail `∑_{n ≥ 0} 1/(2^(n+2) − 3)` that the proof engine works with.
Every denominator `2^(n+2) − 3 ≥ 1` is positive, so all terms are well-defined positive reals. It
differs from the literal series `∑_{n ≥ 1} 1/(2ⁿ − 3)` by the single rational low term
`1/(2¹ − 3) = −1`, and irrationality is invariant under adding a rational — so
`erdos_1050_irrational` below and `erdos_1050` are equivalent. -/
noncomputable def S : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)

/-- **Erdős #1050** — the literal series `∑_{n ≥ 1} 1/(2ⁿ − 3)`, exactly as posed on
erdosproblems.com, is irrational. (Lean's `∑' n : ℕ` starts at `n = 0`, hence the `n ↦ n + 1`
reindex: the `n = 0` summand is the source's first term `1/(2¹ − 3)`.) -/
theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := sorry

/-- **Erdős #1050, tail form** — the positive-denominator tail `S` is irrational. -/
theorem erdos_1050_irrational : Irrational S := sorry

/-- **Borwein's Theorem 1** (the engine): for every integer `q` with `2 ≤ |q|` and every nonzero
rational `c` whose translates never vanish (`qⁿ⁺¹ + c ≠ 0` for all `n`), the series
`∑_{n ≥ 1} 1/(qⁿ + c)` is irrational. Erdős #1050 is the `q = 2, c = −3` case. -/
theorem borwein_thm1_abs (q : ℤ) (hq : 2 ≤ |q|) (c : ℚ) (hc0 : c ≠ 0)
    (hcn : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := sorry

/-- **Borwein [Bo91], the general theorem** (the gallery's re-export of `borwein_thm1_abs`, with the
problem's naming). Erdős #1050 is `q = 2, r = −3`; Erdős [Er48] is `q = 2, r = −1`. -/
theorem erdos_1050_borwein_general (q : ℤ) (hq : 2 ≤ |q|) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (r : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) := sorry

/-- **Erdős [Er48]** (solved below-the-box variant) — `∑_{n ≥ 1} 1/(2ⁿ − 1)` is irrational; the
`q = 2, r = −1` case of Borwein's theorem. Same `n ↦ n + 1` reindex as `erdos_1050`. -/
theorem erdos_1050.variants.two_pow_sub_one :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) := sorry

/-- **[Er48], the Lambert-series identity** — `∑_{n ≥ 1} 1/(2ⁿ − 1) = ∑_{n ≥ 1} τ(n)/2ⁿ`, with
`τ(n) = n.divisors.card` the divisor-counting function. -/
theorem erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) =
      ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1) := sorry

/-- **[Er48], the `τ`-series form** — the Lambert series `∑_{n ≥ 1} τ(n)/2ⁿ` is itself irrational:
the exact shape in which [Er48] is quoted on erdosproblems.com. -/
theorem erdos_1050.variants.two_pow_sub_one.divisor_count_series_irrational :
    Irrational (∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1)) := sorry

/-- **Borwein [Bo91], as stated in `formal-conjectures`** (`2 ≤ q`, non-vanishing phrased in `ℚ`) —
a specialization of the stronger `erdos_1050_borwein_general` above. -/
theorem erdos_1050.variants.borwein (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) := sorry

/-- **Consistency with the open conjecture** — Erdős's [Er88c] transcendence conjecture, taken as a
*hypothesis* `h`, implies the proved headline `erdos_1050` (specialize to `t = −3`; transcendence
over `ℚ` is strictly stronger than irrationality). This asserts nothing about the truth of `h`: the
conjecture itself is open and is **not** among the challenge's statements. -/
theorem erdos_1050.variants.transcendental.implies_erdos_1050
    (h : ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
      Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + (t : ℝ)))) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := sorry

end Erdos1050
