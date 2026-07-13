/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #482 — comparator CHALLENGE (the trusted audit surface)

This file is the **thing a human audits.** It imports *only* Mathlib, defines every notion used
in the headline statements, and states them with `sorry`. `Solution.lean` (which imports the real
development) must prove *these exact statements*, and `comparator` machine-checks that it did:
every declaration appearing in a statement here must be **identical** in the solution environment,
the proofs must be accepted by the Lean kernel, and they may use no axioms beyond
`propext`, `Quot.sound`, `Classical.choice`.

So the trust chain is: *read this file, and only this file* — then comparator certifies the rest.

⚠️ Deliberately **no definition holes** (`definition_names`). Comparator only checks a hole's name,
type and universe, which is a gameable surface (its own README: a hole "can be gamed without
additional oversight"). Every definition below carries its real body, so it is covered by the
strict statement-identity check instead.

## The problem

Erdős #482 (Erdős–Graham): *is there a "reasonable" recurrence whose terms give the binary digits
of an algebraic number?* Graham–Pollak (Math. Mag. 43 (1970) 143–145) gave the seed example: put

    u 0 = 1,   u (n+1) = ⌊√2 · (u n + ½)⌋

then `u(2n+1) − 2·u(2n−1)` **is** the `n`-th binary digit of `√2`. Stoll (*A fancy way to obtain
the binary digits of 759250125√2*, arXiv:0902.4168) parametrizes the offset on the odd steps and,
in [St05], resolves the question in full generality: for **every** real `w > 0` and **every** base
`g ≥ 2` there is an explicit floor recurrence whose Graham–Pollak differences read off the base-`g`
digits of `w`.

## What is claimed here

* `graham_pollak` — the headline, in Stoll's floor-formula digit `binDigit`.
* `graham_pollak_digits` — **the anchor**: the same difference is literally mathlib's own
  `Real.digits` base-2 digit of `Int.fract √2`. This is what stops `binDigit` from being a
  self-serving definition: the project notion is pinned to the standard-library notion.
* `cor33_unconditional` — Stoll's showcase constant: the `ε = 1 − π²/e³` recurrence reads off the
  binary digits of `759250125·√2`, with **no hypotheses left** (the 62-step base case is
  discharged inside).
* `erdos482_resolution` — Erdős #482 resolved in full generality (any `w > 0`, any base `g ≥ 2`),
  stated against mathlib's `Real.digits`.
* `binDigit_sqrt2_first_six` — **non-vacuity / faithfulness witness**: the first six digits come
  out `0,1,1,0,1,0`, matching `√2 = 1.0110101…₂`. Concrete numbers, so none of the above can be
  satisfied by a vacuous or degenerate reading of `binDigit`.

All four definitions below (`u`, `binDigit`, `vv`, `gu`) are `noncomputable` for the boring reason
that `Real.sqrt`, `Int.floor` and `Nat.floor` on `ℝ` are — nothing hides there.
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

namespace Erdos482

/-! ## Definitions (the full closure — everything else is Mathlib) -/

/-- The Graham–Pollak sequence: `u 0 = 1`, `u (n+1) = ⌊√2 · (u n + ½)⌋`. -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-- The `n`-th binary digit of `t` (Graham–Pollak / Stoll floor formula):
`⌊t·2ⁿ⌋ − 2⌊t·2ⁿ⁻¹⌋ ∈ {0,1}`. Pinned to mathlib's `Real.digits` by `graham_pollak_digits`. -/
noncomputable def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

/-- Stoll's parametrized Graham–Pollak sequence, 0-indexed (`vv ε n = v_{n+1}`): the step from `n`
uses the offset `ε` when `n` is even, and `½` when `n` is odd. -/
noncomputable def vv (ε : ℝ) : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((vv ε n : ℝ) + (if Even n then ε else 1 / 2))⌋₊

/-- St05 Theorem 1.3's base-`g` recurrence, 0-indexed (`gu g a b ε n = u_{n+1}`, `u₁ = 1`): the step
from `n` uses `(a, ε)` when `n` is even and `(b, 1/(g−1))` when `n` is odd. -/
noncomputable def gu (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((gu g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((gu g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-! ## The headline statements -/

/-- **Erdős #482 / Graham–Pollak (the headline).** For `u 0 = 1`, `u (n+1) = ⌊√2·(u n + ½)⌋`, the
difference `u(2n+1) − 2·u(2n−1)` is the `n`-th binary digit of `√2`. -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := sorry

/-- **The anchor to mathlib's notion of a digit.** The same Graham–Pollak difference is literally
the `(n−1)`-th base-2 digit of `Int.fract √2` under mathlib's `Real.digits`. Without this, the
headline would only be a statement about the project's own `binDigit`. -/
theorem graham_pollak_digits (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ)
      = ((Real.digits (Int.fract (Real.sqrt 2)) 2 (n - 1) : ℕ) : ℤ) := sorry

/-- **Stoll, arXiv:0902.4168, Corollary 3.3 — the showcase constant, UNCONDITIONAL.** Run the
parametrized recurrence with `ε = 1 − π²/e³`: its Graham–Pollak difference at `k = m + 31` reads off
the `(m+1)`-th binary digit of `759250125·√2`. No hypotheses remain — the `ε`-sensitive 62-step base
case is discharged inside the development from mathlib's `π`/`e`/`√2` bounds. -/
theorem cor33_unconditional (m : ℕ) :
    (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) + 1) : ℤ)
        - 2 * (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) - 1) : ℤ)
      = binDigit (759250125 * Real.sqrt 2) (m + 1) := sorry

/-- **Erdős #482, resolved in full generality (Stoll [St05]).** For any real `w > 0` and any integer
base `g ≥ 2`, with mantissa `t = w/g^{⌊log_g w⌋}`, there exist coefficients `a, b, ε` with `a·b = g`
such that the recurrence `gu g a b ε` reads off the base-`g` digits of `w`:
`gu(2n) − g·gu(2n−2) = Real.digits (t·g^{n−1}/g) g 0` for every `n ≥ 1`. -/
theorem erdos482_resolution (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 1 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits
              (w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := sorry

/-- **Non-vacuity / faithfulness witness.** The first six Graham–Pollak digits are `0, 1, 1, 0, 1, 0`
— exactly the binary expansion `√2 = 1.0110101…₂`. Concrete numbers, so `binDigit` cannot be a
degenerate notion that makes the headlines cheap. -/
theorem binDigit_sqrt2_first_six :
    binDigit (Real.sqrt 2) 1 = 0 ∧ binDigit (Real.sqrt 2) 2 = 1 ∧
      binDigit (Real.sqrt 2) 3 = 1 ∧ binDigit (Real.sqrt 2) 4 = 0 ∧
      binDigit (Real.sqrt 2) 5 = 1 ∧ binDigit (Real.sqrt 2) 6 = 0 := sorry

end Erdos482
