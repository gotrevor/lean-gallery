/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #1213 — comparator CHALLENGE (the trusted audit surface)

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

Erdős #1213 asks after Hegyvári's `f(a, K)`: take strictly increasing positive integers
`a₁ < a₂ < ⋯ < a_s` whose consecutive gaps are at most `K` (`a_{i+1} ≤ a_i + K`), and require that
**all** consecutive-block sums `a_u + a_{u+1} + ⋯ + a_v` be pairwise distinct. Can the last term
`a_s` be arbitrarily large — i.e. is `f(a, K) = sup a_s` finite?

It is finite, with the explicit bound of Hegyvári's Theorem 3:
```
a_s  <  L  :=  (a₁ + K/2)·e^(K+1) + K·e^(2K+2).
```
Source: N. Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar. **48** (1986) 193–200,
Theorem 3 (DOI 10.1007/BF01949064). Problem page: <https://www.erdosproblems.com/1213>.

## What is stated below

* `erdos_1213` — the last-term form: the bound `a_s < L` above.
* `erdos_1213_f_finite` — the supremum form (closest to how the problem is posed):
  `f(init, K) ≤ L`, where `f = hegyvariF` is the sup of achievable last terms.
* Three **non-vacuity / faithfulness anchors**, which is what keeps the two bounds above from being
  cheap. A bound `a_s < L` is worthless if `AllCSumsDistinct` is unsatisfiable, and `f ≤ L` is
  worthless if the supremum is taken over the empty set (`sSup ∅ = 0` in `ℕ`). So:
  - `erdos_1213_anchor_valid` — `[1, 2]` really *is* all-block-sums-distinct (the hypothesis of
    `erdos_1213` is satisfiable);
  - `erdos_1213_anchor_collision` — `[1, 2, 3]` really is *not* (the predicate has teeth: it is not
    vacuously true, e.g. `a₁ + a₂ = 3 = a₃`);
  - `erdos_1213_f_lower` — `f(1, 1) ≥ 2`, so the supremum in `erdos_1213_f_finite` is over a
    nonempty set and is not the degenerate `sSup ∅ = 0`.
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

namespace Erdos1213
open Finset

/-- The "consecutive sum" (c-sum) of `a` over the index block `u..v` (1-based, `u ≤ v`). -/
def csum (a : ℕ → ℕ) (u v : ℕ) : ℕ := ∑ i ∈ Finset.Icc u v, a i

/-- All c-sums of `a` on blocks inside `[1, s]` are pairwise distinct (as a function of the block). -/
def AllCSumsDistinct (a : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂, 1 ≤ u₁ → u₁ ≤ v₁ → v₁ ≤ s → 1 ≤ u₂ → u₂ ≤ v₂ → v₂ ≤ s →
    csum a u₁ v₁ = csum a u₂ v₂ → u₁ = u₂ ∧ v₁ = v₂

/-- The set of achievable last terms for starting value `a₁ = init`, gap bound `K`. -/
def validLastTerms (init K : ℕ) : Set ℕ :=
  {n | ∃ (s : ℕ) (seq : ℕ → ℕ), seq 1 = init ∧ 1 ≤ s ∧ seq s = n ∧
    (∀ i, 1 ≤ i → i < s → seq i < seq (i + 1)) ∧
    (∀ i, 1 ≤ i → i < s → seq (i + 1) ≤ seq i + K) ∧
    AllCSumsDistinct seq s}

/-- `f(a,K)` from the paper: the supremum of last terms of strictly-increasing sequences with first
term `a₁ = init`, gaps `≤ K`, and all consecutive-block sums distinct. -/
noncomputable def hegyvariF (init K : ℕ) : ℕ := sSup (validLastTerms init K)

/-- A 1-indexed sequence from an explicit list: `seqOf l i = l[i-1]` (with `0` past the end). -/
def seqOf (l : List ℕ) : ℕ → ℕ := fun i => l.getD (i - 1) 0

/-- **Erdős #1213 — Hegyvári's Theorem 3 (last-term form).**

Let `a 1 < a 2 < … < a s` be strictly increasing positive integers whose consecutive gaps are at most
`K` (`a (i+1) ≤ a i + K`). If **all** consecutive-block sums `csum a u v = a u + … + a v` are distinct
(`AllCSumsDistinct`), then the last term is bounded:
```
a s  <  (a 1 + K/2)·e^(K+1) + K·e^(2K+2).
```
In particular no such "all block-sums distinct" sequence can be arbitrarily long. -/
theorem erdos_1213 (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap  : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hdist : AllCSumsDistinct a s) :
    (a s : ℝ) <
      ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) := sorry

/-- **Erdős #1213 — finiteness of `f(a,K)`.**

`hegyvariF init K` is the paper's `f(a,K)`: the supremum (over all valid sequences with first term
`init` and gaps `≤ K` whose block-sums are all distinct) of the last term. This theorem says that
supremum is finite, bounded by the same constant `L`:
```
f(init, K)  ≤  (init + K/2)·e^(K+1) + K·e^(2K+2).
```
This is the form closest to how the problem is posed ("is `f(a,K)` finite?"). -/
theorem erdos_1213_f_finite (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init) :
    (hegyvariF init K : ℝ) ≤
      ((init : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) := sorry

/-- **Non-vacuity anchor (positive).** The hypothesis of `erdos_1213` is satisfiable: the sequence
`[1, 2]` (i.e. `a 1 = 1`, `a 2 = 2`) has all four of its consecutive-block sums distinct
(`a₁ = 1`, `a₂ = 2`, `a₁ + a₂ = 3`). This is the witness behind the paper's `f(1,1) = 2`.

Without it, `erdos_1213` could be satisfied by a theory in which `AllCSumsDistinct` is never true. -/
theorem erdos_1213_anchor_valid : AllCSumsDistinct (seqOf [1, 2]) 2 := sorry

/-- **Faithfulness anchor (negative).** `AllCSumsDistinct` is a real constraint, not a predicate that
everything satisfies: extending the witness above by one step to `[1, 2, 3]` collides, because the
block `(1,2)` and the block `(3,3)` share the c-sum `1 + 2 = 3 = a₃`.

Together with `erdos_1213_anchor_valid` this pins the predicate from both sides: satisfiable, and not
trivially true. -/
theorem erdos_1213_anchor_collision : ¬ AllCSumsDistinct (seqOf [1, 2, 3]) 3 := sorry

/-- **Non-vacuity anchor for the supremum.** `f(1,1) ≥ 2`, certified by the witness `[1, 2]` above.

In `ℕ`, `sSup ∅ = 0`, so `erdos_1213_f_finite` would hold vacuously if `validLastTerms` were empty.
This anchor rules that out: the supremum is taken over a nonempty set of genuinely achievable last
terms. (The paper's exact value is `f(1,1) = 2`, so this is sharp; the upper bound `L` from
`erdos_1213_f_finite` is correct but loose — it only asserts `f(1,1) < 65.7`.) -/
theorem erdos_1213_f_lower : 2 ≤ hegyvariF 1 1 := sorry

end Erdos1213
