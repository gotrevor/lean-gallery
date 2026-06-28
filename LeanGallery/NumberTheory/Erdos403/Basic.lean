/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős problem #403 — sums of distinct factorials that are powers of two

*Only finitely many powers of two are sums of distinct factorials; the largest is
`2⁷ = 2! + 3! + 5! = 128`.* — Burr–Erdős [ErGr80, p. 79], proved independently by P. Frankl
and Shen Lin (1976, both **unpublished** — Lin's was a Bell Labs internal memorandum).

This file is the **abstract and audit surface** for the formalization: it fixes the faithful
definition of a "sum of distinct factorials", records the extremal solution and machine-checked
sample values that pin the definition down, and points at the headline theorems. The proof lives
in `Engine.lean` and the headline statements in `Statement.lean`; neither is part of the trust
surface. Read this file against the problem statement.

## The construction

A *sum of distinct factorials* `a₁! + ⋯ + aₖ!` with `a₁ < ⋯ < aₖ` is modelled by the finite set
of indices `S : Finset ℕ` (distinctness of the `aᵢ` is then automatic), and
`factSum S = ∑_{a ∈ S} a!`. Note `0! = 1! = 1`, so e.g. `{0, 1}` and `{2}` both sum to `2`.

## Main definitions
* `factSum S = ∑_{a ∈ S} a!` — the sum of distinct factorials indexed by `S`.

## Main statements
The headlines live in `Statement.lean` (proved in `Engine.lean`):
```
theorem erdos_403_sharp  {S m} (h : factSum S = 2 ^ m) : m ≤ 7
theorem erdos_403_finite : {S | ∃ m, factSum S = 2 ^ m}.Finite
```
Every power of two that is a sum of distinct factorials has exponent `m ≤ 7`, and `witness` below
exhibits `m = 7`, so the bound is **sharp**: the largest such power is `2⁷ = 128`. The original
proofs are lost to the literature, so `Engine.lean` is a **reconstruction**: it works in the
factorial number system (a sum of distinct factorials is exactly a factorial-base numeral with all
digits `≤ 1`) and shows that for every `m ≥ 8` both `2^m` and `2^m − 1` carry a factorial digit
`≥ 2` — a finite, fixed-modulus (`12!`) check. Verified axiom-clean and kernel-pure (no
`native_decide`): `#print axioms erdos_403_finite` reports only
`[propext, Classical.choice, Quot.sound]`.

## Sample values (machine-checked below)
The `decide` examples at the end compute `factSum` straight from the definition, so a vacuous or
placeholder definition could not reproduce them. They are standalone `example`s that never sit on a
headline's axiom path.

## References
* P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number theory*,
  Monographies de L'Enseignement Mathématique **28** (1980), p. 79.
* Erdős problem #403, <https://www.erdosproblems.com/403>.
-/

namespace LeanGallery.NumberTheory.Erdos403

open scoped Nat

/-- The sum of distinct factorials indexed by `S`: `∑_{a ∈ S} a!`. This is the basic object of
Erdős #403: a "sum of distinct factorials" is exactly `factSum S` for some `S : Finset ℕ`. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

/-- **The extremal solution.** `factSum {2, 3, 5} = 2! + 3! + 5! = 2 + 6 + 120 = 128 = 2⁷` — the
largest power of two that is a sum of distinct factorials. Together with `erdos_403_sharp`
(`m ≤ 7`), this shows the bound is sharp. -/
theorem witness : factSum {2, 3, 5} = 2 ^ 7 := by
  rw [factSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  decide

/-! ### Ground-truth anchors (faithfulness gate)

Hand-computed values of `factSum`, discharged by `decide` straight from the definition above. They
are the anti-vacuity lock: a placeholder definition could not reproduce them. They live in the
library so they count toward the no-`sorry` gate; re-check `#print axioms erdos_403_finite`, not
these. -/

-- `0! = 1! = 1`, so the smallest value `2 = 2¹` is hit two ways: `{2}` and `{0, 1}`.
example : factSum {2} = 2 ^ 1 := by rw [factSum, Finset.sum_singleton]; decide
example : factSum {0, 1} = 2 ^ 1 := by
  rw [factSum, Finset.sum_insert (by decide), Finset.sum_singleton]; decide

-- `0! + 1! + 2! = 1 + 1 + 2 = 4 = 2²`.
example : factSum {0, 1, 2} = 2 ^ 2 := by
  rw [factSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]; decide

-- The extremal value as a bare numeral.
example : factSum {2, 3, 5} = 128 := by
  rw [factSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]; decide

end LeanGallery.NumberTheory.Erdos403
