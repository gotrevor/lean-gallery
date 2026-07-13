/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #403 — comparator CHALLENGE (the trusted audit surface)

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

## Why the `LeanGallery.NumberTheory.Erdos403` namespace

This file re-derives the gallery's constants **under their own fully-qualified names**, from Mathlib
alone — it imports nothing from the gallery, and everything below is written out in full and
auditable on its own terms. `Solution.lean` then imports the real development and declares
**nothing**. Comparator compares this file's `LeanGallery.NumberTheory.Erdos403.*` against the
*real* ones and fails unless they are the same declarations, so the certificate is about the
gallery's **genuine** `factSum` and `erdos_403_finite` — not an isomorphic copy under a private
namespace, bridged back by glue code that would itself need auditing.

## The problem
Erdős #403 asks: does `2^m = a₁! + ⋯ + a_k!` with `a₁ < ⋯ < a_k` have only finitely many solutions?
The answer is yes, and sharply so: the largest such power of two is `2⁷ = 2! + 3! + 5! = 128`.
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

namespace LeanGallery.NumberTheory.Erdos403

open scoped Nat

/-- The sum of distinct factorials indexed by `S`: `∑_{a ∈ S} a!`. This is the basic object of
Erdős #403: a "sum of distinct factorials" is exactly `factSum S` for some `S : Finset ℕ`. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

/-- **Erdős #403 (sharp form)** — every solution has `m ≤ 7`. -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := sorry

/-- **Erdős #403 (finiteness)** — exactly what the problem asks: only finitely many powers of two
are sums of distinct factorials. -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite := sorry

/-- **Non-vacuity witness** — `m = 7` is actually attained: `2! + 3! + 5! = 128 = 2⁷`.

Without this, `erdos_403_sharp` would be satisfied by a theory in which no `S` is ever a power of
two at all. Shipping the witness alongside the bound is what makes the pair *sharp* rather than
vacuously true. (This is the gallery's `witness`; the name is its own.) -/
theorem witness : factSum {2, 3, 5} = 2 ^ 7 := sorry

end LeanGallery.NumberTheory.Erdos403
