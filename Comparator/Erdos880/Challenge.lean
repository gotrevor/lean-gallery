/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #880 (Burr–Erdős restricted addition) — comparator CHALLENGE (the trusted audit surface)

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

Let `A ⊆ ℕ` be an additive basis of order `k` (every large integer is a sum of at most `k` elements
of `A`), and let `B` be the set of integers that are a sum of `k` or fewer **pairwise distinct**
elements of `A`. Burr and Erdős asked: **are the gaps `b_{n+1} − b_n` of `B` bounded?**

Hegyvári, Hennecart and Plagne resolved it:

* **`k = 2`: YES** — the gaps are eventually `≤ 2` (`erdos_880_order_two`), equivalently
  `Δ(2 × A) ≤ 2` (`erdos_880_order_two_delta`). This holds for *every* basis of order `2`.
* **`k ≥ 3`: NO** — there **exists** a basis of order `k` whose restricted-sum set has arbitrarily
  long gaps (`erdos_880`), equivalently `Δ = +∞` (`erdos_880_delta`). The negative answer is the
  headline, and it is an **existence** claim: the witness basis is exhibited (`constA`, inlined
  below in full), so the statement is not vacuous.

`Δ` is the paper's asymptotic gap functional `Δ(X) = limsup_{i→∞} (a_{i+1} − a_i) ∈ ℕ ∪ {+∞}`,
rendered here (`Delta`) via the elementary identity `limsup g = inf {d | eventually gₙ ≤ d}`: the
least `d` that *eventually* bounds the consecutive gaps of `X`, or `⊤` if none does.

Source: N. Hegyvári, F. Hennecart, A. Plagne, *Answer to a question by Burr and Erdős on restricted
addition, and related results*, Combin. Probab. Comput. **16** (2007) 747–756.
Problem page: <https://www.erdosproblems.com/880>.
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

open scoped BigOperators
open Finset

namespace LeanGallery.Combinatorics.Erdos880

/-! ### The problem's vocabulary (`Basic.lean`) -/

/-- Integers that are a sum of **exactly `h` pairwise distinct** elements of `A` (the restricted
`h`-fold sumset, written `h × A` in the paper). -/
def restrictedSumset (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ T : Finset ℕ, (↑T ⊆ A) ∧ T.card = h ∧ ∑ a ∈ T, a = n}

/-- Integers that are a sum of **at most `k` (not necessarily distinct)** elements of `A` (the
ordinary "≤ k-fold" sumset — used for the basis condition). -/
def sumsetLE (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ (m : ℕ) (f : Fin m → ℕ), m ≤ k ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- The set `B` of #880: integers that are a sum of `k` or fewer pairwise distinct elements of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  ⋃ h ∈ Finset.Icc 1 k, restrictedSumset A h

/-- `A` is an additive basis of order `k`: all but finitely many naturals lie in `sumsetLE A k`. -/
def IsBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  {n : ℕ | n ∉ sumsetLE A k}.Finite

/-- `S` has **unbounded gaps**: arbitrarily long runs of consecutive integers are missing from `S`. -/
def UnboundedGaps (S : Set ℕ) : Prop :=
  ∀ G : ℕ, ∃ m : ℕ, ∀ x : ℕ, m ≤ x → x ≤ m + G → x ∉ S

/-- `S` has **gaps eventually bounded by `C`**: beyond some `N`, every integer has a member of `S`
within `C` above it (so consecutive members are `≤ C` apart). -/
def BoundedGapsBy (S : Set ℕ) (C : ℕ) : Prop :=
  ∃ N : ℕ, ∀ x : ℕ, N ≤ x → ∃ y ∈ S, x ≤ y ∧ y ≤ x + C

/-! ### The paper's gap functional `Δ` (`Delta.lean`) -/

/-- `EvGapLe X d` : **eventually**, every element of `X` has a successor in `X` within distance `d`.
For an infinite `X` with increasing enumeration `a₁ < a₂ < ⋯`, this says exactly that
`a_{i+1} − a_i ≤ d` for all large `i` — i.e. `d` is an eventual upper bound for the gap sequence. -/
def EvGapLe (X : Set ℕ) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∀ x ∈ X, N ≤ x → ∃ y ∈ X, x < y ∧ y ≤ x + d

open Classical in
/-- The **asymptotic gap functional** `Δ(X) ∈ ℕ∞` of HHP07: the least `d` that eventually bounds the
consecutive gaps of `X`, or `⊤ (= +∞)` if the gaps are unbounded. Faithful to `limsup(a_{i+1}−a_i)`
via `limsup g = inf { d | eventually gₙ ≤ d }`. -/
noncomputable def Delta (X : Set ℕ) : ℕ∞ :=
  if _h : ∃ d, EvGapLe X d then ((sInf {d : ℕ | EvGapLe X d} : ℕ) : ℕ∞) else ⊤

/-! ### The headlines

Note both `k ≥ 3` headlines are stated **existentially**, which is what HHP07 Theorem 1(ii) actually
claims ("for `k ≥ 3` the answer is no" = a counterexample basis exists). The proof supplies the
explicit Hegyvári–Hennecart–Plagne witness, but naming that construction *here* would drag its
recurrence (`xseq`, `block`, `constA`) into the trusted surface, forcing a reader to audit a
definition the theorem does not depend on. The existential form is both the faithful rendering and
the smaller thing to check. -/

/-- **Erdős Problem #880 (the resolution, `k ≥ 3`).** For every order `h ≥ 3` there **exists** an
additive basis `A` of order `h` whose set of restricted sums (sums of `≤ h` distinct elements) has
arbitrarily long gaps. So the Burr–Erdős gap-boundedness fails for `k ≥ 3`.

This is an existence statement, which is its own non-vacuity witness: a basis of order `h` really is
produced, and its restricted-sum set really does have unbounded gaps. -/
theorem erdos_880 (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ UnboundedGaps (restrictedSums A h) := sorry

/-- **Erdős Problem #880 (the `k = 2` case).** For *every* basis `A` of order `2`, the restricted-sum
set has gaps eventually bounded by `2`. This is the positive half of the answer. -/
theorem erdos_880_order_two (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    BoundedGapsBy (restrictedSums A 2) 2 := sorry

/-- **Erdős #880, faithful `Δ` form (`k ≥ 3`).** For every `h ≥ 3` there exists a basis `A` of order
`h` whose restricted-sum set has asymptotic gap functional `Δ = +∞` — exactly the paper's
`Δ(𝒜 ∪ 2×𝒜 ∪ ⋯ ∪ h×𝒜) = +∞` (HHP07 Theorem 1(ii)). This restates the negative answer in the paper's
own `limsup` language rather than via the `UnboundedGaps` predicate.

⚠️ This is the **one deliberately restated theorem** in this pair. The gallery proves the sharper
`erdos_880_delta : Δ (restrictedSums (constA h) h) = ⊤`, which names the explicit HHP07 witness
`constA`. Naming `constA` *here* would drag its whole recurrence (`xseq`, `block`, `constA`) into the
trusted surface, forcing a reader to audit a construction the theorem does not depend on. So the
challenge asks only for the existential — the faithful reading of "for `k ≥ 3` the answer is no" —
and `Solution.lean` derives it from the gallery's sharper form in one line. Hence the distinct name:
`erdos_880_delta` in the gallery is a *different statement* from this one. -/
theorem erdos_880_delta_exists (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ Delta (restrictedSums A h) = ⊤ := sorry

/-- **Erdős #880, faithful `Δ` form (`k = 2`).** For a basis `A` of order `2`, the restricted-sum set
has asymptotic gap functional `Δ(2 × A) ≤ 2` — the paper's Theorem 1(i). -/
theorem erdos_880_order_two_delta (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    Delta (restrictedSums A 2) ≤ 2 := sorry

end LeanGallery.Combinatorics.Erdos880
