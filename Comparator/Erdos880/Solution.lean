/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Statement

/-!
# Erdős #880 (Burr–Erdős restricted addition) — comparator SOLUTION

Discharges every `sorry` in `Challenge.lean` by delegating to the real development. The definitions
are repeated **verbatim** from the challenge (comparator requires that every declaration appearing
in a statement be identical in both environments), and each theorem is closed by the corresponding
gallery result.

This file is *not* part of the audit surface — `Challenge.lean` is. Comparator's job is to prove
that whatever happens in here really did establish the challenge's statements.
-/

open scoped BigOperators
open Finset

namespace Erdos880

/-! ### Verbatim from `Challenge.lean` — comparator checks the two are the same declarations. -/

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

-- `xseq`/`block`/`constA` (the HHP07 witness construction) are deliberately NOT redeclared here:
-- the challenge states both `k ≥ 3` headlines existentially, so the construction never appears in a
-- statement. It is supplied below as the existential's *witness term*, straight from the gallery.

/-! ### The headlines, delegated to the gallery -/

theorem erdos_880 (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ UnboundedGaps (restrictedSums A h) :=
  LeanGallery.Combinatorics.Erdos880.erdos_880 h hh

theorem erdos_880_order_two (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    BoundedGapsBy (restrictedSums A 2) 2 :=
  LeanGallery.Combinatorics.Erdos880.erdos_880_order_two A hbasis

theorem erdos_880_delta (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ Delta (restrictedSums A h) = ⊤ :=
  ⟨LeanGallery.Combinatorics.Erdos880.constA h,
   LeanGallery.Combinatorics.Erdos880.constA_isBasis h hh,
   LeanGallery.Combinatorics.Erdos880.erdos_880_delta h hh⟩

theorem erdos_880_order_two_delta (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    Delta (restrictedSums A 2) ≤ 2 :=
  LeanGallery.Combinatorics.Erdos880.erdos_880_order_two_delta A hbasis

end Erdos880
