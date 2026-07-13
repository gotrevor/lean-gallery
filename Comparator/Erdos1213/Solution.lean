/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Statement
import LeanGallery.Combinatorics.Erdos1213.Anchors

/-!
# Erdős #1213 — comparator SOLUTION

Discharges every `sorry` in `Challenge.lean` by delegating to the real development. The definitions
are repeated **verbatim** from the challenge (comparator requires that every declaration appearing
in a statement be identical in both environments), and each theorem is closed by the corresponding
gallery result.

The two headline bounds come from `LeanGallery.Combinatorics.Erdos1213.Statement`; the anchors come
from `…/Anchors.lean` (`distinctB` + `distinctB_iff` give a kernel-checkable Bool mirror of
`AllCSumsDistinct`, and `hegyvariF_ge_1_1` is the certified lower bound `f(1,1) ≥ 2`). Every one of
them is axiom-clean: no `native_decide` (which would add `Lean.ofReduceBool`) is on any path used
here — the anchors are closed by kernel `decide` only.

This file is *not* part of the audit surface — `Challenge.lean` is. Comparator's job is to prove
that whatever happens in here really did establish the challenge's statements.
-/

namespace Erdos1213
open Finset

/-! ## Definitions — verbatim from `Challenge.lean`

Comparator checks that each of these is the *same declaration* in both environments. They are also
definitionally the gallery's own (`LeanGallery.Combinatorics.Erdos1213.{csum, AllCSumsDistinct,
validLastTerms, hegyvariF, seqOf}`), which is what lets the delegations below typecheck. -/

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

/-! ## The challenge statements, discharged -/

theorem erdos_1213 (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap  : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hdist : AllCSumsDistinct a s) :
    (a s : ℝ) <
      ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) :=
  LeanGallery.Combinatorics.Erdos1213.erdos_1213 a s K hK hs ha1 hmono hgap hdist

theorem erdos_1213_f_finite (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init) :
    (hegyvariF init K : ℝ) ≤
      ((init : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) :=
  LeanGallery.Combinatorics.Erdos1213.erdos_1213_f_finite init K hK ha

/-- Positive anchor. Kernel-`decide`d through the gallery's `Bool` mirror `distinctB`
(`distinctB_iff : distinctB a s = true ↔ AllCSumsDistinct a s`) — this is exactly the `by decide`
that already discharges the `hdist` argument of `hegyvariF_ge_1_1` in `Anchors.lean`. -/
theorem erdos_1213_anchor_valid : AllCSumsDistinct (seqOf [1, 2]) 2 := by
  show LeanGallery.Combinatorics.Erdos1213.AllCSumsDistinct
      (LeanGallery.Combinatorics.Erdos1213.seqOf [1, 2]) 2
  rw [← LeanGallery.Combinatorics.Erdos1213.distinctB_iff]
  decide

/-- Negative anchor. Proved by exhibiting the collision explicitly rather than by a decision
procedure: the blocks `(1,2)` and `(3,3)` of `[1, 2, 3]` both have c-sum `3`, yet `1 ≠ 3`. -/
theorem erdos_1213_anchor_collision : ¬ AllCSumsDistinct (seqOf [1, 2, 3]) 3 := by
  intro h
  have hc : csum (seqOf [1, 2, 3]) 1 2 = csum (seqOf [1, 2, 3]) 3 3 := by decide
  obtain ⟨h1, -⟩ :=
    h 1 2 3 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hc
  omega

/-- Supremum anchor: `f(1,1) ≥ 2`, from the gallery's certified lower bound (witness `[1, 2]`,
`le_csSup` against `bddAbove_validLastTerms`). -/
theorem erdos_1213_f_lower : 2 ≤ hegyvariF 1 1 :=
  LeanGallery.Combinatorics.Erdos1213.hegyvariF_ge_1_1

end Erdos1213
