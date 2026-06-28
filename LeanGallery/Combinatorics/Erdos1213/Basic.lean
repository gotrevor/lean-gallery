/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #1213 — Hegyvári Thm 3: bounded-gap increasing sequences force equal consecutive-sums

A strictly increasing sequence with consecutive gaps ≤ K and ALL consecutive-block sums distinct
must be short: its last term is `< (a₁+K/2)·e^{K+1} + K·e^{2K+2}`.  Hence `f(a,K)` (the largest such
last term) is finite.  Source: N. Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar.
48 (1986) 193–200, Thm 3 (DOI 10.1007/BF01949064).
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

/-- The "consecutive sum" (c-sum) of `a` over the index block `u..v` (1-based, `u ≤ v`). -/
def csum (a : ℕ → ℕ) (u v : ℕ) : ℕ := ∑ i ∈ Finset.Icc u v, a i

/-- All c-sums of `a` on blocks inside `[1, s]` are pairwise distinct (as a function of the block). -/
def AllCSumsDistinct (a : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂, 1 ≤ u₁ → u₁ ≤ v₁ → v₁ ≤ s → 1 ≤ u₂ → u₂ ≤ v₂ → v₂ ≤ s →
    csum a u₁ v₁ = csum a u₂ v₂ → u₁ = u₂ ∧ v₁ = v₂

/-- The headline constant `L = (a₁ + K/2)·e^{K+1} + K·e^{2K+2}` of Hegyvári Thm 3. -/
noncomputable def hegyvariBound (a : ℕ → ℕ) (K : ℕ) : ℝ :=
  ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1) + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2)

/-! The headline theorem `hegyvari_thm3` is stated and proved in `Main.lean`, where the counting and
pigeonhole engine is available.  See `LeanGallery.Combinatorics.Erdos1213/Main.lean`. -/

end LeanGallery.Combinatorics.Erdos1213
