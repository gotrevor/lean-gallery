/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos403.Statement

/-!
# Erdős #403 — comparator SOLUTION

Discharges every `sorry` in `Challenge.lean` by delegating to the real development. The definitions
are repeated **verbatim** from the challenge (comparator requires that every declaration appearing
in a statement be identical in both environments), and each theorem is closed by the corresponding
gallery result.

This file is *not* part of the audit surface — `Challenge.lean` is. Comparator's job is to prove
that whatever happens in here really did establish the challenge's statements.
-/

open scoped Nat

namespace Erdos403

/-- Verbatim from `Challenge.lean` — comparator checks the two are the same declaration. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite :=
  LeanGallery.NumberTheory.Erdos403.erdos_403_finite

theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 :=
  LeanGallery.NumberTheory.Erdos403.erdos_403_sharp h

theorem erdos_403_witness : factSum {2, 3, 5} = 2 ^ 7 :=
  LeanGallery.NumberTheory.Erdos403.witness

end Erdos403
