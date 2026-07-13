/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Statement

/-!
# Erdős #880 — comparator SOLUTION

Discharges the `sorry`s in `Challenge.lean` by bringing the real development into scope. This file
declares **no definitions**: `Challenge.lean` re-derives `restrictedSumset`, `sumsetLE`,
`restrictedSums`, `IsBasisOfOrder`, `UnboundedGaps`, `BoundedGapsBy`, `EvGapLe` and `Delta` under
their real fully-qualified names from Mathlib alone, so importing the gallery here already populates
this environment with constants of exactly those names.

`erdos_880`, `erdos_880_order_two` and `erdos_880_order_two_delta` therefore need nothing at all —
they arrive proved, straight from the gallery.

The single theorem below is the one **deliberate restatement** in the pair. The gallery proves the
sharper `erdos_880_delta : Δ (restrictedSums (constA h) h) = ⊤`, naming the explicit HHP07 witness.
The challenge asks only for the existential `∃ A, IsBasisOfOrder A h ∧ Δ (restrictedSums A h) = ⊤`
— which is what HHP07 Theorem 1(ii) actually claims, and which keeps the witness recurrence
(`xseq`, `block`, `constA`) out of the audited surface entirely. Supplying the witness is the whole
content of this file, and it is one line.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/

namespace LeanGallery.Combinatorics.Erdos880

/-- The existential `Δ`-form asked for by the challenge, from the gallery's sharper witnessed form:
`constA h` is a basis of order `h` (`constA_isBasis`) whose restricted-sum set has `Δ = ⊤`
(`erdos_880_delta`). -/
theorem erdos_880_delta_exists (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ Delta (restrictedSums A h) = ⊤ :=
  ⟨constA h, constA_isBasis h hh, erdos_880_delta h hh⟩

end LeanGallery.Combinatorics.Erdos880
