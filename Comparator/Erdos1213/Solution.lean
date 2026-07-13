/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Statement
import LeanGallery.Combinatorics.Erdos1213.Anchors

/-!
# Erdős #1213 — comparator SOLUTION

Discharges the `sorry`s in `Challenge.lean` by bringing the real development into scope. This file
declares **no definitions**: `Challenge.lean` re-derives `csum`, `AllCSumsDistinct`,
`validLastTerms`, `hegyvariF` and `seqOf` under their real fully-qualified names from Mathlib alone,
so importing the gallery here already populates this environment with constants of exactly those
names. Comparator's job is to check the two are the *same declarations*.

`erdos_1213`, `erdos_1213_f_finite` and `hegyvariF_ge_1_1` therefore need nothing at all — they
arrive proved, straight from the gallery.

The two `AllCSumsDistinct` anchors are the only declarations here. They are theorems the gallery
does not happen to state under those names (it carries the machinery — the `Bool` mirror `distinctB`
and `distinctB_iff` — but not these two corollaries), so they are proved here, against the gallery's
genuine `AllCSumsDistinct` and `seqOf`. No definition is copied, and nothing is bridged.

Every proof used here is axiom-clean: no `native_decide` (which would add `Lean.ofReduceBool`) is on
any path — the anchors are closed by kernel `decide` only.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/

namespace LeanGallery.Combinatorics.Erdos1213

/-- Positive anchor. Kernel-`decide`d through the gallery's `Bool` mirror `distinctB`
(`distinctB_iff : distinctB a s = true ↔ AllCSumsDistinct a s`) — this is exactly the `by decide`
that already discharges the `hdist` argument of `hegyvariF_ge_1_1` in `Anchors.lean`. -/
theorem anchor_valid : AllCSumsDistinct (seqOf [1, 2]) 2 := by
  rw [← distinctB_iff]
  decide

/-- Negative anchor. Proved by exhibiting the collision explicitly rather than by a decision
procedure: the blocks `(1,2)` and `(3,3)` of `[1, 2, 3]` both have c-sum `3`, yet `1 ≠ 3`. -/
theorem anchor_collision : ¬ AllCSumsDistinct (seqOf [1, 2, 3]) 3 := by
  intro h
  have hc : csum (seqOf [1, 2, 3]) 1 2 = csum (seqOf [1, 2, 3]) 3 3 := by decide
  obtain ⟨h1, -⟩ :=
    h 1 2 3 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hc
  omega

end LeanGallery.Combinatorics.Erdos1213
