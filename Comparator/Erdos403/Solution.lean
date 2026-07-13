/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos403.Statement

/-!
# Erdős #403 — comparator SOLUTION

Discharges the `sorry`s in `Challenge.lean` by bringing the real development into scope. This file
declares **nothing**.

`Challenge.lean` re-derives `factSum`, `erdos_403_sharp`, `erdos_403_finite` and `witness` under
their real fully-qualified names from Mathlib alone. Importing `Statement` here (which pulls in
`Basic` — hence `factSum` and `witness` — and `Engine`, which proves the headlines) populates this
environment with constants of exactly those names. Comparator then checks that the two are the
*same declarations*, replays the gallery's proofs through the Lean kernel and nanoda, and rejects
any axiom outside `propext` / `Quot.sound` / `Classical.choice`.

Nothing is bridged, transported or re-proved here: the certificate is about the gallery's genuine
`erdos_403_finite`, not a namespace-local clone of it.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/
