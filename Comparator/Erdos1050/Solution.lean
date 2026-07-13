/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050

/-!
# Erdős #1050 — comparator SOLUTION

Discharges the `sorry`s in `Challenge.lean` by bringing the real development into scope. This file
declares **nothing**.

`Challenge.lean` re-derives `S` and all nine headline theorems under their real fully-qualified
names from Mathlib alone. Importing the gallery here populates this environment with constants of
exactly those names — `erdos_1050` and `erdos_1050_irrational` from `Statement.lean`,
`borwein_thm1_abs` from `GeneralAssembly.lean`, and the `erdos_1050.variants.*` family from
`Variants.lean`. Comparator then checks that the two are the *same declarations*, replays the
gallery's proofs through the Lean kernel and nanoda, and rejects any axiom outside `propext` /
`Quot.sound` / `Classical.choice`.

Nothing is bridged, transported or re-proved here: the certificate is about the gallery's genuine
`erdos_1050`, not a namespace-local clone of it.

⚠️ The gallery module imported here also carries the **open** [Er88c] conjecture
`erdos_1050.variants.transcendental` (a deliberate `sorry`, pinned by `#guard_msgs`). It is
deliberately **not** in the challenge — a challenge may contain only theorems the solution actually
proves — and nothing in the challenge depends on it. The only statement that mentions it takes it as
a *hypothesis* (`…implies_erdos_1050`), so every proof certified here stays axiom-clean.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/
