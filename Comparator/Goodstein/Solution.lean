/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Logic.Goodstein.Statement

/-!
# Goodstein's theorem — comparator SOLUTION

Discharges the `sorry` in `Challenge.lean` by bringing the real development into scope. This file
declares **nothing** — and that is not a shortcut, it is the point.

## Why there is nothing to write here

`Challenge.lean` re-derives the gallery's constants (`base`, `bump`, `goodsteinSeq`,
`goodstein_terminates`) **under their own fully-qualified names**, from Mathlib alone, importing
nothing from this repo. Importing the real `Statement` here therefore populates this environment
with constants of exactly those names, and comparator's job becomes to check that the two are *the
same declarations*:

* `compareAt` compares the challenge's and the solution's `goodstein_terminates` at the level of
  `ConstantVal` (name, universe params, **type**), then walks the transitive constant closure of
  that type — `goodsteinSeq`, hence `bump` and `base` — demanding a byte-identical `ConstantInfo`
  for every one of them;
* `checkAxioms` then walks the *gallery's* proof and rejects any axiom outside the whitelist;
* the Lean kernel (and nanoda) replay the whole thing.

The alternative — a challenge under a fresh namespace, whose copies this file would have to bridge
to the gallery's — is strictly worse here. `bump` is defined by **well-founded recursion**, and Lean
marks such definitions **irreducible**: the two copies would not be interchangeable by `rfl` or
unification at default transparency, so the bridge could not be a one-liner. It took a pointwise
`bump_eq` by strong induction (unfolding both sides through their equation lemmas), a
`goodsteinSeq_eq` lifting it along the sequence recursion, and a transport of the headline across
that — roughly fifty lines of hand-written glue on the trust path, whose only purpose was to undo a
namespace choice. Using the gallery's real names deletes all of it, and upgrades the certificate
from "a faithful copy of the theorem holds" to "**the gallery's theorem** holds".

If anyone ever edits the gallery's `bump`, `base`, `goodsteinSeq` or the headline's statement,
comparator fails here — which is exactly the tripwire we want.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/
