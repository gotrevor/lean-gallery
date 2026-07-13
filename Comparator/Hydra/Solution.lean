/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Logic.Hydra.Statement

/-!
# Kirby–Paris hydra — comparator SOLUTION

Discharges the `sorry` in `Challenge.lean` by bringing the real development into scope. Unlike the
`Erdos403` pair, this file declares **nothing** — and that is not a shortcut, it is the point.

## Why there is nothing to write here

The statement closure of `hydra_terminates` contains three **inductive** types (`Hydra`, `Chop`,
`Step`). Inductive types are *generative*: had the challenge declared its own copies under a fresh
namespace (say `Hydra.Hydra`), those copies would be **different types** from the gallery's, no
amount of `rfl` would bridge them, and this file would have to ship a hand-written transport across
an isomorphism — new, unaudited code sitting directly on the trust path, buying nothing.

So `Challenge.lean` instead re-derives the gallery's constants **under their own names**
(`LeanGallery.Logic.Hydra.Hydra`, `.leaf`, `.Chop`, `.Step`, `.hydra_terminates`) from Mathlib
alone, importing nothing from this repo. Importing the real `Statement` here therefore populates
this environment with constants of exactly those names — and comparator's job becomes to check that
the two are *the same declarations*:

* `compareAt` compares the challenge's and the solution's `hydra_terminates` at the level of
  `ConstantVal` (name, universe params, **type**), then walks the transitive constant closure of
  that type — `Step` and its constructors, hence `Chop` and its constructors, hence `Hydra`,
  `Hydra.node`, `Hydra.leaf`, `List.Perm`, `List.replicate` — demanding a byte-identical
  `ConstantInfo` for every one of them (`Comparator/Compare.lean`, `runForUsedConsts`);
* `checkAxioms` then walks the *gallery's* proof and rejects any axiom outside the whitelist;
* the Lean kernel (and nanoda) replay the whole thing.

The certificate you get is thus about the gallery's genuine `hydra_terminates`, with no
isomorphism-shaped gap in the middle. If anyone ever edits the gallery's `Hydra`, `Chop`, `Step`,
`leaf` or the headline's statement, comparator fails here — which is exactly the tripwire we want.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/
