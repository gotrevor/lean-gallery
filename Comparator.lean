/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Comparator harness — machine-checked, statement-level trust

Library root for the `comparator/` challenge-solution pairs. Each result in the gallery gets a
`Comparator/<Result>/` directory holding:

* `Challenge.lean` — imports **only Mathlib**, defines every notion used, states the headlines with
  `sorry`. **This is the file a human audits.** It is small on purpose.
* `Solution.lean` — imports the real development and discharges them.
* `config.json` — the theorem list and the permitted-axiom whitelist.

[`leanprover/comparator`](https://github.com/leanprover/comparator) then certifies that the solution
proves *the challenge's* statements (every declaration used in a statement must be identical in both
environments), under the Lean kernel, using no axioms outside the whitelist.

This is deliberately **not** imported by `LeanGallery.lean`: the challenge files contain `sorry` by
design, and the main library builds with warnings-as-errors.

Why it exists: `#print axioms` certifies the *proof*, not the *statement*. `scripts/AxiomCheck.lean`
already pins the axiom set of every headline; comparator closes the other half by pinning the
statement itself against a mathlib-only rendering that a reader can check by eye.
-/
