/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.Lemma3

/-!
# Erdős #1050 — the designated statement (AUDIT SURFACE)

**If you are checking that this repository proves the right thing, read THIS file.**

Everything else (`Criterion.lean`, `Approximants.lean`) is the proof engine. The single theorem below
is the load-bearing statement; it is *definitionally* `LeanGallery.NumberTheory.Erdos1050.erdos_1050`, so it cannot drift, but
here the series and the claim are spelled out in full.

To confirm faithfulness you only need to read, in addition to the signature below:
* `LeanGallery.NumberTheory.Erdos1050.S` in `Basic.lean` (1 line) — the series, with its index-base note.

The claim: the real number `S = ∑_{n} 1/(2ⁿ − 3)` is irrational.

* **Problem source.** P. Erdős & R. Graham, relayed at <https://www.erdosproblems.com/1050>
  ("Is `∑ 1/(2ⁿ − 3)` irrational?", answer yes).
* **Resolving theorem.** P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory
  **37** (1991) 253–259 (and the cleaner *On the irrationality of certain series*, Math. Proc. Camb.
  Phil. Soc. **112** (1992) 141–146), specialized to `q = 2, r = −3`.
* **Index convention.** `S` sums `1/(2^(n+2) − 3)` over `n ≥ 0` (all denominators positive). The
  classical series includes finitely many lower terms that are rational; since irrationality is
  invariant under adding/removing finitely many rationals, this is a faithful encoding. A reviewer
  comparing to the literature should confirm exactly this point and nothing else.

When proven, `#print axioms erdos_1050` should end at `[propext, Classical.choice, Quot.sound]`
(kernel-pure; no `native_decide`, no custom axioms).
-/

namespace LeanGallery.NumberTheory.Erdos1050

/-- **Erdős Problem #1050.** The series `∑ 1/(2ⁿ − 3)` is irrational. -/
theorem erdos_1050_irrational : Irrational S := erdos_1050

end LeanGallery.NumberTheory.Erdos1050
