/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos403.Basic
import LeanGallery.NumberTheory.Erdos403.Engine

/-!
# Erdős #403: the headline theorems (designated audit surface)

**Designated audit surface** (with `Basic.lean`). The proof engine lives in `Engine.lean`; these
statements delegate to it, so they are definitionally the proved results.

## What this says
A *sum of distinct factorials* is `factSum S = ∑_{a ∈ S} a!` (see `Basic.lean`).

* `erdos_403_sharp` — if `factSum S = 2 ^ m` then `m ≤ 7`. With `Basic.witness`
  (`factSum {2,3,5} = 2⁷`) this is sharp: the largest power of two that is a sum of distinct
  factorials is `2⁷ = 128`.
* `erdos_403_finite` — exactly what Erdős #403 asks: only finitely many powers of two are sums of
  distinct factorials, i.e. `{S | ∃ m, factSum S = 2 ^ m}` is finite.

Both are `sorry`-free and kernel-pure; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanGallery.NumberTheory.Erdos403

open scoped Nat

/-- **Erdős #403 (sharp form).** The largest power of two that is a sum of distinct factorials is
`2⁷ = 2! + 3! + 5! = 128`; every solution has `m ≤ 7`. (Proof in `Engine.lean`; this is the thin,
faithful audit statement. Sharpness: `Basic.witness` realizes `m = 7`.) -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 :=
  erdos_403_sharp_engine h

/-- **Erdős #403 (finiteness).** Only finitely many powers of two are sums of distinct factorials.
(Proof in `Engine.lean`; this is the thin, faithful audit statement.) -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite :=
  erdos_403_finite_engine

end LeanGallery.NumberTheory.Erdos403
