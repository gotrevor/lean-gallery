/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Main

/-!
# Erdős #1213 — the designated statement (AUDIT SURFACE)

**If you are checking that this repository proves the right thing, read THIS file.**

Everything else (`Counting.lean`, `Analytic.lean`, `Main.lean`) is the proof engine. The two theorems
below are the load-bearing statements: each is *definitionally* the corresponding engine theorem, so it
cannot drift, but here the bound `L` is written out verbatim and the English is spelled out.

To confirm faithfulness you only need to read, in addition to the signatures below:
* `csum` and `AllCSumsDistinct` in `Basic.lean` (≈ 4 lines) — the block-sum and distinctness notions;
* `validLastTerms` and `hegyvariF` in `Main.lean` (≈ 6 lines) — the definition of the paper's `f(a,K)`.

Source: N. Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar. **48** (1986) 193–200,
Theorem 3 (DOI 10.1007/BF01949064). Problem page: <https://www.erdosproblems.com/1213>.

Both theorems are axiom-clean: `#print axioms` ends at `[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

/-- **Erdős Problem #1213 — Hegyvári's Theorem 3 (last-term form).**

Let `a 1 < a 2 < … < a s` be strictly increasing positive integers whose consecutive gaps are at most
`K` (`a (i+1) ≤ a i + K`). If **all** consecutive-block sums `csum a u v = a u + … + a v` are distinct
(`AllCSumsDistinct`), then the last term is bounded:
```
a s  <  (a 1 + K/2)·e^(K+1) + K·e^(2K+2).
```
In particular no such "all block-sums distinct" sequence can be arbitrarily long.

Sanity anchors from the paper (largest achievable last term `f(a,K)`): `f(1,1)=2`, `f(2,1)=4`,
`f(1,2)=7`, `f(2,2)=10` (the bound is correct but loose — e.g. it only asserts `f(1,1) < 65.7`).

This is `hegyvari_thm3` with the bound written out; the proof just unfolds `hegyvariBound`. -/
theorem erdos_1213 (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap  : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hdist : AllCSumsDistinct a s) :
    (a s : ℝ) <
      ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) := by
  have h := hegyvari_thm3 a s K hK hs ha1 hmono hgap hdist
  simpa only [hegyvariBound] using h

/-- **Erdős Problem #1213 — finiteness of `f(a,K)`.**

`hegyvariF init K` is the paper's `f(a,K)`: the supremum (over all valid sequences with first term
`init` and gaps `≤ K` whose block-sums are all distinct) of the last term. This theorem says that
supremum is finite, bounded by the same constant `L`:
```
f(init, K)  ≤  (init + K/2)·e^(K+1) + K·e^(2K+2).
```
This is the form closest to how the problem is posed ("is `f(a,K)` finite?"). It is `hegyvariF_le_bound`
with the bound written out. -/
theorem erdos_1213_f_finite (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init) :
    (hegyvariF init K : ℝ) ≤
      ((init : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) := by
  have h := hegyvariF_le_bound init K hK ha
  simpa only [hegyvariBound] using h

end LeanGallery.Combinatorics.Erdos1213
