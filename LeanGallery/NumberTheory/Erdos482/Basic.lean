/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #482 — Graham–Pollak: the recurrence extracts the binary digits of √2

`u 0 = 1`,  `u (n+1) = ⌊√2 · (u n + 1/2)⌋`.  Then `u (2n+1) − 2·u (2n−1)` is the n-th binary
digit of √2.  Source: Stoll, *A fancy way to obtain the binary digits of 759250125√2*,
arXiv:0902.4168 (free); orig. Graham–Pollak, Math. Mag. 43 (1970) 143–145.
-/

namespace LeanGallery.NumberTheory.Erdos482
open Real

/-- The Graham–Pollak sequence.  (`noncomputable`: `Real.sqrt` is.) -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-- The n-th binary digit of `t` (Graham–Pollak / Stoll definition): `⌊t·2ⁿ⌋ − 2⌊t·2ⁿ⁻¹⌋ ∈ {0,1}`.
(`noncomputable`: `Int.floor` on `ℝ` is.) -/
noncomputable def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

end LeanGallery.NumberTheory.Erdos482
