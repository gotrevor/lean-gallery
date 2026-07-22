import Mathlib

/- Inlined from our repo (kernel-verified there): the binary-shift map on Int.fract. -/
axiom fract_two_mul (x : ℝ) : Int.fract (2 * x) = Int.fract (2 * Int.fract x)

/-
GOAL: the packaged two-branch form of the pair-5 band bracket.

Let `f := Int.fract (√2 · 2^i)` (so `0 ≤ f < 1`).  The band bracket at step `j = i+1` is
`B = Int.fract (√2 · 2^(i+1)) − √2·f + √2·ε`.  Since `√2·2^(i+1) = 2·(√2·2^i)`,
`fract_two_mul` gives `Int.fract (√2·2^(i+1)) = Int.fract (2·f)`, and on `[0,1)` the doubling map
is `2f` (when `f < ½`) or `2f − 1` (when `f ≥ ½`).  Hence:

  f < ½  ⟹  B = (2 − √2)·f + √2·ε ,      ½ ≤ f  ⟹  B = (2 − √2)·f − 1 + √2·ε .

Hints: `√2·2^(i+1) = 2*(√2·2^i)` by `ring`; then `rw [fract_two_mul]`; case on `f < 1/2` and
compute `Int.fract (2*f)` via `Int.fract = id - ⌊·⌋` with `⌊2f⌋ = 0` or `1` (`Int.floor_eq_iff`).
-/

theorem pair5_band_branch (i : ℕ) (ε : ℝ) :
    (Int.fract (Real.sqrt 2 * 2 ^ i) < 1 / 2 →
        Int.fract (Real.sqrt 2 * 2 ^ (i + 1))
            - Real.sqrt 2 * Int.fract (Real.sqrt 2 * 2 ^ i) + Real.sqrt 2 * ε
          = (2 - Real.sqrt 2) * Int.fract (Real.sqrt 2 * 2 ^ i) + Real.sqrt 2 * ε) ∧
      (1 / 2 ≤ Int.fract (Real.sqrt 2 * 2 ^ i) →
        Int.fract (Real.sqrt 2 * 2 ^ (i + 1))
            - Real.sqrt 2 * Int.fract (Real.sqrt 2 * 2 ^ i) + Real.sqrt 2 * ε
          = (2 - Real.sqrt 2) * Int.fract (Real.sqrt 2 * 2 ^ i) - 1 + Real.sqrt 2 * ε) := by
  sorry
