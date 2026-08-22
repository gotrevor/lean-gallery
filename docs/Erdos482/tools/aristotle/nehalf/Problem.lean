import Mathlib

/-
GOAL: √2's binary orbit never lands exactly on ½.

For every `n : ℕ`, `Int.fract (Real.sqrt 2 * 2 ^ n) ≠ 1 / 2`.

Reason: if `Int.fract (√2 · 2^n) = 1/2`, then `√2 · 2^n = ⌊√2·2^n⌋ + 1/2`, so
`√2 = (2·⌊√2·2^n⌋ + 1) / 2^(n+1)`, a rational — contradicting irrationality of √2.
mathlib: `irrational_sqrt_two : Irrational (Real.sqrt 2)`, and `Irrational` means not in the
range of the rational cast.  `Int.fract x = x - ⌊x⌋`.  A clean route: from the hypothesis derive
`Real.sqrt 2 = (2 * ⌊√2·2^n⌋ + 1) / 2^(n+1)` and feed it to `irrational_sqrt_two` via
`Irrational` / `Rat`/`ℚ` cast lemmas (e.g. show the RHS `∈ Set.range ((↑) : ℚ → ℝ)`).
-/

theorem fract_sqrt2_pow_ne_half (n : ℕ) :
    Int.fract (Real.sqrt 2 * 2 ^ n) ≠ 1 / 2 := by
  sorry
