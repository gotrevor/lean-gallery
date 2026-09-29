/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-
GOAL: the binary-shift / doubling identity for `Int.fract`.

For every real `x`, `Int.fract (2 * x) = Int.fract (2 * Int.fract x)`.

This is the map underlying the binary digit shift of any real: writing `x = ⌊x⌋ + Int.fract x`,
we get `2*x = 2*⌊x⌋ + 2*Int.fract x` with `2*⌊x⌋ ∈ ℤ`, so the fractional parts agree
(`Int.fract` is invariant under adding an integer).  Useful mathlib facts:
`Int.fract_int_add`, `Int.self_sub_floor`, `Int.fract_add_int`, `Int.fract_intCast`.
-/

theorem fract_two_mul (x : ℝ) :
    Int.fract (2 * x) = Int.fract (2 * Int.fract x) := by
  sorry
