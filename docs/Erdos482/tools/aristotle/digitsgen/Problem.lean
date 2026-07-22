import Mathlib

/-
GOAL: the i-th base-2 digit of any y ∈ [0,1) is the floor-difference digit.

`Real.digits y b i = Fin.ofNat _ ⌊y * b ^ (i+1)⌋₊`. For base 2 and y ∈ [0,1), show its value
equals `⌊y·2^(i+1)⌋ - 2·⌊y·2^i⌋` (which lies in {0,1} by floor-doubling).

Strategy:
* `(Real.digits y 2 i : ℕ) = ⌊y·2^(i+1)⌋₊ % 2` (unfold + Fin.ofNat val = mod).
* Since y ≥ 0, `(⌊y·2^(i+1)⌋₊ : ℤ) = ⌊y·2^(i+1)⌋ =: N` and `M := ⌊y·2^i⌋`.
* Floor-doubling: `2*M ≤ N ≤ 2*M+1` (from `Int.le_floor`/`Int.floor_lt`, using `y·2^(i+1)=2·(y·2^i)`).
* Then `N - 2M ∈ {0,1}` and `N % 2 = N - 2M`; conclude with `omega`.
-/

theorem digits_eq_floor_sub (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) (i : ℕ) :
    ((Real.digits y 2 i : ℕ) : ℤ) = ⌊y * 2 ^ (i + 1)⌋ - 2 * ⌊y * 2 ^ i⌋ := by
  sorry
