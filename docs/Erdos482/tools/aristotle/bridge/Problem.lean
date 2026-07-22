import Mathlib

/-
GOAL: bridge Stoll's floor-formula binary digit to mathlib's `Real.digits`.

`Real.digits x b i = Fin.ofNat _ ⌊x * b ^ (i+1)⌋₊` (defined for x ∈ [0,1), base b).
For a real `x` with `1 ≤ x < 2` (so `Int.fract x = x - 1`), the i-th base-2 digit of the
fractional part `Int.fract x` equals the floor-difference digit `⌊x·2^(i+1)⌋ - 2·⌊x·2^i⌋`,
which lies in {0,1}.

Proof strategy:
* `Real.digits (Int.fract x) 2 i = Fin.ofNat 2 ⌊Int.fract x · 2^(i+1)⌋₊`, whose `.val`
  is `⌊Int.fract x · 2^(i+1)⌋₊ % 2`.
* Set `z := x * 2^i`. Then `x*2^(i+1) = 2*z`, `Int.fract x · 2^(i+1) = 2*z - 2^(i+1)`
  (since `Int.fract x = x - 1` because `⌊x⌋ = 1` from `1 ≤ x < 2`).
* `⌊2*z - 2^(i+1)⌋ = ⌊2z⌋ - 2^(i+1)`. Write `N := ⌊2z⌋ = ⌊x*2^(i+1)⌋`, `M := ⌊z⌋ = ⌊x*2^i⌋`.
  Then `N - 2M ∈ {0,1}` (floor doubling), and `N - 2^(i+1) = 2*(M - 2^i) + (N - 2M) ≥ 0`.
* So `⌊Int.fract x · 2^(i+1)⌋₊ = (N - 2^(i+1)).toNat`, and its `% 2` equals `N - 2M`.
  Conclude via `omega` once `N = 2M + d`, `d ∈ {0,1}`, `N ≥ 2^(i+1)` are in hand.
-/

theorem digit_bridge (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x < 2) (i : ℕ) :
    ((Real.digits (Int.fract x) 2 i : ℕ) : ℤ)
      = ⌊x * 2 ^ (i + 1)⌋ - 2 * ⌊x * 2 ^ i⌋ := by
  sorry
