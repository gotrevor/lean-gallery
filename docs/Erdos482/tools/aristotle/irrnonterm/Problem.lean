import Mathlib

/-
GOAL: for ANY irrational y ≥ 0, its base-2 Real.digits are not eventually zero (the expansion of
an irrational never terminates). Generalizes the √2 case.

`Real.digits y 2 i = Fin.ofNat _ ⌊y·2^(i+1)⌋₊`; for y ≥ 0 its value is `⌊y·2^(i+1)⌋ - 2⌊y·2^i⌋`
(floor-difference; provable: ⌊2z⌋-2⌊z⌋∈{0,1} and floor mod 2).

Strategy (proof by contradiction; assume digit i = 0 for all i ≥ N):
* digit i = 0  ⟹  ⌊y·2^(i+1)⌋ = 2·⌊y·2^i⌋ for i ≥ N.
* Induct: ⌊y·2^(N+k)⌋ = 2^k · ⌊y·2^N⌋ for all k. Let M := ⌊y·2^N⌋, c := M / 2^N.
* From ⌊·⌋ ≤ · < ⌊·⌋+1: c ≤ y and y < c + 1/2^(N+k) for every k.
* Archimedean (exists_pow_lt_of_lt_one with 1/2 < 1): y = c = M/2^N, a rational. Contradicts Irrational y.
-/

theorem digits_two_irrational_not_eventually_zero
    (y : ℝ) (hy0 : 0 ≤ y) (hyirr : Irrational y) :
    ¬ ∃ N, ∀ i, N ≤ i → (Real.digits y 2 i : ℕ) = 0 := by
  sorry
