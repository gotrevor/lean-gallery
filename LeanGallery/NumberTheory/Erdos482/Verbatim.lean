/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.Main

/-!
# Erdős #482 in the website's own indexing

erdosproblems.com/482 states the problem with a 1-indexed sequence: $a_1 = 1$,
$a_{n+1} = \lfloor \sqrt{2}(a_n + 1/2) \rfloor$, and claims that $a_{2n+1} - 2a_{2n-1}$ is the
$n$-th digit of the binary expansion $\sqrt{2} = 1.0110101\ldots_2$, counting the leading `1` as
the first digit.

The development elsewhere uses the 0-indexed `u` with `u k = a (k+1)`, and its headline
`graham_pollak` is about the *even*-indexed terms `a (2n+2) − 2 a (2n)`, which give the digits after
the binary point.  This file proves the literal odd-index statement from the closed form `gp_pair`.
-/

namespace LeanGallery.NumberTheory.Erdos482
open Real

/-- The Graham–Pollak sequence in the website's 1-indexing: `a 1 = 1`,
`a (n+1) = ⌊√2·(a n + 1/2)⌋` for `n ≥ 1`.  The value `a 0` is unused. -/
noncomputable def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => ⌊Real.sqrt 2 * ((a (n + 1) : ℝ) + 1 / 2)⌋₊

theorem a_succ (n : ℕ) : a (n + 1) = u n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [a, ih, u]

/-- `⌊2z⌋ − 2⌊z⌋` is the parity of `⌊2z⌋` for `z ≥ 0`. -/
theorem floor_two_mul_sub_eq_mod (z : ℝ) (hz : 0 ≤ z) :
    ⌊2 * z⌋ - 2 * ⌊z⌋ = ((⌊2 * z⌋₊ % 2 : ℕ) : ℤ) := by
  have h2z : (0 : ℝ) ≤ 2 * z := by linarith
  have hdiv : ⌊z⌋₊ = ⌊2 * z⌋₊ / 2 := by
    have := Nat.floor_div_natCast (2 * z) 2
    push_cast at this
    rw [← this]
    congr 1
    ring
  rw [← Int.natCast_floor_eq_floor hz, ← Int.natCast_floor_eq_floor h2z, hdiv]
  omega

/-- **Erdős #482, verbatim.**  For every `n ≥ 1`, `a (2n+1) − 2·a (2n−1)` is the `n`-th binary digit
of `√2 = 1.0110101…₂`, i.e. `⌊√2 · 2^(n−1)⌋ mod 2`. -/
theorem erdos_482_verbatim (n : ℕ) (hn : 1 ≤ n) :
    (a (2 * n + 1) : ℤ) - 2 * (a (2 * n - 1) : ℤ)
      = ((⌊Real.sqrt 2 * 2 ^ (n - 1)⌋₊ % 2 : ℕ) : ℤ) := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
  rw [e1, a_succ, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, a_succ, Nat.add_sub_cancel]
  cases m with
  | zero =>
    have h2 := (gp_pair 0).2
    have hfl : ⌊Real.sqrt 2⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast
        exact Real.one_le_sqrt.mpr (by norm_num)
      · push_cast
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
    have hfln : ⌊Real.sqrt 2⌋₊ = 1 := by
      have := Int.natCast_floor_eq_floor hs0
      omega
    simp only [pow_zero, mul_one, zero_add] at h2 ⊢
    rw [hfln, hfl] at *
    simp [u] at h2 ⊢
    omega
  | succ k =>
    have hA := (gp_pair (k + 1)).2
    have hB := (gp_pair k).2
    have hz : (0 : ℝ) ≤ Real.sqrt 2 * 2 ^ k := by positivity
    have key := floor_two_mul_sub_eq_mod (Real.sqrt 2 * 2 ^ k) hz
    have e2 : 2 * (Real.sqrt 2 * 2 ^ k) = Real.sqrt 2 * 2 ^ (k + 1) := by ring
    rw [e2] at key
    rw [← key, hA, show 2 * (k + 1) = 2 * k + 2 by ring, hB]
    ring

/-- **Erdős #482, verbatim, in Mathlib's digits.**  The `n`-th binary digit of `√2`, counting the
leading `1` as digit 1, is digit `n − 1` of `√2 / 2 = 0.10110101…₂` in `Real.digits`; and those
digits are the binary expansion, since they reconstruct `√2 / 2`. -/
theorem erdos_482_verbatim_digits :
    (∀ n : ℕ, 1 ≤ n →
      (a (2 * n + 1) : ℤ) - 2 * (a (2 * n - 1) : ℤ)
        = ((Real.digits (Real.sqrt 2 / 2) 2 (n - 1) : ℕ) : ℤ)) ∧
      Real.ofDigits (Real.digits (Real.sqrt 2 / 2) 2) = Real.sqrt 2 / 2 := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [erdos_482_verbatim n hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Real.digits, Fin.val_ofNat, Nat.add_sub_cancel]
    congr 3
    push_cast
    rw [pow_succ]
    ring
  · refine Real.ofDigits_digits (by norm_num) ⟨by positivity, ?_⟩
    rw [div_lt_one (by norm_num), Real.sqrt_lt' (by norm_num)]
    norm_num
