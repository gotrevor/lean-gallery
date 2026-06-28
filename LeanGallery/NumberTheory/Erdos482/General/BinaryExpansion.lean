/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Binary block orbits recover the base-2 floor expansion of their value

A **binary block orbit** is a sequence `orbit : ℕ → ℤ` with `orbit 0 = m` and the doubling-plus-digit
recurrence `orbit (n+1) = 2·orbit n + dₙ`, each digit `dₙ ∈ {0,1}`.  Its real *value* is the binary
number `W = m + ∑ₖ dₖ·2^(−(k+1))`.  Provided the digit sequence is not eventually all `1` (`htail`: every
tail contains a `0` — excluding dyadic boundary values), the orbit is exactly the base-2 block orbit of
`W`:  `⌊W·2ⁿ⌋ = orbit n` for every `n` (`binary_floor_eq`).

This is the bridge that turns a digit-reading *recurrence* orbit (e.g. the cubic self-referential map's
`orbit(n+1) = cubicV3(orbit n)`) into a statement about the floor orbit `⌊W·2ⁿ⌋` of its value, the form
the a.e.-`W` impossibility theorems consume.
-/

open scoped BigOperators
open Filter

namespace LeanGallery.NumberTheory.Erdos482.General

/-- The tail value `∑ⱼ d_{n+j}·2^(−(j+1))` of the digit sequence from index `n`. -/
noncomputable def binTail (d : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, (d (n + j) : ℝ) * (1 / 2) ^ (j + 1)

/-- Each tail term is dominated by the geometric term `(1/2)^(j+1)` (digits in `{0,1}`). -/
private lemma binTerm_le (d : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1) (n j : ℕ) :
    (d (n + j) : ℝ) * (1 / 2) ^ (j + 1) ≤ (1 / 2) ^ (j + 1) := by
  have hpow : (0:ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
  rcases hd (n + j) with h | h <;> rw [h] <;> simp

private lemma binTerm_nonneg (d : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1) (n j : ℕ) :
    0 ≤ (d (n + j) : ℝ) * (1 / 2) ^ (j + 1) := by
  rcases hd (n + j) with h | h <;> rw [h] <;> positivity

/-- The geometric series `∑ⱼ (1/2)^(j+1) = 1`. -/
private lemma tsum_half_succ : ∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 1) = 1 := by
  have h2 : ∑' j : ℕ, ((1:ℝ) / 2) ^ j = (1 - 1 / 2)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  simp_rw [pow_succ]
  rw [tsum_mul_right, h2]
  norm_num

private lemma summable_geom_half : Summable (fun j : ℕ => ((1:ℝ) / 2) ^ (j + 1)) := by
  have h : Summable (fun j : ℕ => ((1:ℝ) / 2) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (h.mul_right (1 / 2)).congr (fun j => (pow_succ (1 / 2) j).symm)

/-- The tail series is summable (comparison with the geometric series). -/
private lemma summable_binTail (d : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1) (n : ℕ) :
    Summable (fun j : ℕ => (d (n + j) : ℝ) * (1 / 2) ^ (j + 1)) :=
  summable_geom_half.of_nonneg_of_le (binTerm_nonneg d hd n) (binTerm_le d hd n)

/-- `binTail` is nonnegative. -/
private lemma binTail_nonneg (d : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1) (n : ℕ) :
    0 ≤ binTail d n :=
  tsum_nonneg (binTerm_nonneg d hd n)

/-- The tail recurrence `2·binTail n = dₙ + binTail (n+1)`. -/
private lemma binTail_rec (d : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1) (n : ℕ) :
    2 * binTail d n = (d n : ℝ) + binTail d (n + 1) := by
  have hsum := summable_binTail d hd n
  rw [binTail, (hsum.tsum_eq_zero_add)]
  have h0 : (d (n + 0) : ℝ) * (1 / 2) ^ (0 + 1) = (d n : ℝ) * (1 / 2) := by norm_num
  have hrest : ∑' j : ℕ, (d (n + (j + 1)) : ℝ) * (1 / 2) ^ (j + 1 + 1)
      = (1 / 2) * binTail d (n + 1) := by
    rw [binTail, ← tsum_mul_left]
    congr 1; ext j
    have : n + (j + 1) = (n + 1) + j := by ring
    rw [this]; ring
  rw [h0, hrest]; ring

/-- `binTail` is `< 1`: dominated by the geometric series `∑(1/2)^(j+1) = 1`, strictly because the
tail contains a `0` digit (`htail`). -/
private lemma binTail_lt_one (d : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1)
    (htail : ∀ n, ∃ k, n ≤ k ∧ d k = 0) (n : ℕ) : binTail d n < 1 := by
  obtain ⟨k, hk, hdk⟩ := htail n
  have hkj : n + (k - n) = k := by omega
  have hlt : binTail d n < ∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 1) := by
    rw [binTail]
    refine Summable.tsum_lt_tsum_of_nonneg (i := k - n) (binTerm_nonneg d hd n)
      (binTerm_le d hd n) ?_ summable_geom_half
    rw [hkj, hdk]; simp only [Int.cast_zero, zero_mul]; positivity
  rwa [tsum_half_succ] at hlt

/-- The orbit/value/tail identity `W·2ⁿ = orbit n + binTail n`, by induction on `n` via the tail
recurrence. -/
private lemma binTail_Wpow (m : ℤ) (d : ℕ → ℤ) (orbit : ℕ → ℤ) (hd : ∀ k, d k = 0 ∨ d k = 1)
    (ho0 : orbit 0 = m) (hostep : ∀ n, orbit (n + 1) = 2 * orbit n + d n)
    (W : ℝ) (hW : W = (m : ℝ) + ∑' k : ℕ, (d k : ℝ) * (1 / 2) ^ (k + 1)) :
    ∀ n, W * 2 ^ n = (orbit n : ℝ) + binTail d n := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, mul_one, hW, ho0, binTail]
    congr 1
    exact tsum_congr (fun j => by rw [Nat.zero_add])
  | succ k ih =>
    have hpow : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by ring
    rw [hpow, ← mul_assoc, ih]
    have hrec := binTail_rec d hd k
    have hostepk : (orbit (k + 1) : ℝ) = 2 * orbit k + d k := by
      have := hostep k; push_cast [this]; ring
    rw [hostepk]; linarith

/-- **A binary block orbit recovers the base-2 floor expansion of its value.**  If `orbit 0 = m`,
`orbit (n+1) = 2·orbit n + dₙ` with each `dₙ ∈ {0,1}`, the digit sequence is not eventually all `1`
(`htail`), and `W = m + ∑ₖ dₖ·2^(−(k+1))`, then `⌊W·2ⁿ⌋ = orbit n` for every `n`. -/
theorem binary_floor_eq (m : ℤ) (d : ℕ → ℤ) (orbit : ℕ → ℤ)
    (hd : ∀ k, d k = 0 ∨ d k = 1) (ho0 : orbit 0 = m)
    (hostep : ∀ n, orbit (n + 1) = 2 * orbit n + d n)
    (htail : ∀ n, ∃ k, n ≤ k ∧ d k = 0)
    (W : ℝ) (hW : W = (m : ℝ) + ∑' k : ℕ, (d k : ℝ) * (1 / 2) ^ (k + 1)) (n : ℕ) :
    ⌊W * 2 ^ n⌋ = orbit n := by
  have hWpow := binTail_Wpow m d orbit hd ho0 hostep W hW n
  rw [Int.floor_eq_iff, hWpow]
  refine ⟨by linarith [binTail_nonneg d hd n], by linarith [binTail_lt_one d hd htail n]⟩

end LeanGallery.NumberTheory.Erdos482.General
