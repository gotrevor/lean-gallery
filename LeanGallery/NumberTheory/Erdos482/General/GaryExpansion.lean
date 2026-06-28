/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Base-`g` block orbits recover the base-`g` floor expansion of their value

The base-`g` (`g ≥ 2`) analogue of `BinaryExpansion`.  A **base-`g` block orbit** is a sequence
`orbit : ℕ → ℤ` with `orbit 0 = m` and `orbit (n+1) = g·orbit n + dₙ`, each digit `dₙ ∈ {0,…,g-1}`.  Its
real value is `W = m + ∑ₖ dₖ·g^{−(k+1)}`.  Provided the digit sequence is not eventually all `g-1`
(`htail`: every tail contains a digit `≤ g-2` — excluding `g`-adic boundary values), the orbit is exactly
the base-`g` block orbit of `W`: `⌊W·gⁿ⌋ = orbit n` for every `n` (`gary_floor_eq`).

Bridge for the base-`g` self-referential capstones (`BaseGFinish`), turning a digit-reading *recurrence*
orbit into a statement about the floor orbit `⌊W·gⁿ⌋` of its value.
-/

open scoped BigOperators
open Filter

namespace LeanGallery.NumberTheory.Erdos482.General

variable {g : ℕ}

/-- The tail value `∑ⱼ d_{n+j}·g^{−(j+1)}` of the digit sequence from index `n`. -/
noncomputable def garyTail (g : ℕ) (d : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, (d (n + j) : ℝ) * (1 / g) ^ (j + 1)

private lemma garyTerm_le (hg : 2 ≤ g) (d : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1) (n j : ℕ) :
    (d (n + j) : ℝ) * (1 / g) ^ (j + 1) ≤ ((g : ℝ) - 1) * (1 / g) ^ (j + 1) := by
  have hpow : (0:ℝ) ≤ (1 / g) ^ (j + 1) := by positivity
  have hdle : (d (n + j) : ℝ) ≤ (g : ℝ) - 1 := by
    have := (hd (n + j)).2; exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hdle hpow

private lemma garyTerm_nonneg (d : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1) (n j : ℕ) :
    0 ≤ (d (n + j) : ℝ) * (1 / g) ^ (j + 1) := by
  have hd0 : (0 : ℝ) ≤ (d (n + j) : ℝ) := by exact_mod_cast (hd (n + j)).1
  positivity

private lemma summable_geom_succ (hg : 2 ≤ g) :
    Summable (fun j : ℕ => ((1:ℝ) / (g:ℝ)) ^ (j + 1)) := by
  have hgr : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < (g : ℝ) := by linarith
  have hlt1 : (1:ℝ) / (g:ℝ) < 1 := by rw [div_lt_one hg0]; linarith
  have hge0 : (0:ℝ) ≤ (1:ℝ) / (g:ℝ) := by positivity
  have h : Summable (fun j : ℕ => ((1:ℝ) / (g:ℝ)) ^ j) :=
    summable_geometric_of_lt_one hge0 hlt1
  exact (h.mul_right (1 / (g:ℝ))).congr (fun j => (pow_succ (1 / (g:ℝ)) j).symm)

/-- The geometric series `∑ⱼ (g-1)·(1/g)^(j+1) = 1`. -/
private lemma tsum_gary_succ (hg : 2 ≤ g) :
    ∑' j : ℕ, ((g : ℝ) - 1) * ((1:ℝ) / (g:ℝ)) ^ (j + 1) = 1 := by
  have hgr : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < (g : ℝ) := by linarith
  have hlt1 : (1:ℝ) / (g:ℝ) < 1 := by rw [div_lt_one hg0]; linarith
  have hge0 : (0:ℝ) ≤ (1:ℝ) / (g:ℝ) := by positivity
  have h2 : ∑' j : ℕ, ((1:ℝ) / (g:ℝ)) ^ j = (1 - 1 / (g:ℝ))⁻¹ :=
    tsum_geometric_of_lt_one hge0 hlt1
  rw [tsum_mul_left]
  have hgeom : ∑' j : ℕ, ((1:ℝ) / (g:ℝ)) ^ (j + 1) = (1 / (g:ℝ)) * (1 - 1 / (g:ℝ))⁻¹ := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, h2]; ring
  rw [hgeom]
  have hgne : (g:ℝ) ≠ 0 := by positivity
  have hg1ne : (g:ℝ) - 1 ≠ 0 := by linarith
  field_simp

private lemma summable_gary_geom (hg : 2 ≤ g) :
    Summable (fun j : ℕ => ((g : ℝ) - 1) * ((1:ℝ) / (g:ℝ)) ^ (j + 1)) :=
  (summable_geom_succ hg).mul_left ((g:ℝ) - 1)

/-- The tail series is summable (comparison with the geometric series). -/
private lemma summable_garyTail (hg : 2 ≤ g) (d : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1) (n : ℕ) :
    Summable (fun j : ℕ => (d (n + j) : ℝ) * (1 / g) ^ (j + 1)) :=
  (summable_gary_geom hg).of_nonneg_of_le (garyTerm_nonneg d hd n) (garyTerm_le hg d hd n)

private lemma garyTail_nonneg (d : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1) (n : ℕ) :
    0 ≤ garyTail g d n :=
  tsum_nonneg (garyTerm_nonneg d hd n)

/-- The tail recurrence `g·garyTail n = dₙ + garyTail (n+1)`. -/
private lemma garyTail_rec (hg : 2 ≤ g) (d : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1) (n : ℕ) :
    (g : ℝ) * garyTail g d n = (d n : ℝ) + garyTail g d (n + 1) := by
  have hgr : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg0 : (g : ℝ) ≠ 0 := by positivity
  have hsum := summable_garyTail hg d hd n
  rw [garyTail, (hsum.tsum_eq_zero_add)]
  have h0 : (d (n + 0) : ℝ) * (1 / (g:ℝ)) ^ (0 + 1) = (d n : ℝ) * (1 / g) := by norm_num
  have hrest : ∑' j : ℕ, (d (n + (j + 1)) : ℝ) * (1 / (g:ℝ)) ^ (j + 1 + 1)
      = (1 / g) * garyTail g d (n + 1) := by
    rw [garyTail, ← tsum_mul_left]
    congr 1; ext j
    have : n + (j + 1) = (n + 1) + j := by ring
    rw [this]; ring
  rw [h0, hrest]; field_simp

/-- `garyTail < 1`: dominated by `∑(g-1)·(1/g)^(j+1) = 1`, strictly because the tail contains a digit
`≤ g-2` (`htail`). -/
private lemma garyTail_lt_one (hg : 2 ≤ g) (d : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1)
    (htail : ∀ n, ∃ k, n ≤ k ∧ d k ≤ (g : ℤ) - 2) (n : ℕ) : garyTail g d n < 1 := by
  obtain ⟨k, hk, hdk⟩ := htail n
  have hkj : n + (k - n) = k := by omega
  have hlt : garyTail g d n < ∑' j : ℕ, ((g : ℝ) - 1) * ((1:ℝ) / g) ^ (j + 1) := by
    rw [garyTail]
    refine Summable.tsum_lt_tsum_of_nonneg (i := k - n) (garyTerm_nonneg d hd n)
      (garyTerm_le hg d hd n) ?_ (summable_gary_geom hg)
    rw [hkj]
    have hgr : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have hpow : (0:ℝ) < ((1:ℝ) / g) ^ (k - n + 1) := by positivity
    have hdk' : (d k : ℝ) ≤ (g : ℝ) - 2 := by
      have := hdk; exact_mod_cast this
    have : (d k : ℝ) < (g : ℝ) - 1 := by linarith
    exact mul_lt_mul_of_pos_right this hpow
  rwa [tsum_gary_succ hg] at hlt

/-- The orbit/value/tail identity `W·gⁿ = orbit n + garyTail n`. -/
private lemma garyTail_Wpow (hg : 2 ≤ g) (m : ℤ) (d : ℕ → ℤ) (orbit : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1)
    (ho0 : orbit 0 = m) (hostep : ∀ n, orbit (n + 1) = (g : ℤ) * orbit n + d n)
    (W : ℝ) (hW : W = (m : ℝ) + ∑' k : ℕ, (d k : ℝ) * (1 / g) ^ (k + 1)) :
    ∀ n, W * (g : ℝ) ^ n = (orbit n : ℝ) + garyTail g d n := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, mul_one, hW, ho0, garyTail]
    congr 1
    exact tsum_congr (fun j => by rw [Nat.zero_add])
  | succ k ih =>
    have hpow : (g : ℝ) ^ (k + 1) = (g:ℝ) ^ k * g := by ring
    rw [hpow, ← mul_assoc, ih]
    have hrec := garyTail_rec hg d hd k
    have hostepk : (orbit (k + 1) : ℝ) = (g:ℝ) * orbit k + d k := by
      have := hostep k; push_cast [this]; ring
    rw [hostepk]
    linear_combination hrec

/-- **A base-`g` block orbit recovers the base-`g` floor expansion of its value.**  If `orbit 0 = m`,
`orbit (n+1) = g·orbit n + dₙ` with each `dₙ ∈ {0,…,g-1}`, the digit sequence is not eventually all `g-1`
(`htail`: every tail has a digit `≤ g-2`), and `W = m + ∑ₖ dₖ·g^{−(k+1)}`, then `⌊W·gⁿ⌋ = orbit n` for
every `n`.  Base-`g` analogue of `binary_floor_eq`. -/
theorem gary_floor_eq (hg : 2 ≤ g) (m : ℤ) (d : ℕ → ℤ) (orbit : ℕ → ℤ)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ (g : ℤ) - 1) (ho0 : orbit 0 = m)
    (hostep : ∀ n, orbit (n + 1) = (g : ℤ) * orbit n + d n)
    (htail : ∀ n, ∃ k, n ≤ k ∧ d k ≤ (g : ℤ) - 2)
    (W : ℝ) (hW : W = (m : ℝ) + ∑' k : ℕ, (d k : ℝ) * (1 / g) ^ (k + 1)) (n : ℕ) :
    ⌊W * (g : ℝ) ^ n⌋ = orbit n := by
  have hWpow := garyTail_Wpow hg m d orbit hd ho0 hostep W hW n
  rw [Int.floor_eq_iff, hWpow]
  refine ⟨by linarith [garyTail_nonneg d hd n], by linarith [garyTail_lt_one hg d hd htail n]⟩

end LeanGallery.NumberTheory.Erdos482.General
