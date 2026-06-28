/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Basic

/-!
The block-count engine (the real work). Build here, lap by lap:
* (3.2) pointwise bound `a_{i+1} ≤ a₁ + i·K` from the gap hypothesis.
* (3.3) block-sum upper bound: `a_{i+1}+…+a_{i+j} ≤ j·a₁ + K·(i·j + j(j-1)/2)` (doubled, to stay in ℕ).
* (3.5) `≥ ⌊D/(Kj) − (a+K/2)/K − j/2⌋` blocks of length `j` with c-sum `< D`.
* (3.6) `S > (D/K)·log A − A(a+K/2)/K − (A+2)²/4`  -- via `log_le_harmonic_floor` (`Σ_{j≤A} 1/j ≥ log A`).
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

variable {a : ℕ → ℕ} {s K : ℕ}

/-- The finset of index-blocks `(u,v)` inside `[1,s]` whose c-sum is `< D`. -/
def smallBlocks (a : ℕ → ℕ) (s D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 s ×ˢ Finset.Icc 1 s).filter (fun p => p.1 ≤ p.2 ∧ csum a p.1 p.2 < D)

/-- The finset of offsets `i ≥ 0` for which the length-`j` block `(i+1, i+j)` lies in `[1,s]` and
has c-sum `< D`.  Mapping `i ↦ (i+1, i+j)` injects this into `smallBlocks`. -/
def offsetSet (a : ℕ → ℕ) (s D j : ℕ) : Finset ℕ :=
  (Finset.range (s + 1)).filter (fun i => i + j ≤ s ∧ csum a (i + 1) (i + j) < D)

/-- **(3.2)** From `a_{i+1} ≤ a_i + K` (for `1 ≤ i < s`) we get the affine pointwise bound
`a_{i+1} ≤ a₁ + i·K`, valid for every offset `i` with `i + 1 ≤ s`.  Proof by induction on `i`. -/
theorem pointwise_bound (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K) :
    ∀ i, i + 1 ≤ s → a (i + 1) ≤ a 1 + i * K := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    -- `a (n+2) ≤ a (n+1) + K ≤ (a 1 + n·K) + K = a 1 + (n+1)·K`
    have hn1 : n + 1 ≤ s := Nat.le_of_succ_le hn
    have hstep : a (n + 1 + 1) ≤ a (n + 1) + K :=
      hgap (n + 1) (Nat.le_add_left 1 n) (Nat.lt_of_succ_le hn)
    have hih : a (n + 1) ≤ a 1 + n * K := ih hn1
    calc a (n + 1 + 1) ≤ a (n + 1) + K := hstep
      _ ≤ (a 1 + n * K) + K := by exact Nat.add_le_add_right hih K
      _ = a 1 + (n + 1) * K := by ring

/-- Strict monotonicity of `a` on `[1,s]` gives `a 1 ≤ a u` for every `1 ≤ u ≤ s`. -/
theorem a_one_le (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (u : ℕ) (h1 : 1 ≤ u) (hu : u ≤ s) : a 1 ≤ a u := by
  obtain ⟨d, rfl⟩ : ∃ d, u = 1 + d := ⟨u - 1, by omega⟩
  clear h1
  induction d with
  | zero => simp
  | succ n ih =>
    have hns : 1 + n ≤ s := by omega
    have hstep : a (1 + n) < a (1 + n + 1) := hmono (1 + n) (by omega) (by omega)
    have hih := ih hns
    have e : 1 + (n + 1) = 1 + n + 1 := by ring
    rw [e]; omega

/-- The c-sum of the length-`j` block at offset `i` (indices `i+1, …, i+j`) equals
`∑_{t < j} a (i+1+t)` -- a reindexing of `csum` onto `Finset.range`. -/
theorem csum_eq_sum_range (a : ℕ → ℕ) (i j : ℕ) :
    csum a (i + 1) (i + j) = ∑ t ∈ Finset.range j, a (i + 1 + t) := by
  rw [csum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have : i + j + 1 - (i + 1) = j := by omega
  rw [this]

/-- **(3.3)** Block-sum upper bound, doubled to stay in ℕ:
`2·(a_{i+1}+…+a_{i+j}) ≤ 2·j·a₁ + K·(2·i·j + j·(j−1))`.
Equivalent to the paper's `a_{i+1}+…+a_{i+j} ≤ j·a₁ + K·(i·j + j(j−1)/2)`.  Needs `i + j ≤ s`. -/
theorem block_sum_bound (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (i j : ℕ) (hij : i + j ≤ s) :
    2 * csum a (i + 1) (i + j) ≤ 2 * j * a 1 + K * (2 * i * j + j * (j - 1)) := by
  rw [csum_eq_sum_range]
  -- termwise: `a (i+1+t) ≤ a 1 + (i+t)·K` for `t < j` (block fits inside `[1,s]`)
  have hterm : ∀ t ∈ Finset.range j, a (i + 1 + t) ≤ a 1 + (i + t) * K := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hle : (i + t) + 1 ≤ s := by omega
    have := pointwise_bound hgap (i + t) hle
    simpa [Nat.add_right_comm, Nat.add_assoc] using this
  have hsum : (∑ t ∈ Finset.range j, a (i + 1 + t)) ≤ ∑ t ∈ Finset.range j, (a 1 + (i + t) * K) :=
    Finset.sum_le_sum hterm
  -- evaluate the RHS sum
  have heval : (∑ t ∈ Finset.range j, (a 1 + (i + t) * K))
      = j * a 1 + K * (i * j) + K * (∑ t ∈ Finset.range j, t) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    have : (∑ t ∈ Finset.range j, (i + t) * K)
        = K * (i * j) + K * (∑ t ∈ Finset.range j, t) := by
      rw [← Finset.sum_mul]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      ring
    rw [this]; ring
  have hgauss : (∑ t ∈ Finset.range j, t) * 2 = j * (j - 1) := Finset.sum_range_id_mul_two j
  calc 2 * (∑ t ∈ Finset.range j, a (i + 1 + t))
      ≤ 2 * (∑ t ∈ Finset.range j, (a 1 + (i + t) * K)) := by
        exact Nat.mul_le_mul_left 2 hsum
    _ = 2 * (j * a 1 + K * (i * j) + K * (∑ t ∈ Finset.range j, t)) := by rw [heval]
    _ = 2 * j * a 1 + K * (2 * i * j) + K * ((∑ t ∈ Finset.range j, t) * 2) := by ring
    _ = 2 * j * a 1 + K * (2 * i * j) + K * (j * (j - 1)) := by rw [hgauss]
    _ = 2 * j * a 1 + K * (2 * i * j + j * (j - 1)) := by ring

/-- Mapping an offset `i` to the block `(i+1, i+j)` is injective. -/
theorem block_of_offset_injOn (a : ℕ → ℕ) (s D j : ℕ) :
    Set.InjOn (fun i => (i + 1, i + j)) (offsetSet a s D j) := by
  intro i _ i' _ h
  simp only [Prod.mk.injEq] at h
  omega

/-- Each `(i+1, i+j)` with `i ∈ offsetSet a s D j` and `1 ≤ j` lies in `smallBlocks a s D`. -/
theorem block_of_offset_mem (a : ℕ → ℕ) (s D j : ℕ) (hj : 1 ≤ j)
    (i : ℕ) (hi : i ∈ offsetSet a s D j) :
    (i + 1, i + j) ∈ smallBlocks a s D := by
  simp only [offsetSet, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨_, hfit, hlt⟩ := hi
  simp only [smallBlocks, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  all_goals omega

/-- **(3.5) Per-length offset count, lower bound.**  If the first `m` offsets `0,…,m−1` all fit
inside `[1,s]` (`hfit`) and satisfy the doubled block-sum sufficient condition for c-sum `< D`
(`hsum`, an integer inequality implied by `block_sum_bound`), then `offsetSet a s D j` has at least
`m` elements.  This isolates the two analytic obligations (fitting + the arithmetic threshold) so
they can be discharged separately with the explicit floor `m ≈ ⌊D/(Kj) − a₁/K − (j−1)/2⌋`. -/
theorem offsetSet_card_ge (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (D j : ℕ) (m : ℕ)
    (hfit : ∀ i, i < m → i + j ≤ s)
    (hsum : ∀ i, i < m → 2 * j * a 1 + K * (2 * i * j + j * (j - 1)) < 2 * D) :
    m ≤ (offsetSet a s D j).card := by
  have hsub : Finset.range m ⊆ offsetSet a s D j := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hfiti := hfit i hi
    have hsumi := hsum i hi
    have hbound := block_sum_bound hgap i j hfiti
    -- `2·csum ≤ … < 2D` ⟹ `csum < D`
    have hcsum : csum a (i + 1) (i + j) < D := by omega
    simp only [offsetSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hfiti, hcsum⟩
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ (offsetSet a s D j).card := Finset.card_le_card hsub

/-- **Lower bound on the block count via disjoint length-blocks.**  Summing the offset counts over
all lengths `1 ≤ j ≤ A` undercounts `smallBlocks`, since the blocks `(i+1, i+j)` are distinct across
both `i` and `j`.  This is the combinatorial half of (3.5)→(3.6): `S ≤ #smallBlocks`. -/
theorem sum_offsetSet_card_le (a : ℕ → ℕ) (s D A : ℕ) :
    ∑ j ∈ Finset.Icc 1 A, (offsetSet a s D j).card ≤ (smallBlocks a s D).card := by
  classical
  -- the image of `offsetSet j` under `i ↦ (i+1, i+j)`
  set img : ℕ → Finset (ℕ × ℕ) := fun j => (offsetSet a s D j).image (fun i => (i + 1, i + j))
    with himg
  -- card of each image = card of the offset set (injective map)
  have hcard_img : ∀ j ∈ Finset.Icc 1 A, (img j).card = (offsetSet a s D j).card := by
    intro j _
    exact Finset.card_image_of_injOn (block_of_offset_injOn a s D j)
  -- images for distinct lengths are disjoint (a block determines its length `v - u + 1`)
  have hdisj : ∀ x ∈ Finset.Icc 1 A, ∀ y ∈ Finset.Icc 1 A, x ≠ y → Disjoint (img x) (img y) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    rintro p hpx hpy
    simp only [himg, Finset.mem_image] at hpx hpy
    obtain ⟨i, _, hi⟩ := hpx
    obtain ⟨i', _, hi'⟩ := hpy
    rw [← hi'] at hi
    simp only [Prod.mk.injEq] at hi
    exact hxy (by omega)
  -- the union of images sits inside smallBlocks
  have hsub : (Finset.Icc 1 A).biUnion img ⊆ smallBlocks a s D := by
    intro p hp
    simp only [Finset.mem_biUnion] at hp
    obtain ⟨j, hjmem, hpj⟩ := hp
    rw [Finset.mem_Icc] at hjmem
    simp only [himg, Finset.mem_image] at hpj
    obtain ⟨i, hi, rfl⟩ := hpj
    exact block_of_offset_mem a s D j hjmem.1 i hi
  calc ∑ j ∈ Finset.Icc 1 A, (offsetSet a s D j).card
      = ∑ j ∈ Finset.Icc 1 A, (img j).card := (Finset.sum_congr rfl hcard_img).symm
    _ = ((Finset.Icc 1 A).biUnion img).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (smallBlocks a s D).card := Finset.card_le_card hsub
