/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Erdős #880 — restricted addition and gaps in the set of restricted sums (Burr–Erdős)

Let `A ⊆ ℕ` be an additive basis of order `k`, and let `B` be the set of integers that are a sum of
`k` or fewer **pairwise distinct** elements of `A`. Burr & Erdős asked: are the gaps `b_{n+1} − b_n`
bounded? Hegyvári, Hennecart & Plagne resolved it:

* **`k = 2`: YES** — in fact `b_{n+1} − b_n ≤ 2` for large `n` (every odd element of `A+A` is a sum of
  two *distinct* elements, so `2A` and `2×A` agree on odds, which are 2-apart). Trivial.
* **`k ≥ 3`: NO** — an explicit construction gives a basis of order `k` whose restricted-sum set has
  **arbitrarily long gaps** (`Δ = +∞`). This is the whole project (`Construction.lean`).

Source: N. Hegyvári, F. Hennecart, A. Plagne, *Answer to a question by Burr and Erdős on restricted
addition, and related results*, **Combin. Probab. Comput. 16 (2007) 747–756**, DOI
10.1017/S0963548306008224. Problem page: <https://www.erdosproblems.com/880>.

⚠️ The headline theorem is the **negative** answer for `k ≥ 3` (unbounded gaps), NOT a bounded-gap
result. Get the definitions below pinned against the paper lap 1 — this is the audit surface.
-/

namespace LeanGallery.Combinatorics.Erdos880
open scoped BigOperators
open Finset

/-- Integers that are a sum of **exactly `h` pairwise distinct** elements of `A` (the restricted
`h`-fold sumset, written `h × A` in the paper). -/
def restrictedSumset (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ T : Finset ℕ, (↑T ⊆ A) ∧ T.card = h ∧ ∑ a ∈ T, a = n}

/-- Integers that are a sum of **at most `k` (not necessarily distinct)** elements of `A` (the
ordinary "≤ k-fold" sumset — used for the basis condition). -/
def sumsetLE (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ (m : ℕ) (f : Fin m → ℕ), m ≤ k ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- The set `B` of #880: integers that are a sum of `k` or fewer pairwise distinct elements of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  ⋃ h ∈ Finset.Icc 1 k, restrictedSumset A h

/-- `A` is an additive basis of order `k`: all but finitely many naturals lie in `sumsetLE A k`. -/
def IsBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  {n : ℕ | n ∉ sumsetLE A k}.Finite

/-- `A` is a **restricted basis of order `≤ k`**: all but finitely many naturals are a sum of `≤ k`
*pairwise-distinct* elements of `A` (i.e. `restrictedSums A k` is cofinite). The **restricted order**
`ord_r(A)` of HHP07 is the least such `k` (if any). -/
def IsRestrictedBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  {n : ℕ | n ∉ restrictedSums A k}.Finite

/-- The **restricted order** `ord_r(A)` (HHP07): the least `k` such that all but finitely many naturals
are a sum of `≤ k` pairwise-distinct elements of `A` (`0` if no such `k` exists, by `Nat.sInf`). -/
noncomputable def restrictedOrder (A : Set ℕ) : ℕ :=
  sInf {k : ℕ | IsRestrictedBasisOfOrder A k}

/-- `S` has **unbounded gaps**: arbitrarily long runs of consecutive integers are missing from `S`. -/
def UnboundedGaps (S : Set ℕ) : Prop :=
  ∀ G : ℕ, ∃ m : ℕ, ∀ x : ℕ, m ≤ x → x ≤ m + G → x ∉ S

/-- `S` has **gaps eventually bounded by `C`**: beyond some `N`, every integer has a member of `S`
within `C` above it (so consecutive members are `≤ C` apart). -/
def BoundedGapsBy (S : Set ℕ) (C : ℕ) : Prop :=
  ∃ N : ℕ, ∀ x : ℕ, N ≤ x → ∃ y ∈ S, x ≤ y ∧ y ≤ x + C

/-! ### Restricted-sumset ergonomics + the `k = 2` parity argument -/

/-- Membership in `restrictedSums` from a witnessing cardinality `h ∈ [1,k]`. -/
lemma mem_restrictedSums {A : Set ℕ} {k h n : ℕ}
    (hh : h ∈ Finset.Icc 1 k) (hn : n ∈ restrictedSumset A h) :
    n ∈ restrictedSums A k := by
  rw [restrictedSums]
  exact Set.mem_iUnion₂.mpr ⟨h, hh, hn⟩

/-- A single element of `A` is a restricted sum (of order `1 ≤ k`). -/
lemma mem_restrictedSums_single {A : Set ℕ} {k a : ℕ} (hk : 1 ≤ k) (ha : a ∈ A) :
    a ∈ restrictedSums A k :=
  mem_restrictedSums (Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩)
    ⟨{a}, by simpa using ha, Finset.card_singleton a, by simp⟩

/-- An odd integer that is a sum of `≤ 2` elements of `A` is a sum of `1` or `2` *distinct*
elements: the parity argument — an odd number cannot be written `a + a`. -/
lemma odd_mem_restrictedSums_two {A : Set ℕ} {n : ℕ}
    (hodd : Odd n) (hn : n ∈ sumsetLE A 2) : n ∈ restrictedSums A 2 := by
  obtain ⟨m, f, hm, hf, hsum⟩ := hn
  rw [Nat.odd_iff] at hodd
  interval_cases m
  · -- m = 0 : sum is `0`, impossible for odd `n`
    simp at hsum
    omega
  · -- m = 1 : `n = f 0`, a single element of `A`
    rw [Fin.sum_univ_one] at hsum
    exact hsum ▸ mem_restrictedSums_single (by norm_num) (hf 0)
  · -- m = 2 : `n = f 0 + f 1`; oddness forces `f 0 ≠ f 1`
    rw [Fin.sum_univ_two] at hsum
    have hne : f 0 ≠ f 1 := by intro h; rw [h] at hsum; omega
    refine mem_restrictedSums (Finset.mem_Icc.mpr ⟨by norm_num, le_refl 2⟩)
      ⟨{f 0, f 1}, ?_, Finset.card_pair hne, ?_⟩
    · rw [Finset.coe_insert, Finset.coe_singleton]
      exact Set.insert_subset_iff.mpr ⟨hf 0, Set.singleton_subset_iff.mpr (hf 1)⟩
    · rw [Finset.sum_pair hne]; exact hsum

/-- **Erdős #880 — the `k = 2` POSITIVE answer (gaps `≤ 2`).**
If `A` is a basis of order `2` then its restricted-sum set has gaps eventually bounded by `2`. -/
theorem erdos_880_k2 (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    BoundedGapsBy (restrictedSums A 2) 2 := by
  obtain ⟨M, hM⟩ := hbasis.bddAbove
  have hbig : ∀ y, M < y → y ∈ sumsetLE A 2 := by
    intro y hy
    by_contra hmem
    exact absurd (hM hmem) (by omega)
  refine ⟨M + 1, ?_⟩
  intro x hx
  rcases Nat.even_or_odd x with he | ho
  · -- `x` even: the next odd `x+1` lies in the restricted sums
    exact ⟨x + 1, odd_mem_restrictedSums_two he.add_one (hbig _ (by omega)), by omega, by omega⟩
  · -- `x` odd: `x` itself lies in the restricted sums
    exact ⟨x, odd_mem_restrictedSums_two ho (hbig _ (by omega)), le_refl x, by omega⟩

end LeanGallery.Combinatorics.Erdos880
