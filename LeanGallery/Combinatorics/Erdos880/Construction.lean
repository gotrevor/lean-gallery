/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Basic
import LeanGallery.Combinatorics.Erdos880.Popcount

/-!
# The Hegyvári–Hennecart–Plagne construction (the `k ≥ 3` negative answer)

The explicit basis with unbounded restricted-sum gaps. Everything here is elementary: a quadratic
recurrence, intervals, and **binary representation** of `2^{h−1} − 1 = 1 + 2 + ⋯ + 2^{h−2}`.

Parameters (fix `h ≥ 3`):
* recurrence `x 0 = h`, `x (n+1) = (3·2^(h−2) − 1)·(x n)^2 + h·(x n)`;
* block `Aₙ = Finset.Icc 0 (x n)^2 ∪ {2^j·(x n)^2 : j ∈ Finset.range (h−1)}`;
* `A = {0} ∪ ⋃ₙ ((x n) + Aₙ)` (translated blocks).

Two obligations:
1. **`A` is a basis of order `h`** (`IsBasisOfOrder A h`): every integer `≤ 2^{h−1} − 2` is a sum of
   `≤ h−2` distinct powers of two from `{2⁰,…,2^{h−2}}` (binary rep), which lets `[xₙ, x_{n+1})` be
   covered by `≤ h` ordinary sums.
2. **Unbounded gaps** (`UnboundedGaps (restrictedSums A h)`): for `ℓ ≤ 2^{h−2}+h−2`,
   `max(ℓ × (xₙ + Aₙ)) ≤ (2^{h−1}+ℓ−h)·xₙ²`, so a gap of length `≥ xₙ² − (2^{h−2}−2)·xₙ → ∞` opens up
   just below `x_{n+1}`.

The crux (still elementary): the interval `[(2^{h−1}−1)xₙ² + (h−1)xₙ + 1, 2^{h−1}xₙ² − 1]` is NOT a sum
of `h−1` distinct block elements — forced by **uniqueness of the binary representation** of `2^{h−1}−1`
(pins all coefficients to 1, contradiction). No Kneser / Erdős–Rado needed here; those appear only in
the paper's non-headline auxiliaries (Prop 5, Thm 8–10), which we skip.

⚠️ Placeholder `def`s below — pin the exact block/recurrence shapes against the PDF lap 1
(`papers/hhp-2007.pdf`, free at cmls.polytechnique.fr/perso/plagne/Erdos-Burr.pdf, gitignored).
-/

namespace LeanGallery.Combinatorics.Erdos880
open scoped BigOperators
open Finset

/-- The recurrence `x 0 = h`, `x (n+1) = (3·2^(h−2) − 1)·(x n)^2 + h·(x n)`. -/
def xseq (h : ℕ) : ℕ → ℕ
  | 0 => h
  | n + 1 => (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + h * (xseq h n)

/-- The `n`-th block `Aₙ = [0, xₙ²] ∪ {2ʲ·xₙ² : 0 ≤ j ≤ h−2}`. -/
def block (h : ℕ) (n : ℕ) : Set ℕ :=
  Set.Icc 0 ((xseq h n) ^ 2) ∪ {m | ∃ j < h - 1, m = 2 ^ j * (xseq h n) ^ 2}

/-- The constructed basis `A = {0} ∪ ⋃ₙ (xₙ + Aₙ)`. -/
def constA (h : ℕ) : Set ℕ :=
  {0} ∪ ⋃ n, {m | ∃ b ∈ block h n, m = xseq h n + b}

/-! ### Growth of the recurrence `xseq`

Pure `Nat` arithmetic facts about `x 0 = h`, `x (n+1) = (3·2^{h-2}−1)·xₙ² + h·xₙ`. These feed both
the basis-covering and the unbounded-gap arguments. -/

@[simp] lemma xseq_zero (h : ℕ) : xseq h 0 = h := rfl

lemma xseq_succ (h n : ℕ) :
    xseq h (n + 1) = (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + h * (xseq h n) := rfl

/-- For `h ≥ 3` every term of the sequence is `≥ h` (in particular positive). -/
lemma le_xseq (h : ℕ) (hh : 3 ≤ h) (n : ℕ) : h ≤ xseq h n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [xseq_succ]
      have hx1 : 1 ≤ xseq h n := le_trans (by omega) ih
      calc h = h * 1 := (Nat.mul_one h).symm
        _ ≤ h * xseq h n := Nat.mul_le_mul_left h hx1
        _ ≤ (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + h * xseq h n := Nat.le_add_left _ _

lemma xseq_pos (h : ℕ) (hh : 3 ≤ h) (n : ℕ) : 0 < xseq h n :=
  lt_of_lt_of_le (by omega) (le_xseq h hh n)

/-- The sequence is strictly increasing. -/
lemma xseq_lt_succ (h : ℕ) (hh : 3 ≤ h) (n : ℕ) : xseq h n < xseq h (n + 1) := by
  rw [xseq_succ]
  have hx1 : 1 ≤ xseq h n := le_trans (by omega) (le_xseq h hh n)
  have h3 : 3 * xseq h n ≤ h * xseq h n := Nat.mul_le_mul_right _ hh
  have : xseq h n < h * xseq h n := by nlinarith [hx1, h3]
  exact lt_of_lt_of_le this (Nat.le_add_left _ _)

/-- Hence `h + n ≤ xseq h n`: the sequence climbs at least one per step from `x 0 = h`. -/
lemma add_le_xseq (h : ℕ) (hh : 3 ≤ h) (n : ℕ) : h + n ≤ xseq h n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have := xseq_lt_succ h hh n
      omega

/-- `xseq` is unbounded: for any target `T` some term exceeds it. -/
lemma exists_xseq_ge (h : ℕ) (hh : 3 ≤ h) (T : ℕ) : ∃ n, T ≤ xseq h n :=
  ⟨T, le_trans (by omega) (add_le_xseq h hh T)⟩

/-- `2 ≤ 2^{h-2}` for `h ≥ 3` (used to keep recurrence coefficients positive). -/
lemma two_le_pow (h : ℕ) (hh : 3 ≤ h) : 2 ≤ 2 ^ (h - 2) := by
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (h - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A clean subtraction-free lower bound on the successor: `x_{n+1} ≥ (2·2^{h-2}+1)·xₙ² + h·xₙ`.
(The leading coefficient `3·2^{h-2}−1 ≥ 2·2^{h-2}+1`.) -/
lemma xseq_succ_ge (h : ℕ) (hh : 3 ≤ h) (n : ℕ) :
    (2 * 2 ^ (h - 2) + 1) * (xseq h n) ^ 2 + h * (xseq h n) ≤ xseq h (n + 1) := by
  rw [xseq_succ]
  have hc := two_le_pow h hh
  gcongr
  omega

/-- The gap below `x_{n+1}` exceeds any prescribed length `G` for suitable `n`. Concretely
`2^{h-1}·xₙ² + 2h·xₙ + G < x_{n+1}`, so `[2^{h-1}xₙ²+2h·xₙ, x_{n+1})` is a run of `> G` integers. -/
lemma gap_size (h : ℕ) (hh : 3 ≤ h) (G : ℕ) :
    ∃ n, 2 ^ (h - 1) * (xseq h n) ^ 2 + 2 * h * (xseq h n) + G < xseq h (n + 1) := by
  obtain ⟨n, hn⟩ := exists_xseq_ge h hh (G + h + 1)
  refine ⟨n, ?_⟩
  have h21 : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
    rw [show h - 1 = (h - 2) + 1 by omega, pow_succ]; ring
  have hge := xseq_succ_ge h hh n
  have hbig : h * xseq h n + G < (xseq h n) ^ 2 := by nlinarith [hn]
  rw [h21]
  nlinarith [hge, hbig]

/-! ### Binary representation (basis-covering core input)

Every `n < 2^k` is a sum of distinct powers `2^0,…,2^{k-1}`. Proof obtained via the Aristotle
auto-formalizer (job `6a32c9a8`), verified in-kernel (`#print axioms` = `[propext,
Classical.choice, Quot.sound]`) and ported here. This is the elementary fact behind "any integer
`≤ 2^{h-1}−2` is a sum of `≤ h−2` distinct powers of two" (HHP07, p. 4). -/
theorem binary_subset_sum (k : ℕ) :
    ∀ n : ℕ, n < 2 ^ k →
      ∃ S : Finset ℕ, S ⊆ Finset.range k ∧ ∑ j ∈ S, 2 ^ j = n := by
  induction' k with k ih
  · aesop
  · intro n hn; by_cases h : n < 2 ^ k <;> simp_all +decide [pow_succ']
    · exact Exists.elim (ih n h) fun S hS =>
        ⟨S, Finset.Subset.trans hS.1 (Finset.range_mono (Nat.le_succ _)), hS.2⟩
    · obtain ⟨S, hS₁, hS₂⟩ := ih (n - 2 ^ k) (by rw [tsub_lt_iff_left h]; linarith)
      use S ∪ {k}; simp_all +decide [Finset.subset_iff]
      grind

/-! ### `sumsetLE` constructors and block/`constA` membership -/

/-- The empty sum: `0` is a sum of `≤ k` elements (vacuously). -/
lemma zero_mem_sumsetLE {A : Set ℕ} (k : ℕ) : (0 : ℕ) ∈ sumsetLE A k :=
  ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, by simp⟩

/-- A single element of `A` is a sum of `≤ k` elements (for `k ≥ 1`). -/
lemma mem_sumsetLE_single {A : Set ℕ} {k a : ℕ} (hk : 1 ≤ k) (ha : a ∈ A) :
    a ∈ sumsetLE A k :=
  ⟨1, fun _ => a, hk, fun _ => ha, by simp⟩

/-- Concatenating witnesses: a sum of `≤ k₁` and a sum of `≤ k₂` give a sum of `≤ k₁+k₂`. -/
lemma mem_sumsetLE_add {A : Set ℕ} {k₁ k₂ z₁ z₂ : ℕ}
    (h1 : z₁ ∈ sumsetLE A k₁) (h2 : z₂ ∈ sumsetLE A k₂) :
    z₁ + z₂ ∈ sumsetLE A (k₁ + k₂) := by
  obtain ⟨m₁, f₁, hm₁, hf₁, hs₁⟩ := h1
  obtain ⟨m₂, f₂, hm₂, hf₂, hs₂⟩ := h2
  refine ⟨m₁ + m₂, Fin.append f₁ f₂, by omega, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hf₁ j
    · rw [Fin.append_right]; exact hf₂ j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hs₁, hs₂]

/-- Any list of `≤ k` elements of `A` realises its sum as a member of `sumsetLE A k`. -/
lemma mem_sumsetLE_of_list {A : Set ℕ} {k : ℕ} (L : List ℕ)
    (hlen : L.length ≤ k) (hmem : ∀ a ∈ L, a ∈ A) : L.sum ∈ sumsetLE A k := by
  induction L generalizing k with
  | nil => simpa using zero_mem_sumsetLE k
  | cons a t ih =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [List.length_cons] at hlen; omega⟩
      have ht : t.length ≤ k' := by simp only [List.length_cons] at hlen; omega
      have hadd : a + t.sum ∈ sumsetLE A (1 + k') :=
        mem_sumsetLE_add (mem_sumsetLE_single (le_refl 1) (hmem a (by simp)))
          (ih ht (fun b hb => hmem b (List.mem_cons_of_mem a hb)))
      rw [List.sum_cons]
      rwa [Nat.add_comm 1 k'] at hadd

/-- An element `≤ xₙ²` lies in the interval part of the `n`-th block. -/
lemma mem_block_interval (h n b : ℕ) (hb : b ≤ (xseq h n) ^ 2) : b ∈ block h n :=
  Set.mem_union_left _ ⟨Nat.zero_le _, hb⟩

/-- A power `2ʲ·xₙ²` with `j < h-1` lies in the power part of the `n`-th block. -/
lemma mem_block_pow (h n j : ℕ) (hj : j < h - 1) : 2 ^ j * (xseq h n) ^ 2 ∈ block h n :=
  Set.mem_union_right _ ⟨j, hj, rfl⟩

/-- Every translate `xₙ + b` of a block element is in `constA h`. -/
lemma mem_constA_block (h n b : ℕ) (hb : b ∈ block h n) : xseq h n + b ∈ constA h :=
  Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨n, b, hb, rfl⟩)

/-! ### Block localization (gap-core structure)

A translated block `xᵢ + Aᵢ` lives inside `[xᵢ, x_{i+1})`; the blocks are disjoint. So any element
of `constA h` in `[xₙ, x_{n+1})` is forced into the `n`-th block. -/

/-- `xseq` is monotone. -/
lemma xseq_mono (h : ℕ) (hh : 3 ≤ h) : Monotone (xseq h) :=
  (strictMono_nat_of_lt_succ (fun n => xseq_lt_succ h hh n)).monotone

/-- Largest element of a block: every `b ∈ block h i` satisfies `b ≤ 2^{h-2}·xᵢ²`. -/
lemma block_le (h i b : ℕ) (hh : 3 ≤ h) (hb : b ∈ block h i) :
    b ≤ 2 ^ (h - 2) * (xseq h i) ^ 2 := by
  have h1 : (1 : ℕ) ≤ 2 ^ (h - 2) := Nat.one_le_pow _ _ (by norm_num)
  rcases hb with hb | hb
  · have hb2 : b ≤ (xseq h i) ^ 2 := (Set.mem_Icc.mp hb).2
    calc b ≤ (xseq h i) ^ 2 := hb2
      _ = 1 * (xseq h i) ^ 2 := (one_mul _).symm
      _ ≤ 2 ^ (h - 2) * (xseq h i) ^ 2 := mul_le_mul_left h1 _
  · obtain ⟨j, hj, rfl⟩ := hb
    exact mul_le_mul_left (Nat.pow_le_pow_right (by norm_num) (by omega)) _

/-- A translated block element stays below the next term: `xᵢ + b < x_{i+1}` for `b ∈ block h i`. -/
lemma block_translate_lt_succ (h i b : ℕ) (hh : 3 ≤ h) (hb : b ∈ block h i) :
    xseq h i + b < xseq h (i + 1) := by
  have hble := block_le h i b hh hb
  have hge := xseq_succ_ge h hh i
  have hx := xseq_pos h hh i
  have hc2 := two_le_pow h hh
  nlinarith [hble, hge, hx, hc2]

/-- Localization: an element of `constA h` in `[xₙ, x_{n+1})` is in the `n`-th translated block, so
its offset `a − xₙ` is a genuine block element. -/
lemma mem_constA_localize (h n a : ℕ) (hh : 3 ≤ h) (ha : a ∈ constA h)
    (hlo : xseq h n ≤ a) (hhi : a < xseq h (n + 1)) :
    a - xseq h n ∈ block h n := by
  rw [constA, Set.mem_union] at ha
  rcases ha with ha | ha
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    exact absurd hlo (by have := le_xseq h hh n; omega)
  · rw [Set.mem_iUnion] at ha
    obtain ⟨i, b, hb, rfl⟩ := ha
    have hmono := xseq_mono h hh
    have hi : i = n := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 : xseq h i + b < xseq h (i + 1) := block_translate_lt_succ h i b hh hb
        have h2 : xseq h (i + 1) ≤ xseq h n := hmono (by omega)
        omega
      · have h3 : xseq h (n + 1) ≤ xseq h i := hmono (by omega)
        omega
    subst hi
    simpa using hb

/-! ### Block covering via binary representation

The technical heart of the basis direction: every `z < (3·2^{h-2}−1)·xₙ²` is a sum of `≤ h`
block elements (HHP07 p. 4). Built from the binary representation [[binary_subset_sum]]. -/

/-- `∑_{j<n} 2ʲ = 2ⁿ − 1`. -/
lemma sum_range_two_pow (n : ℕ) : ∑ j ∈ Finset.range n, 2 ^ j = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; omega

/-- Summing a constant shift over a list: `∑ (x + bᵢ) = |L|·x + ∑ bᵢ`. -/
lemma sum_map_add_const (x : ℕ) (M : List ℕ) :
    (M.map (fun b => x + b)).sum = M.length * x + M.sum := by
  induction M with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring

/-- Block-covering core: every `w < (2·2^{h-2}−1)·xₙ²` is a sum of `≤ h−1` block elements.
(Write `w = q·xₙ² + r` with `r < xₙ²` an interval element and `q ≤ 2^{h-1}−2` a sum of `≤ h−2`
distinct powers of two by [[binary_subset_sum]].) -/
lemma block_list_core (h : ℕ) (hh : 3 ≤ h) (n w : ℕ)
    (hw : w < (2 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2) :
    ∃ M : List ℕ, M.length ≤ h - 1 ∧ (∀ a ∈ M, a ∈ block h n) ∧ M.sum = w := by
  have hx : 0 < xseq h n := xseq_pos h hh n
  have hx2 : 0 < (xseq h n) ^ 2 := by positivity
  have hc2 : 2 ≤ 2 ^ (h - 2) := two_le_pow h hh
  have h21 : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
    rw [show h - 1 = (h - 2) + 1 by omega, pow_succ]; ring
  -- w = q·x² + r
  have hdm := Nat.div_add_mod w ((xseq h n) ^ 2)
  set q := w / (xseq h n) ^ 2 with hqdef
  set r := w % (xseq h n) ^ 2 with hrdef
  have hr : r < (xseq h n) ^ 2 := Nat.mod_lt w hx2
  have hwqr : w = q * (xseq h n) ^ 2 + r := by rw [Nat.mul_comm] at hdm; omega
  have hqlt : q < 2 * 2 ^ (h - 2) - 1 := by
    rw [hqdef]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hw)
  have hq : q < 2 ^ (h - 1) := by rw [h21]; omega
  obtain ⟨S, hSsub, hSsum⟩ := binary_subset_sum (h - 1) q hq
  have hScard : S.card ≤ h - 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have hSeq : S = Finset.range (h - 1) :=
      Finset.eq_of_subset_of_card_le hSsub (by rw [Finset.card_range]; omega)
    rw [hSeq, sum_range_two_pow] at hSsum
    omega
  -- build the list: powers (from S) ++ the remainder r
  refine ⟨(S.toList.map (fun j => 2 ^ j * (xseq h n) ^ 2)) ++ [r], ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_map, List.length_singleton, Finset.length_toList]
    omega
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · rw [List.mem_map] at ha
      obtain ⟨j, hjS, rfl⟩ := ha
      exact mem_block_pow h n j (Finset.mem_range.mp (hSsub (Finset.mem_toList.mp hjS)))
    · rw [List.mem_singleton] at ha
      subst ha
      exact mem_block_interval h n r (le_of_lt hr)
  · rw [List.sum_append, List.sum_cons, List.sum_nil, Finset.sum_map_toList,
        ← Finset.sum_mul, hSsum]
    omega

/-- Block covering: every `z < (3·2^{h-2}−1)·xₙ²` is a sum of `≤ h` block elements. -/
lemma block_list (h : ℕ) (hh : 3 ≤ h) (n z : ℕ)
    (hz : z < (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2) :
    ∃ M : List ℕ, M.length ≤ h ∧ (∀ a ∈ M, a ∈ block h n) ∧ M.sum = z := by
  have hc2 : 2 ≤ 2 ^ (h - 2) := two_le_pow h hh
  have expand : (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2
      = (2 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + 2 ^ (h - 2) * (xseq h n) ^ 2 := by
    rw [show 3 * 2 ^ (h - 2) - 1 = (2 * 2 ^ (h - 2) - 1) + 2 ^ (h - 2) by omega, Nat.add_mul]
  by_cases hsplit : z < (2 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2
  · obtain ⟨M, hlen, hmem, hsum⟩ := block_list_core h hh n z hsplit
    exact ⟨M, by omega, hmem, hsum⟩
  · rw [not_lt] at hsplit
    have hle' : 2 ^ (h - 2) * (xseq h n) ^ 2 ≤ (2 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 := by
      gcongr; omega
    have hle : 2 ^ (h - 2) * (xseq h n) ^ 2 ≤ z := le_trans hle' hsplit
    have hw : z - 2 ^ (h - 2) * (xseq h n) ^ 2 < (2 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 := by
      omega
    obtain ⟨M, hlen, hmem, hsum⟩ := block_list_core h hh n _ hw
    refine ⟨(2 ^ (h - 2) * (xseq h n) ^ 2) :: M, by simp only [List.length_cons]; omega, ?_, ?_⟩
    · intro a ha
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact mem_block_pow h n (h - 2) (by omega)
      · exact hmem a ha
    · rw [List.sum_cons, hsum]; omega

/-- **Sum of distinct powers of two, `k` largest** (gap-core input). A subset `J ⊆ {0,…,m−1}` of
size `k` has `∑ 2ʲ ≤ 2ᵐ − 2^{m−k}`, the sum of the `k` largest available powers (subtraction-free
form). Obtained via Aristotle (job `a5fd78a8`), verified in-kernel (axioms clean) and ported. -/
theorem power_subset_sum_le (m : ℕ) :
    ∀ J : Finset ℕ, J ⊆ Finset.range m →
      (∑ j ∈ J, 2 ^ j) + 2 ^ (m - J.card) ≤ 2 ^ m := by
  induction' m with m ih <;> simp +arith +decide [pow_succ'] at *
  intro J hJ
  by_cases hm : m ∈ J
  · rw [← Finset.sum_erase_add _ _ hm]
    grind +revert
  · rw [Nat.succ_sub (show J.card ≤ m from le_trans (Finset.card_le_card
      (show J ⊆ Finset.range m from fun x hx => Finset.mem_range.mpr
        (Nat.lt_of_le_of_ne (Finset.mem_range_succ_iff.mp (hJ hx)) (by aesop)))) (by simp))]
    grind

/-! ### The two combinatorial cores

`erdos_880_unbounded` reduces (via the plumbing below) to exactly these two statements about the
explicit construction. Both are elementary (binary representation + block arithmetic) — the genuine
mathematical content of HHP07 Theorem 1(ii). They are stated precisely here and discharged
incrementally. -/

/-- **Basis-covering core.** Every integer in a block `[xₙ, x_{n+1})` is a sum of `≤ h` elements of
`constA h`. (HHP07 p. 4: `[xₙ, x_{n+1}) ⊆ h(xₙ+Aₙ) ∪ {0} ⊆ hA`, using that any integer
`< (2^{h-1}−1)xₙ²` is a sum of `h−1` elements of `Aₙ` via the binary representation
[[binary_subset_sum]].) -/
lemma basis_covering (h : ℕ) (hh : 3 ≤ h) (n y : ℕ)
    (hlo : xseq h n ≤ y) (hhi : y < xseq h (n + 1)) :
    y ∈ sumsetLE (constA h) h := by
  have hx_ge : h ≤ xseq h n := le_xseq h hh n
  by_cases hcase : y ≤ h * xseq h n
  · -- regime A: `[xₙ, h·xₙ]` — a single element `xₙ + b` of the interval part of the block
    obtain ⟨b, rfl⟩ : ∃ b, y = xseq h n + b := ⟨y - xseq h n, by omega⟩
    have hhx : h * xseq h n ≤ xseq h n * xseq h n := mul_le_mul_left hx_ge (xseq h n)
    have hb : b ≤ (xseq h n) ^ 2 := by rw [pow_two]; omega
    exact mem_sumsetLE_single (by omega) (mem_constA_block h n b (mem_block_interval h n b hb))
  · -- regime B: `[h·xₙ, x_{n+1})` — `h` elements `xₙ + bᵢ` covering `y = h·xₙ + z` via `block_list`
    rw [not_le] at hcase
    obtain ⟨z, rfl⟩ : ∃ z, y = h * xseq h n + z := ⟨y - h * xseq h n, by omega⟩
    have hsucc : xseq h (n + 1) = (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + h * (xseq h n) :=
      xseq_succ h n
    have hzbound : z < (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 := by omega
    obtain ⟨M, hMlen, hMmem, hMsum⟩ := block_list h hh n z hzbound
    have hmul : M.length * xseq h n + (h - M.length) * xseq h n = h * xseq h n := by
      rw [← Nat.add_mul]; congr 1; omega
    have hLsum : (M.map (fun b => xseq h n + b)
        ++ List.replicate (h - M.length) (xseq h n)).sum = h * xseq h n + z := by
      rw [List.sum_append, sum_map_add_const, List.sum_replicate, smul_eq_mul, hMsum]
      omega
    rw [← hLsum]
    apply mem_sumsetLE_of_list
    · rw [List.length_append, List.length_map, List.length_replicate]; omega
    · intro a ha
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · rw [List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact mem_constA_block h n b (hMmem b hb)
      · rw [List.mem_replicate] at ha
        obtain ⟨-, rfl⟩ := ha
        simpa using mem_constA_block h n 0 (mem_block_interval h n 0 (Nat.zero_le _))

/-- **Block sum bound (general slack `c`).** A finite set `T` of naturals, each `≤ X` or a power
`2ʲ·X` with `j ≤ m`, of size `≤ m+1+c`, sums to `≤ (2^{m+1}−1+c)·X` (the `m+1` distinct powers total
`(2^{m+1}−1)X`, then `c` further interval elements each `≤ X`). Proof: split `T` into powers `> X` (a
set of distinct powers `2ʲ·X`, exponent set `J ⊆ {0,…,m}`, bounded via [[power_subset_sum_le]] by
`2^{m+1}−2^{m+1−|J|}`) and elements `≤ X` (at most `m+1+c−|J|` of them); the trade-off closes by
`t < 2ᵗ` (`Nat.lt_two_pow_self`). The `c = 1` case is [[block_sum_bound]] (used by the order-`h` gap
core); the `c = 2^{h-2}−1` case feeds the `L`-fold gap core for HHP07 Theorem 3. -/
theorem block_sum_bound_gen (X m c : ℕ) (hX : 0 < X) (T : Finset ℕ)
    (hcard : T.card ≤ m + 1 + c)
    (hmem : ∀ a ∈ T, a ≤ X ∨ ∃ j ≤ m, a = 2 ^ j * X) :
    ∑ a ∈ T, a ≤ (2 ^ (m + 1) - 1 + c) * X := by
  classical
  -- split into "big" (a power `> X`) and "small" (`≤ X`) elements
  set Big := T.filter (fun a => X < a) with hBigdef
  set Sm := T.filter (fun a => ¬ X < a) with hSmdef
  have hpart : ∑ a ∈ T, a = ∑ a ∈ Big, a + ∑ a ∈ Sm, a := by
    rw [hBigdef, hSmdef]; exact (Finset.sum_filter_add_sum_filter_not T _ _).symm
  -- each big element is a power `2ʲ·X` with `j ≤ m`
  have hbigpow : ∀ a ∈ Big, ∃ j ≤ m, a = 2 ^ j * X := by
    intro a ha
    rw [hBigdef, Finset.mem_filter] at ha
    rcases hmem a ha.1 with h | h
    · omega
    · exact h
  -- the exponent of a big element, recovered as `log₂ (a / X)`
  set e : ℕ → ℕ := fun a => Nat.log 2 (a / X) with hedef
  have hexp : ∀ a ∈ Big, e a ≤ m ∧ a = 2 ^ (e a) * X := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := hbigpow a ha
    have hdiv : 2 ^ j * X / X = 2 ^ j := by
      rw [Nat.mul_div_cancel _ hX]
    have hlog : e (2 ^ j * X) = j := by rw [hedef]; simp only [hdiv]; exact Nat.log_pow (by norm_num) j
    rw [hlog]; exact ⟨hj, rfl⟩
  have hinj : ∀ a ∈ Big, ∀ b ∈ Big, e a = e b → a = b := by
    intro a ha b hb hab
    rw [(hexp a ha).2, (hexp b hb).2, hab]
  set J := Big.image e with hJdef
  have hJsub : J ⊆ Finset.range (m + 1) := by
    intro j hj
    rw [hJdef, Finset.mem_image] at hj
    obtain ⟨a, ha, rfl⟩ := hj
    rw [Finset.mem_range]; have := (hexp a ha).1; omega
  have hJcard : J.card = Big.card := by
    rw [hJdef]; exact Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb)
  have hBigsum : ∑ a ∈ Big, a = (∑ j ∈ J, 2 ^ j) * X := by
    rw [Finset.sum_mul, hJdef, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun a ha => (hexp a ha).2)
  have hpow := power_subset_sum_le (m + 1) J hJsub
  have hJle : J.card ≤ m + 1 := le_trans (Finset.card_le_card hJsub) (by rw [Finset.card_range])
  have hlt2 := Nat.lt_two_pow_self (n := m + 1 - J.card)
  -- small elements: each `≤ X`
  have hSmbound : ∑ a ∈ Sm, a ≤ Sm.card * X := by
    have hb : ∀ a ∈ Sm, a ≤ X := by
      intro a ha; rw [hSmdef, Finset.mem_filter] at ha; omega
    calc ∑ a ∈ Sm, a ≤ Sm.card • X := Finset.sum_le_card_nsmul Sm _ _ hb
      _ = Sm.card * X := smul_eq_mul _ _
  have hcardsum : Big.card + Sm.card = T.card := by
    rw [hBigdef, hSmdef]; exact Finset.card_filter_add_card_filter_not _
  have hSmcard : Sm.card ≤ m + 1 + c - J.card := by rw [hJcard]; omega
  have hfinal : (∑ j ∈ J, 2 ^ j) + Sm.card ≤ 2 ^ (m + 1) - 1 + c := by omega
  calc ∑ a ∈ T, a = ∑ a ∈ Big, a + ∑ a ∈ Sm, a := hpart
    _ ≤ (∑ j ∈ J, 2 ^ j) * X + Sm.card * X := by rw [hBigsum]; exact Nat.add_le_add_left hSmbound _
    _ = ((∑ j ∈ J, 2 ^ j) + Sm.card) * X := by rw [Nat.add_mul]
    _ ≤ (2 ^ (m + 1) - 1 + c) * X := mul_le_mul_left hfinal _

/-- **Block sum bound** (`c = 1` specialization of [[block_sum_bound_gen]]). A finite set `T` of
naturals, each `≤ X` or a power `2ʲ·X` with `j ≤ m`, of size `≤ m+2`, sums to `≤ 2^{m+1}·X`. -/
theorem block_sum_bound (X m : ℕ) (hX : 0 < X) (T : Finset ℕ)
    (hcard : T.card ≤ m + 2)
    (hmem : ∀ a ∈ T, a ≤ X ∨ ∃ j ≤ m, a = 2 ^ j * X) :
    ∑ a ∈ T, a ≤ 2 ^ (m + 1) * X := by
  have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have h := block_sum_bound_gen X m 1 hX T (by omega) hmem
  rwa [show 2 ^ (m + 1) - 1 + 1 = 2 ^ (m + 1) by omega] at h

/-- **Gap core (general fold count `L`).** Any restricted sum of `≤ L` distinct elements of
`constA h` that is below `x_{n+1}` is in fact below `(2^{h-1}−1+(L−(h−1)))·xₙ² + 2L·xₙ`. (HHP07 p. 5:
a sum `< x_{n+1}` uses only elements of blocks `≤ n`; the block-`n` part of any `≤ L` distinct elements
sums to `≤ (2^{h-1}−1+(L−(h−1)))xₙ²` by the slack-`(L−(h−1))` bound [[block_sum_bound_gen]], and the
lower blocks contribute `< L·xₙ`.) The `L = h` case is [[gap_core]]; `L = 2^{h-2}+h-2` drives the
quantitative Theorem 3 bound. -/
lemma gap_core_gen (h : ℕ) (hh : 3 ≤ h) (L n u : ℕ) (hL : h - 1 ≤ L)
    (hu : u ∈ restrictedSums (constA h) L) (hlt : u < xseq h (n + 1)) :
    u < (2 ^ (h - 1) - 1 + (L - (h - 1))) * (xseq h n) ^ 2 + 2 * L * (xseq h n) := by
  rw [restrictedSums, Set.mem_iUnion₂] at hu
  obtain ⟨j, hj, T, hTsub, hTcard, hTsum⟩ := hu
  rw [Finset.mem_Icc] at hj
  have hTle : T.card ≤ L := by omega
  have hele : ∀ a ∈ T, a < xseq h (n + 1) := by
    intro a ha
    have hax : a ≤ ∑ b ∈ T, b := Finset.single_le_sum (fun i _ => Nat.zero_le i) ha
    omega
  -- partition `T` into the block-`n` elements and the lower ones
  set Tn := T.filter (fun a => xseq h n ≤ a) with hTndef
  set Tlo := T.filter (fun a => ¬ xseq h n ≤ a) with hTlodef
  have hTncard : Tn.card ≤ L := le_trans (Finset.card_filter_le _ _) hTle
  have hpart : ∑ a ∈ T, a = ∑ a ∈ Tn, a + ∑ a ∈ Tlo, a := by
    rw [hTndef, hTlodef]; exact (Finset.sum_filter_add_sum_filter_not T _ _).symm
  -- lower blocks: each element `< xₙ`
  have hlo_bound : ∑ a ∈ Tlo, a ≤ L * (xseq h n - 1) := by
    have hb : ∀ a ∈ Tlo, a ≤ xseq h n - 1 := by
      intro a ha; rw [hTlodef, Finset.mem_filter] at ha; omega
    calc ∑ a ∈ Tlo, a ≤ Tlo.card • (xseq h n - 1) := Finset.sum_le_card_nsmul Tlo _ _ hb
      _ = Tlo.card * (xseq h n - 1) := smul_eq_mul _ _
      _ ≤ L * (xseq h n - 1) :=
          mul_le_mul_left (le_trans (Finset.card_filter_le _ _) hTle) _
  -- block `n`: offsets form a set of block elements, bounded by `block_sum_bound_gen`
  set B := Tn.image (fun a => a - xseq h n) with hBdef
  have hinj : ∀ a ∈ Tn, ∀ b ∈ Tn, a - xseq h n = b - xseq h n → a = b := by
    intro a ha b hb hab; rw [hTndef, Finset.mem_filter] at ha hb; omega
  have hBcard : B.card = Tn.card := by
    rw [hBdef]; exact Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)
  have hBmem : ∀ b ∈ B, b ≤ (xseq h n) ^ 2 ∨ ∃ jj ≤ h - 2, b = 2 ^ jj * (xseq h n) ^ 2 := by
    intro b hb
    rw [hBdef, Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [hTndef, Finset.mem_filter] at ha
    have hablock : a - xseq h n ∈ block h n :=
      mem_constA_localize h n a hh (hTsub ha.1) ha.2 (hele a ha.1)
    rcases hablock with hbi | hbp
    · left; exact (Set.mem_Icc.mp hbi).2
    · right; obtain ⟨jj, hjj, hbeq⟩ := hbp; exact ⟨jj, by omega, hbeq⟩
  have hTn_eq : ∑ a ∈ Tn, a = Tn.card * xseq h n + ∑ b ∈ B, b := by
    calc ∑ a ∈ Tn, a
        = ∑ a ∈ Tn, (xseq h n + (a - xseq h n)) := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          rw [hTndef, Finset.mem_filter] at ha; omega
      _ = ∑ _a ∈ Tn, xseq h n + ∑ a ∈ Tn, (a - xseq h n) := Finset.sum_add_distrib
      _ = Tn.card * xseq h n + ∑ a ∈ Tn, (a - xseq h n) := by rw [Finset.sum_const, smul_eq_mul]
      _ = Tn.card * xseq h n + ∑ b ∈ B, b := by rw [hBdef, Finset.sum_image hinj]
  have hBsum : ∑ b ∈ B, b ≤ (2 ^ (h - 1) - 1 + (L - (h - 1))) * (xseq h n) ^ 2 := by
    have hBcle : B.card ≤ (h - 2) + 1 + (L - (h - 1)) := by rw [hBcard]; omega
    have hbb := block_sum_bound_gen ((xseq h n) ^ 2) (h - 2) (L - (h - 1))
      (pow_pos (xseq_pos h hh n) 2) B hBcle hBmem
    rwa [show (h - 2) + 1 = h - 1 by omega] at hbb
  -- assemble
  have hcx : Tn.card * xseq h n ≤ L * xseq h n := mul_le_mul_left hTncard _
  have hx1 : 1 ≤ xseq h n := le_trans (by omega) (le_xseq h hh n)
  have hMA : L * (xseq h n - 1) + L = L * xseq h n := by
    conv_rhs => rw [← Nat.sub_add_cancel hx1]
    ring
  have h2x : 2 * L * xseq h n = L * xseq h n + L * xseq h n := by ring
  rw [← hTsum, hpart, hTn_eq]
  omega

/-- **Gap core** (`L = h` specialization of [[gap_core_gen]]). Any restricted sum of `≤ h` distinct
elements of `constA h` that is below `x_{n+1}` is below `2^{h-1}·xₙ² + 2h·xₙ`. -/
lemma gap_core (h : ℕ) (hh : 3 ≤ h) (n u : ℕ)
    (hu : u ∈ restrictedSums (constA h) h) (hlt : u < xseq h (n + 1)) :
    u < 2 ^ (h - 1) * (xseq h n) ^ 2 + 2 * h * (xseq h n) := by
  have hpos : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
  have hgen := gap_core_gen h hh h n u (by omega) hu hlt
  rwa [show 2 ^ (h - 1) - 1 + (h - (h - 1)) = 2 ^ (h - 1) by omega] at hgen

/-! ### Plumbing: the two cores imply the headline -/

/-- Locate the block `[xₙ, x_{n+1})` containing a given `y ≥ h = x₀`. -/
lemma find_block (h : ℕ) (hh : 3 ≤ h) (y : ℕ) (hy : h ≤ y) :
    ∃ n, xseq h n ≤ y ∧ y < xseq h (n + 1) := by
  have hex : ∃ n, y < xseq h n := by
    obtain ⟨n, hn⟩ := exists_xseq_ge h hh (y + 1); exact ⟨n, by omega⟩
  classical
  have hspec : y < xseq h (Nat.find hex) := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0; rw [h0, xseq_zero] at hspec; omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  refine ⟨m, ?_, ?_⟩
  · have hmin : ¬ (y < xseq h m) := Nat.find_min hex (by omega)
    omega
  · rw [hm] at hspec; exact hspec

/-- `constA h` is an additive basis of order `h`: all `y ≥ h` are covered, so the complement is
contained in `[0, h)` and finite. -/
lemma constA_isBasis (h : ℕ) (hh : 3 ≤ h) : IsBasisOfOrder (constA h) h := by
  apply Set.Finite.subset (Set.finite_Iio h)
  intro y hy
  rw [Set.mem_Iio]
  by_contra hlt
  have hle : h ≤ y := Nat.le_of_not_lt hlt
  obtain ⟨n, hn1, hn2⟩ := find_block h hh y hle
  exact hy (basis_covering h hh n y hn1 hn2)

/-- The constructed basis `constA h` is **infinite**: it contains the strictly increasing sequence
`(xseq h n)ₙ` (each `xseq h n = xseq h n + 0` lies in the block via `0 ∈ block h n`). Needed to turn
`UnboundedGaps (restrictedSums …)` into the faithful `Δ(…) = +∞` (the empty set has unbounded gaps
vacuously, so infinitude is what makes `Δ` non-degenerate). -/
lemma constA_infinite (h : ℕ) (hh : 3 ≤ h) : (constA h).Infinite := by
  have hmem : ∀ n, xseq h n ∈ constA h := by
    intro n
    have := mem_constA_block h n 0 (mem_block_interval h n 0 (Nat.zero_le _))
    simpa using this
  have hinj : Function.Injective (xseq h) :=
    (strictMono_nat_of_lt_succ (fun n => xseq_lt_succ h hh n)).injective
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hmem n)

/-- **Gap localization (quantitative).** Every integer in the half-open interval
`[2^{h-1}·xₙ² + 2h·xₙ, x_{n+1})` is missing from the restricted-sum set: this pins down *where* the
gaps live and that the entire interval is empty. Its length
`x_{n+1} − (2^{h-1}xₙ²+2h·xₙ) = (2^{h-2}−1)xₙ² − h·xₙ` grows super-exponentially in `n`, so this is a
localized sharpening of `constA_unboundedGaps`. -/
lemma constA_gap_interval (h n : ℕ) (hh : 3 ≤ h) {x : ℕ}
    (hlo : 2 ^ (h - 1) * (xseq h n) ^ 2 + 2 * h * (xseq h n) ≤ x)
    (hhi : x < xseq h (n + 1)) :
    x ∉ restrictedSums (constA h) h :=
  fun hxS => absurd (gap_core h hh n x hxS hhi) (by omega)

/-- The restricted-sum set of `constA h` has unbounded gaps: by [[gap_size]] the localized gap
`[2^{h-1}xₙ²+2h·xₙ, x_{n+1})` of [[constA_gap_interval]] exceeds any prescribed length. -/
lemma constA_unboundedGaps (h : ℕ) (hh : 3 ≤ h) :
    UnboundedGaps (restrictedSums (constA h) h) := by
  intro G
  obtain ⟨n, hgap⟩ := gap_size h hh G
  refine ⟨2 ^ (h - 1) * (xseq h n) ^ 2 + 2 * h * (xseq h n), ?_⟩
  intro x hxm hxG hxS
  exact constA_gap_interval h n hh hxm (lt_of_le_of_lt hxG hgap) hxS

/-- **Erdős #880 — headline (the `k ≥ 3` NEGATIVE answer).**
For every order `h ≥ 3` there is a basis `A` of order `h` whose set of restricted sums has unbounded
gaps. Hence the Burr–Erdős boundedness fails for `k ≥ 3` (HHP07, Theorem 1(ii)). -/
theorem erdos_880_unbounded (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ UnboundedGaps (restrictedSums A h) :=
  ⟨constA h, constA_isBasis h hh, constA_unboundedGaps h hh⟩

/-! ### Quantitative strengthening: HHP07 Theorem 3 (`k(h) ≥ 2^{h-2}+h−1`)

The very same construction gives more than #880 asks. The order-`h` gap argument above only used
`≤ h` folds, but the *block-`n` sum bound* keeps the gap open for far more folds: for every
`l ≤ L := 2^{h-2}+h−2`, the `l`-fold restricted sumset `l × A` still has unbounded gaps. Concretely a
sum of `≤ L` distinct elements below `x_{n+1}` is bounded by `(3·2^{h-2}−2)xₙ² + 2L·xₙ`
([[gap_core_gen]]), leaving a gap `[(3·2^{h-2}−2)xₙ²+2L·xₙ, x_{n+1})` of length `≥ xₙ² − (2L−h)xₙ → ∞`.

In HHP07's language: for this single basis `A`, `min{k : Δ(k × A) finite} ≥ 2^{h-2}+h−1`, which is
exactly the witness establishing the lower bound `k(h) ≥ 2^{h-2}+h−1` of Theorem 3. (Note `k(h)`'s
*finiteness* is HHP07 Conjecture 2, still **open** — so the faithful statement is this witness form,
not a claim about a `max` over all bases that may not exist.)

⚠️ Earlier project notes claimed Theorem 3 "needs Kneser / Erdős–Rado". That is incorrect: the proof
(HHP07 p. 5) is the elementary construction below — no Kneser anywhere. -/

/-- Gaps are *monotone* under shrinking the set: a subset of a set with unbounded gaps still has
unbounded gaps (an empty interval for the superset is empty for the subset). -/
lemma UnboundedGaps_mono {S S' : Set ℕ} (hsub : S ⊆ S') (hS' : UnboundedGaps S') :
    UnboundedGaps S := by
  intro G
  obtain ⟨m, hm⟩ := hS' G
  exact ⟨m, fun x hx1 hx2 hxS => hm x hx1 hx2 (hsub hxS)⟩

/-- The exact `l`-fold restricted sumset embeds in the `≤ k`-fold restricted sums for `1 ≤ l ≤ k`. -/
lemma restrictedSumset_subset_restrictedSums {A : Set ℕ} {l k : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ k) :
    restrictedSumset A l ⊆ restrictedSums A k :=
  fun _ hn => mem_restrictedSums (Finset.mem_Icc.mpr ⟨h1, h2⟩) hn

/-- **Gap size for `L = 2^{h-2}+h−2` folds.** For any prescribed `G` some block `n` has
`(3·2^{h-2}−2)xₙ² + 2L·xₙ + G < x_{n+1}` (the left coefficient is one *less* than `x_{n+1}`'s leading
coefficient `3·2^{h-2}−1`, so the surplus quadratic `xₙ²` swallows any `G`). -/
lemma gap_size_L (h : ℕ) (hh : 3 ≤ h) (G : ℕ) :
    ∃ n, (2 ^ (h - 1) - 1 + ((2 ^ (h - 2) + h - 2) - (h - 1))) * (xseq h n) ^ 2
          + 2 * (2 ^ (h - 2) + h - 2) * (xseq h n) + G < xseq h (n + 1) := by
  set L := 2 ^ (h - 2) + h - 2 with hLdef
  have hc2 := two_le_pow h hh
  have h21 : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
    rw [show h - 1 = (h - 2) + 1 by omega, pow_succ]; ring
  obtain ⟨n, hn⟩ := exists_xseq_ge h hh (2 * L + G + 1)
  refine ⟨n, ?_⟩
  set y := xseq h n with hydef
  have hxsucc : xseq h (n + 1) = (3 * 2 ^ (h - 2) - 1) * y ^ 2 + h * y := xseq_succ h n
  have hK : 2 ^ (h - 1) - 1 + (L - (h - 1)) = 3 * 2 ^ (h - 2) - 2 := by rw [hLdef]; omega
  have hlead : 3 * 2 ^ (h - 2) - 1 = (3 * 2 ^ (h - 2) - 2) + 1 := by omega
  have hy1 : 1 ≤ y := by omega
  have key : 2 * L * y + G < y ^ 2 + h * y := by
    have hpr : (2 * L + G + 1) * y ≤ y * y := mul_le_mul_left hn y
    have hGy : G ≤ G * y := le_mul_of_one_le_right (Nat.zero_le G) hy1
    nlinarith [hpr, hGy, hy1]
  rw [hK, hxsucc, hlead]
  nlinarith [key]

/-- **HHP07 Theorem 3 — quantitative gap, master form.** For `h ≥ 3` the restricted-sum set of
`constA h` taken over `≤ 2^{h-2}+h−2` folds *still* has unbounded gaps (a strict strengthening of
[[constA_unboundedGaps]], which is the `h`-fold case and `h ≤ 2^{h-2}+h−2`). -/
lemma constA_unboundedGaps_L (h : ℕ) (hh : 3 ≤ h) :
    UnboundedGaps (restrictedSums (constA h) (2 ^ (h - 2) + h - 2)) := by
  intro G
  obtain ⟨n, hgap⟩ := gap_size_L h hh G
  set L := 2 ^ (h - 2) + h - 2 with hLdef
  have hL : h - 1 ≤ L := by rw [hLdef]; have := two_le_pow h hh; omega
  refine ⟨(2 ^ (h - 1) - 1 + (L - (h - 1))) * (xseq h n) ^ 2 + 2 * L * (xseq h n), ?_⟩
  intro x hxm hxG hxS
  have hxlt : x < xseq h (n + 1) := by omega
  have hmem := gap_core_gen h hh L n x hL hxS hxlt
  omega

/-- **HHP07 Theorem 3 — `k(h) ≥ 2^{h-2}+h−1` (witness form).** For every `h ≥ 3` there is a basis `A`
of order `h` such that for *every* fold count `l` with `1 ≤ l ≤ 2^{h-2}+h−2`, the exact `l`-fold
restricted sumset `l × A` has unbounded gaps (`Δ(l × A) = +∞`). Equivalently the restricted-order gap
threshold `min{k : Δ(k × A) finite}` of this `A` is `≥ 2^{h-2}+h−1`, which is the lower bound
`k(h) ≥ 2^{h-2}+h−1` of HHP07 Theorem 3. -/
theorem erdos_880_thm3 (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧
      ∀ l, 1 ≤ l → l ≤ 2 ^ (h - 2) + h - 2 → UnboundedGaps (restrictedSumset A l) :=
  ⟨constA h, constA_isBasis h hh, fun _l hl1 hl2 =>
    UnboundedGaps_mono (restrictedSumset_subset_restrictedSums hl1 hl2)
      (constA_unboundedGaps_L h hh)⟩

/-! ### Strengthening: the basis order is *exactly* `h` (HHP07 p. 5 crux)

`erdos_880_unbounded` already gives a faithful negative answer (`constA h` *is* a basis of order `h`).
This section upgrades it to "order exactly `h`": `constA h` is **not** a basis of order `h−1`, matching
the paper's full Theorem 1(ii). The witnesses are the tops `wₖ = 2^{h-1}·xₖ² − 1` of the missing
intervals `[(2^{h-1}−1)xₖ²+(h−1)xₖ+1, 2^{h-1}xₖ²−1]`; they form an infinite set of integers not
representable as `≤ h−1` elements of `constA h`. The infinitude plumbing is proven here; the
non-representability core `constA_not_repr` is the disclosed remaining obligation (the
binary-uniqueness / floor argument, HHP07 p. 5; reduces to `binary_min_rep`, Aristotle `2f8ddb0f`). -/

/-- An element of `constA h` below `x_{k+1}` is either a lower-block element (`< xₖ`) or the `k`-th
translated block (`xₖ + b`, `b ∈ block h k`). Reusable localization for the crux. -/
lemma mem_constA_lt_succ (h k a : ℕ) (hh : 3 ≤ h) (ha : a ∈ constA h) (hlt : a < xseq h (k + 1)) :
    a < xseq h k ∨ ∃ b ∈ block h k, a = xseq h k + b := by
  by_cases hak : xseq h k ≤ a
  · exact Or.inr ⟨a - xseq h k, mem_constA_localize h k a hh ha hak hlt, by omega⟩
  · exact Or.inl (by omega)

/-- The missing-interval witnesses `wₖ = 2^{h-1}·xₖ² − 1` are strictly increasing (hence distinct). -/
lemma w_strictMono (h : ℕ) (hh : 3 ≤ h) :
    StrictMono (fun k => 2 ^ (h - 1) * (xseq h k) ^ 2 - 1) := by
  intro a b hab
  dsimp only
  have h1 : xseq h a < xseq h b := strictMono_nat_of_lt_succ (fun n => xseq_lt_succ h hh n) hab
  have h2 : (xseq h a) ^ 2 < (xseq h b) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : 2 ^ (h - 1) * (xseq h a) ^ 2 < 2 ^ (h - 1) * (xseq h b) ^ 2 :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  have hp : 1 ≤ 2 ^ (h - 1) * (xseq h a) ^ 2 :=
    le_trans (Nat.one_le_pow 2 (xseq h a) (xseq_pos h hh a))
      (Nat.le_mul_of_pos_left _ (by positivity))
  omega

/-- **Non-representability core (machine-checked).** No `wₖ = 2^{h-1}·xₖ² − 1` is a sum of `≤ h−1`
elements of `constA h`.

**Clean ℕ proof (avoids HHP07's real-valued `ρ`/floor).** Write `X = xₖ²`, `x = xₖ`.
Suppose `wₖ = ∑_{i<m} f i`, `m ≤ h−1`, `f i ∈ constA h`. Each `f i ≤ wₖ < x_{k+1}`, so by
[[mem_constA_localize]] each `f i` is `< x` (lower) or `= x + bᵢ`, `bᵢ ∈ block h k`. Classify into
**powers** (`f i = x + 2^{jᵢ}·X`, `1 ≤ jᵢ ≤ h−2`; `q` of them) and **non-powers** (block-`k` interval
`x+b`, `b ≤ X`, or lower `< x`; `p` of them, `q+p = m`). Let `C = ∑ 2^{jᵢ}` (power exponents),
`E = ∑(non-power elements)` (each `≤ x+X`, so `E_div := E / X ≤ p` since `x > p`). Then
`wₖ = C·X + q·x + E = (C + E_div)·X + (q·x + E mod X)`.

* `wₖ ≥ (C+E_div)·X` ⇒ `C + E_div ≤ 2^{h-1} − 1`.
* `C·X + E = wₖ − q·x ≥ (2^{h-1}−1)X + 1` (interval lower bound, `q·x ≤ (h−1)x`) and `E < (E_div+1)X`
  ⇒ `C + E_div ≥ 2^{h-1} − 1`.

So `C + E_div = 2^{h-1} − 1` **exactly**. Setting `c₀ = E_div`, `c_j = #{i : jᵢ = j}` gives
`∑_{j<h-1} c_j 2^j = E_div + C = 2^{h-1}−1` with `∑ c_j = E_div + q ≤ p + q = m ≤ h−1`, so
[[binary_min_rep]] forces every `c_j = 1`: `E_div = 1`, `q = h−2`, and the count is tight
(`m = h−1`, `p = 1`). The single non-power element is then `e = wₖ − C·X − q·x = 2X − 1 − (h−2)x`,
but `e ≤ x + X` (max block element), forcing `x(x−(h−1)) ≤ 1` — impossible for `x ≥ h ≥ 3`. ∎

The `Fin m` classification/partition and fiberwise coefficient bookkeeping are formalized below;
the uniqueness fact `∑ c_j 2^j = 2^{h-1}−1 ∧ ∑ c_j ≤ h−1 → ∀ c_j = 1` is `binary_min_rep`
(`LeanGallery.Combinatorics.Erdos880.Popcount`, proven kernel-pure via popcount minimality). No reals needed. -/
lemma constA_not_repr (h : ℕ) (hh : 3 ≤ h) (k : ℕ) :
    2 ^ (h - 1) * (xseq h k) ^ 2 - 1 ∉ sumsetLE (constA h) (h - 1) := by
  classical
  intro hmem
  obtain ⟨m, f, hm, hf, hsum⟩ := hmem
  set x := xseq h k with hxdef
  set X := x ^ 2 with hXdef
  have hxpos : 0 < x := xseq_pos h hh k
  have hxh : h ≤ x := le_xseq h hh k
  have hXpos : 0 < X := by rw [hXdef]; positivity
  have hXx : X = x * x := by rw [hXdef]; ring
  set w := 2 ^ (h - 1) * X - 1 with hwdef
  -- 2^{h-1} = 2 * 2^{h-2}
  have hph : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
    rw [show h - 1 = (h - 2) + 1 by omega, pow_succ]; ring
  have hP2 : (1 : ℕ) ≤ 2 ^ (h - 2) := Nat.one_le_pow _ _ (by norm_num)
  have hP1 : (1 : ℕ) ≤ 2 ^ (h - 1) := Nat.one_le_pow _ _ (by norm_num)
  -- each f i < x_{k+1}
  have hfle : ∀ i, f i ≤ w := by
    intro i
    have : f i ≤ ∑ j, f j := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (mem_univ i)
    rw [hsum] at this; exact this
  have hwlt : w < xseq h (k + 1) := by
    rw [xseq_succ]
    have hxk1 : (3 * 2 ^ (h - 2) - 1) * x ^ 2 + h * x = (3 * 2 ^ (h - 2) - 1) * X + h * x := by
      rw [hXdef]
    rw [hxk1, hwdef]
    have : 2 ^ (h - 1) * X ≤ (3 * 2 ^ (h - 2) - 1) * X := by
      apply Nat.mul_le_mul_right
      rw [hph]; omega
    have hpos : 0 < h * x := by positivity
    omega
  have hflt : ∀ i, f i < xseq h (k + 1) := fun i => lt_of_le_of_lt (hfle i) hwlt
  -- localization disjunction
  have hclass : ∀ i, f i < x ∨ ∃ b ∈ block h k, f i = x + b :=
    fun i => mem_constA_lt_succ h k (f i) hh (hf i) (hflt i)
  -- the power set and exponent map
  set Pw := univ.filter (fun i => X < f i - x) with hPwdef
  set e : Fin m → ℕ := fun i => Nat.log 2 ((f i - x) / X) with hedef
  -- power decode
  have hPw_pow : ∀ i ∈ Pw, 1 ≤ e i ∧ e i < h - 1 ∧ f i = x + 2 ^ (e i) * X := by
    intro i hi
    rw [hPwdef, mem_filter] at hi
    have hXlt : X < f i - x := hi.2
    have hxle : x ≤ f i := by omega
    -- f i - x ∈ block h k
    have hb : f i - x ∈ block h k := by
      rcases hclass i with hlow | ⟨b, hbb, hfb⟩
      · omega
      · have : f i - x = b := by omega
        rw [this]; exact hbb
    -- b > X so it's a power
    have hpoweq : ∃ j < h - 1, f i - x = 2 ^ j * X := by
      rcases hb with hint | ⟨j, hj, hjeq⟩
      · exact absurd (show f i - x ≤ X from (Set.mem_Icc.mp hint).2) (by omega)
      · exact ⟨j, hj, hjeq⟩
    obtain ⟨j, hjlt, hjeq⟩ := hpoweq
    have hdiv : (f i - x) / X = 2 ^ j := by rw [hjeq, Nat.mul_div_cancel _ hXpos]
    have hej : e i = j := by rw [hedef]; simp only [hdiv]; exact Nat.log_pow (by norm_num) j
    have hfi_eq : f i = x + 2 ^ (e i) * X := by rw [hej]; omega
    have he1 : 1 ≤ e i := by
      rw [hej]
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · exfalso; rw [hj0] at hjeq; simp at hjeq; omega
      · exact hjpos
    exact ⟨he1, by rw [hej]; exact hjlt, hfi_eq⟩
  -- non-power bound
  set NP := univ.filter (fun i => ¬ X < f i - x) with hNPdef
  have hNP_le : ∀ i ∈ NP, f i ≤ x + X := by
    intro i hi
    rw [hNPdef, mem_filter] at hi
    have : f i - x ≤ X := by omega
    omega
  -- counts
  set q := Pw.card with hqdef
  set p := NP.card with hpdef
  have hpq : q + p = m := by
    have h1 : q + p = (univ : Finset (Fin m)).card := by
      rw [hqdef, hpdef, hPwdef, hNPdef]
      exact Finset.card_filter_add_card_filter_not _
    simpa using h1
  set C := ∑ i ∈ Pw, 2 ^ (e i) with hCdef
  set E := ∑ i ∈ NP, f i with hEdef
  -- decomposition  w = C*X + q*x + E
  have hPwsum : ∑ i ∈ Pw, f i = q * x + C * X := by
    have : ∑ i ∈ Pw, f i = ∑ i ∈ Pw, (x + 2 ^ (e i) * X) :=
      Finset.sum_congr rfl (fun i hi => (hPw_pow i hi).2.2)
    rw [this, Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul]
    rw [hCdef, hqdef]; ring
  have hdecomp : w = C * X + q * x + E := by
    have hpart : (∑ i ∈ Pw, f i) + (∑ i ∈ NP, f i) = w := by
      rw [hPwdef, hNPdef, ← hsum]
      exact Finset.sum_filter_add_sum_filter_not univ _ _
    rw [hEdef, ← hpart, hPwsum]; ring
  -- E ≤ p*(x+X)
  have hEle : E ≤ p * (x + X) := by
    rw [hEdef, hpdef]
    calc ∑ i ∈ NP, f i ≤ NP.card • (x + X) := Finset.sum_le_card_nsmul NP _ _ hNP_le
      _ = NP.card * (x + X) := by rw [smul_eq_mul]
  -- division
  set Ed := E / X with hEddef
  set Em := E % X with hEmdef
  have hEdm : X * Ed + Em = E := by rw [hEddef, hEmdef]; exact Nat.div_add_mod E X
  have hEmlt : Em < X := by rw [hEmdef]; exact Nat.mod_lt E hXpos
  have hq_le : q ≤ h - 1 := by omega
  have hp_le : p ≤ h - 1 := by omega
  have hpx : p < x := by omega
  have hpxX : p * x < X := by rw [hXx]; exact mul_lt_mul_of_pos_right hpx hxpos
  -- Ed ≤ p
  have hEd_le_p : Ed ≤ p := by
    by_contra hgt
    push Not at hgt
    have h1 : X * (p + 1) ≤ X * Ed := Nat.mul_le_mul (le_refl X) (by omega)
    have h3 : p * (x + X) < X * (p + 1) := by nlinarith [hpxX]
    omega
  -- the master equation
  have hrw : w = (C + Ed) * X + (q * x + Em) := by
    rw [hdecomp, ← hEdm]; ring
  have hwe : 2 ^ (h - 1) * X = (C + Ed) * X + q * x + Em + 1 := by
    have h1 : 0 < 2 ^ (h - 1) * X := by positivity
    have h2 := hrw
    rw [hwdef] at h2
    omega
  -- C + Ed = 2^{h-1} - 1
  have hCEd_upper : C + Ed ≤ 2 ^ (h - 1) - 1 := by
    have hle : (C + Ed) * X ≤ w := by rw [hrw]; omega
    rw [hwdef] at hle
    have hge1 : 0 < 2 ^ (h - 1) * X := by positivity
    have hlt : (C + Ed) * X < 2 ^ (h - 1) * X := by omega
    have := lt_of_mul_lt_mul_right hlt (Nat.zero_le X)
    omega
  have hCEd_lower : 2 ^ (h - 1) - 1 ≤ C + Ed := by
    by_contra hlt
    push Not at hlt
    have hkey : (h - 1) * x < X := by rw [hXx]; exact mul_lt_mul_of_pos_right (by omega) hxpos
    have hCEdle : (C + Ed) * X ≤ (2 ^ (h - 1) - 2) * X := Nat.mul_le_mul (by omega) (le_refl X)
    have hsub : (2 ^ (h - 1) - 2) * X = 2 ^ (h - 1) * X - 2 * X := by rw [Nat.sub_mul]
    have hqx : q * x ≤ (h - 1) * x := Nat.mul_le_mul hq_le (le_refl x)
    have h2X : 2 * X ≤ 2 ^ (h - 1) * X := Nat.mul_le_mul (by omega) (le_refl X)
    omega
  have hCEd : C + Ed = 2 ^ (h - 1) - 1 := le_antisymm hCEd_upper hCEd_lower
  have hqxEm : q * x + Em = X - 1 := by
    have hCEdX : (C + Ed) * X = 2 ^ (h - 1) * X - X := by rw [hCEd, Nat.sub_mul, one_mul]
    have hXle : X ≤ 2 ^ (h - 1) * X := Nat.le_mul_of_pos_left X (by positivity)
    omega
  -- build coefficient function and apply binary_min_rep
  set cnt : ℕ → ℕ := fun j => (Pw.filter (fun i => e i = j)).card with hcntdef
  set cf : ℕ → ℕ := fun j => cnt j + (if j = 0 then Ed else 0) with hcfdef
  have h0mem : (0 : ℕ) ∈ range (h - 1) := Finset.mem_range.mpr (by omega)
  have hmaps : ∀ i ∈ Pw, e i ∈ range (h - 1) := by
    intro i hi; rw [mem_range]; exact (hPw_pow i hi).2.1
  have hfib : ∑ j ∈ range (h - 1), cnt j * 2 ^ j = C := by
    simp only [hcntdef]
    rw [hCdef, ← Finset.sum_fiberwise_of_maps_to hmaps (fun i => 2 ^ (e i))]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_congr rfl (fun i hi => (by rw [(Finset.mem_filter.mp hi).2] :
        (2 : ℕ) ^ (e i) = 2 ^ j)), Finset.sum_const, smul_eq_mul]
  have hcnt_card : ∑ j ∈ range (h - 1), cnt j = q := by
    simp only [hcntdef]
    rw [hqdef]
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcf_card : ∑ j ∈ range (h - 1), cf j = q + Ed := by
    have hsp : ∑ j ∈ range (h - 1), cf j
        = ∑ j ∈ range (h - 1), cnt j + ∑ j ∈ range (h - 1), (if j = 0 then Ed else 0) := by
      rw [← Finset.sum_add_distrib]
    rw [hsp, hcnt_card]
    congr 1
    rw [Finset.sum_eq_single_of_mem 0 h0mem (fun j _ hj0 => by simp [hj0])]
    simp
  have hClaim1 : ∑ j ∈ range (h - 1), cf j * 2 ^ j = 2 ^ (h - 1) - 1 := by
    have hsplit : ∑ j ∈ range (h - 1), cf j * 2 ^ j
        = ∑ j ∈ range (h - 1), cnt j * 2 ^ j
          + ∑ j ∈ range (h - 1), (if j = 0 then Ed else 0) * 2 ^ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [hcfdef]; ring
    rw [hsplit, hfib]
    have hite : ∑ j ∈ range (h - 1), (if j = 0 then Ed else 0) * 2 ^ j = Ed := by
      rw [Finset.sum_eq_single_of_mem 0 h0mem (fun j _ hj0 => by simp [hj0])]; simp
    rw [hite, hCEd]
  have hClaim2 : ∑ j ∈ range (h - 1), cf j ≤ h - 1 := by rw [hcf_card]; omega
  have hbmr := binary_min_rep (h - 1) cf hClaim1 hClaim2
  -- extract Ed = 1 and q = h - 2
  have hcnt0 : cnt 0 = 0 := by
    simp only [hcntdef]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    have := (hPw_pow i hi).1
    omega
  have hEd1 : Ed = 1 := by
    have hc0 := hbmr 0 h0mem
    simp only [hcfdef] at hc0
    rw [hcnt0] at hc0
    simpa using hc0
  have hqval : q = h - 2 := by
    have hsum1 : ∑ j ∈ range (h - 1), cf j = h - 1 := by
      rw [Finset.sum_congr rfl (fun j hj => hbmr j hj)]; simp
    rw [hcf_card, hEd1] at hsum1
    omega
  -- final contradiction
  have hp1 : p = 1 := by omega
  have hEval : E = 2 * X - 1 - (h - 2) * x := by
    have h1 : X * Ed + Em = E := hEdm
    rw [hEd1, mul_one] at h1
    have h2 := hqxEm
    rw [hqval] at h2
    omega
  exfalso
  have hElep1 : E ≤ x + X := by rw [hp1, one_mul] at hEle; exact hEle
  have heqx : (h - 2) * x + x + x = h * x := by
    have hh2 : (h - 2) + 1 + 1 = h := by omega
    calc (h - 2) * x + x + x = ((h - 2) + 1 + 1) * x := by ring
      _ = h * x := by rw [hh2]
  have hxlb : (h - 2) * x + x + x ≤ X := by
    rw [hXx, heqx]; exact Nat.mul_le_mul hxh (le_refl x)
  omega

/-- `constA h` is **not** a basis of order `h−1`: the witnesses `wₖ` give an infinite non-representable
set. (Plumbing — proven; rests on the disclosed [[constA_not_repr]].) -/
lemma constA_not_basis_pred (h : ℕ) (hh : 3 ≤ h) : ¬ IsBasisOfOrder (constA h) (h - 1) := by
  rw [IsBasisOfOrder, ← Set.not_infinite, not_not]
  exact Set.infinite_of_injective_forall_mem (w_strictMono h hh).injective
    (fun k => constA_not_repr h hh k)

/-- **Erdős #880 — strengthened headline.** For `h ≥ 3` there is a set `A` that is a basis of order
*exactly* `h` (a basis of order `h` but not of order `h−1`) whose restricted-sum set has unbounded
gaps. Rests on the disclosed [[constA_not_repr]]; the unconditional clean form is `erdos_880_unbounded`. -/
theorem erdos_880_exact (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ ¬ IsBasisOfOrder A (h - 1) ∧
      UnboundedGaps (restrictedSums A h) :=
  ⟨constA h, constA_isBasis h hh, constA_not_basis_pred h hh, constA_unboundedGaps h hh⟩

/-! ### Toward HHP07 Theorem 4: the restricted order is *exactly* `2^{h-2}+h−1`

Theorem 3 already gives the **lower** half: the restricted-sum set over `≤ 2^{h-2}+h−2` folds has
unbounded gaps, hence is *not* cofinite, so `constA h` is not a restricted basis of that order.
The **upper** half (`constA h` *is* a restricted basis of order `2^{h-2}+h−1`) needs the p.6 covering
lemma and is tracked in `PENDING_WORK.md`. The lower-half plumbing is proven here. -/

/-- A set with unbounded gaps omits arbitrarily long runs of integers, so its complement is
**infinite** (it is not bounded above). -/
lemma unboundedGaps_compl_infinite {S : Set ℕ} (hS : UnboundedGaps S) :
    ¬ {n : ℕ | n ∉ S}.Finite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨m, hm⟩ := hS (N + 1)
  have hmem : (m + (N + 1)) ∈ {n : ℕ | n ∉ S} := hm (m + (N + 1)) (by omega) (le_refl _)
  have hle := hN hmem
  omega

/-- The `≤ k`-fold restricted sums grow with `k`. -/
lemma restrictedSums_mono {A : Set ℕ} {k k' : ℕ} (hk : k ≤ k') :
    restrictedSums A k ⊆ restrictedSums A k' := by
  intro n hn
  rw [restrictedSums, Set.mem_iUnion₂] at hn ⊢
  obtain ⟨j, hj, hjn⟩ := hn
  rw [Finset.mem_Icc] at hj
  exact ⟨j, Finset.mem_Icc.mpr ⟨hj.1, le_trans hj.2 hk⟩, hjn⟩

/-- Restricted-basis order is upward closed: a restricted basis of order `≤ k` is one of order
`≤ k'` for any `k' ≥ k`. -/
lemma IsRestrictedBasisOfOrder.mono {A : Set ℕ} {k k' : ℕ} (hk : k ≤ k')
    (hb : IsRestrictedBasisOfOrder A k) : IsRestrictedBasisOfOrder A k' :=
  hb.subset (fun _ hn hmem => hn (restrictedSums_mono hk hmem))

/-- **HHP07 Theorem 4 — lower half.** `constA h` is **not** a restricted basis of order
`2^{h-2}+h−2`: by [[constA_unboundedGaps_L]] its `≤ (2^{h-2}+h−2)`-fold restricted-sum set has
unbounded gaps, so its complement is infinite. Hence `ord_r(constA h) ≥ 2^{h-2}+h−1`. -/
lemma constA_not_restrictedBasis_pred (h : ℕ) (hh : 3 ≤ h) :
    ¬ IsRestrictedBasisOfOrder (constA h) (2 ^ (h - 2) + h - 2) :=
  unboundedGaps_compl_infinite (constA_unboundedGaps_L h hh)

/-! ### Upper-half building blocks (HHP07 p.6 covering)

The covering needs to hit any `y ∈ [xₙ, x_{n+1})` with `≤ 2^{h-2}+h−1` *distinct* block elements,
split as a **power part** (`≤ h−1` of the `xₙ + 2ʲxₙ²`, each `≥ xₙ + xₙ²`) plus an **interval part**
(`≤ 2^{h-2}` of the `xₙ + r`, `r < xₙ²`, each `< xₙ + xₙ²`). The two ranges are disjoint, so the union
is automatically distinct. The distinct-subset-sum crux (`subset_sum_le_distinct`) and the power part
(step B) are proven here; the telescoping assembly is the remaining obligation (`PENDING_WORK.md`). -/

/-- **Distinct subset-sum crux.** Any target `V` up to the maximal triangular bound
`k·M − k(k−1)/2` (the sum of the `k` largest values in `{0,…,M}`) is the sum of `≤ k` *distinct*
elements of `{0,1,…,M} = range (M+1)`. The hypothesis `2V + k(k−1) ≤ 2kM` is the division-free form of
`V ≤ kM − k(k−1)/2`. Proof by induction on `M`: for `M+1`, if `V ≤ M+1` the singleton `{V}` works;
otherwise `V ≥ M+2` forces `k ≥ 2`, and we peel the top value `M+1` and recurse on `range (M+1)`. -/
theorem subset_sum_le_distinct : ∀ M k V : ℕ, k ≤ M + 1 → 2 * V + k * (k - 1) ≤ 2 * k * M →
    ∃ R : Finset ℕ, R ⊆ Finset.range (M + 1) ∧ R.card ≤ k ∧ ∑ r ∈ R, r = V := by
  intro M
  induction M with
  | zero =>
    intro k V _ hV
    have hV0 : V = 0 := by simp only [Nat.mul_zero] at hV; omega
    exact ⟨∅, by simp, by simp, by simp [hV0]⟩
  | succ M ih =>
    intro k V hk hV
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hV0 : V = 0 := by simp at hV; omega
      exact ⟨∅, by simp, by simp, by simp [hV0]⟩
    · by_cases hVle : V ≤ M + 1
      · exact ⟨{V}, by rw [Finset.singleton_subset_iff, Finset.mem_range]; omega,
          by rw [Finset.card_singleton]; omega, by rw [Finset.sum_singleton]⟩
      · push Not at hVle
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h2 | h2
          · interval_cases k ; omega
          · exact h2
        obtain ⟨b, rfl⟩ : ∃ b, k = b + 2 := ⟨k - 2, by omega⟩
        obtain ⟨V', rfl⟩ : ∃ V', V = V' + (M + 1) := ⟨V - (M + 1), by omega⟩
        have hk' : b + 1 ≤ M + 1 := by omega
        have hV' : 2 * V' + (b + 1) * ((b + 1) - 1) ≤ 2 * (b + 1) * M := by
          have e1 : (b + 1) - 1 = b := by omega
          have e2 : (b + 2) - 1 = b + 1 := by omega
          rw [e2] at hV; rw [e1]; nlinarith [hV]
        obtain ⟨R', hR'sub, hR'card, hR'sum⟩ := ih (b + 1) V' hk' hV'
        have hnotmem : M + 1 ∉ R' :=
          fun hm => by have := Finset.mem_range.mp (hR'sub hm); omega
        refine ⟨insert (M + 1) R', ?_, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_range.mpr (by omega)
          · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hR'sub hx); omega)
        · rw [Finset.card_insert_of_notMem hnotmem]; omega
        · rw [Finset.sum_insert hnotmem, hR'sum]; omega

/-- **Translated distinct subset-sum** (the interval-cover crux). Any `a ≤ T` up to the maximal
`k`-element bound `k(a+M) − k(k−1)/2` is a sum of `≤ k` *distinct* elements of `Icc a (a+M)`. The extra
hypothesis `a + k ≤ M + 1` (vs. the bare `k ≤ M+1`) guarantees enough room that the peeling never hits
an edge — it holds with huge slack in the application (`a = xₙ`, `M = xₙ²−1`, `k = 2^{h-2}`, for `n`
large). Strong induction on `T`: `T ≤ a+M` → `{T}`; band `a+M < T ≤ 2a+M` → `{a, T−a}`; else peel the
top `a+M` and recurse on `Icc a (a+M−1)`. Unlike `range`, the `Icc` elements carry the `a`-offsets, so
the element-count coupling is already resolved (`∑R = T` directly). -/
theorem subset_sum_Icc_distinct : ∀ T a M k : ℕ, a + k ≤ M + 1 → a ≤ T →
    2 * T + k * (k - 1) ≤ 2 * k * (a + M) →
    ∃ R : Finset ℕ, R ⊆ Finset.Icc a (a + M) ∧ R.card ≤ k ∧ ∑ r ∈ R, r = T := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    intro a M k hak haT hbound
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hT0 : T = 0 := by simp only [Nat.mul_zero, Nat.zero_mul] at hbound; omega
      subst hT0; exact ⟨∅, by simp, by simp, by simp⟩
    · by_cases hTle : T ≤ a + M
      · exact ⟨{T}, by rw [Finset.singleton_subset_iff, Finset.mem_Icc]; omega,
          by rw [Finset.card_singleton]; omega, by rw [Finset.sum_singleton]⟩
      · push Not at hTle
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h2 | h2
          · interval_cases k ; omega
          · exact h2
        have ham : a ≤ M := by omega
        by_cases hband : T ≤ 2 * a + M
        · have hne : a ≠ T - a := by omega
          refine ⟨{a, T - a}, ?_, ?_, ?_⟩
          · rw [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_Icc,
              Finset.mem_Icc]; omega
          · rw [Finset.card_pair hne]; omega
          · rw [Finset.sum_pair hne]; omega
        · push Not at hband
          obtain ⟨b, rfl⟩ : ∃ b, k = b + 2 := ⟨k - 2, by omega⟩
          obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
          set T' := T - (a + (M' + 1)) with hT'def
          have hTeq : T = T' + (a + (M' + 1)) := by omega
          have hak' : a + (b + 1) ≤ M' + 1 := by omega
          have haT' : a ≤ T' := by omega
          have hbound' : 2 * T' + (b + 1) * ((b + 1) - 1) ≤ 2 * (b + 1) * (a + M') := by
            have e : (b + 1) - 1 = b := by omega
            have e2 : (b + 2) - 1 = b + 1 := by omega
            rw [e]; rw [e2] at hbound; rw [hTeq] at hbound; nlinarith [hbound]
          have hTlt : T' < T := by omega
          obtain ⟨R', hR'sub, hR'card, hR'sum⟩ :=
            ih T' hTlt a M' (b + 1) hak' haT' hbound'
          have hnotmem : a + (M' + 1) ∉ R' :=
            fun hmem => by have := Finset.mem_Icc.mp (hR'sub hmem); omega
          refine ⟨insert (a + (M' + 1)) R', ?_, ?_, ?_⟩
          · intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · rw [Finset.mem_Icc]; omega
            · have := Finset.mem_Icc.mp (hR'sub hx); rw [Finset.mem_Icc]; omega
          · rw [Finset.card_insert_of_notMem hnotmem]; omega
          · rw [Finset.sum_insert hnotmem, hR'sum]; omega

/-- **Power part (HHP07 p.6 step B).** For `m < 2^{h-1}` there is a set `P` of `≤ h−1` *distinct* power
block elements `xₙ + 2ʲ·xₙ²` (the binary support of `m`) with `∑ P = m·xₙ² + (pc m)·xₙ` — i.e. exactly
the ladder value `zval h n m` (the popcount count is pinned via [[card_eq_pc]]). Every `p ∈ P` is at
least `xₙ + xₙ²`, so `P` is disjoint from the interval part. -/
lemma power_block_repr (h n m : ℕ) (hh : 3 ≤ h) (hm : m < 2 ^ (h - 1)) :
    ∃ P : Finset ℕ, (↑P ⊆ constA h) ∧ (∀ p ∈ P, xseq h n + (xseq h n) ^ 2 ≤ p) ∧
      P.card ≤ h - 1 ∧ ∑ p ∈ P, p = m * (xseq h n) ^ 2 + pc m * xseq h n := by
  obtain ⟨S, hSsub, hSsum⟩ := binary_subset_sum (h - 1) m hm
  have hX : 0 < (xseq h n) ^ 2 := pow_pos (xseq_pos h hh n) 2
  set f : ℕ → ℕ := fun j => xseq h n + 2 ^ j * (xseq h n) ^ 2 with hf
  have hinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b := by
    intro a _ b _ hab
    simp only [hf] at hab
    have h2 : 2 ^ a * (xseq h n) ^ 2 = 2 ^ b * (xseq h n) ^ 2 := Nat.add_left_cancel hab
    exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hX h2)
  refine ⟨S.image f, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [Finset.coe_image, Set.mem_image] at hp
    obtain ⟨j, hjS, rfl⟩ := hp
    exact mem_constA_block h n _ (mem_block_pow h n j (Finset.mem_range.mp (hSsub hjS)))
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨j, _, rfl⟩ := hp
    have h1 : (xseq h n) ^ 2 ≤ 2 ^ j * (xseq h n) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by positivity)
    simp only [hf]; omega
  · calc (S.image f).card ≤ S.card := Finset.card_image_le
      _ ≤ h - 1 := le_trans (Finset.card_le_card hSsub) (by rw [Finset.card_range])
  · rw [Finset.sum_image hinj]
    have hcard : S.card = pc m := card_eq_pc m S hSsum
    have hsum : ∑ j ∈ S, f j = S.card * xseq h n + (∑ j ∈ S, 2 ^ j) * (xseq h n) ^ 2 := by
      simp only [hf, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_mul]
    rw [hsum, hSsum, hcard]; ring

/-- The HHP07 p.6 "ladder" value `z_m = m·xₙ² + (pc m)·xₙ`, where `pc m` is the binary digit-sum
(popcount). For `m < 2^{h-1}` it is exactly `∑P` from [[power_block_repr]] (with `m` the power mask):
the value reachable by the power block elements whose exponent set is the binary support of `m`. -/
def zval (h n m : ℕ) : ℕ := m * (xseq h n) ^ 2 + pc m * xseq h n

/-- **The ladder is strictly increasing** on `[0, 2^{h-1})`. Each `+1` in `m` adds a full `xₙ²` while
the popcount term changes by at most `(h−1)·xₙ < xₙ²` (since `pc m ≤ h−1` for `m < 2^{h-1}` and
`xₙ ≥ h`); so `z_{m+1} > z_m`. This monotonicity (plus the bounded gaps `z_{m+1}−z_m ≤ xₙ²+xₙ`) is the
backbone of the telescoping that covers `[xₙ, x_{n+1})`. -/
lemma zval_lt_succ (h n m : ℕ) (hh : 3 ≤ h) (hm : m < 2 ^ (h - 1)) :
    zval h n m < zval h n (m + 1) := by
  have hpcm : pc m ≤ h - 1 := pc_le_of_lt_pow (h - 1) m hm
  have hx0 : 0 < xseq h n := xseq_pos h hh n
  have hx : h ≤ xseq h n := le_xseq h hh n
  have h1 : pc m * xseq h n ≤ (h - 1) * xseq h n := Nat.mul_le_mul_right _ hpcm
  have h2 : (h - 1) * xseq h n < (xseq h n) ^ 2 := by
    have hlt : h - 1 < xseq h n := by omega
    nlinarith [hlt, hx0]
  simp only [zval]
  nlinarith [h1, h2, Nat.zero_le (pc (m + 1) * xseq h n)]

/-- The ladder gap is at most `xₙ² + xₙ`: `z_{m+1} − z_m ≤ xₙ² + xₙ` (the `+1` adds one `xₙ²` and the
popcount rises by at most `1`, [[pc_succ_le]]). Together with [[zval_lt_succ]] this bounds the spacing,
so the width-`2^{h-2}xₙ²` interval-cover translates overlap. -/
lemma zval_succ_le (h n m : ℕ) : zval h n (m + 1) ≤ zval h n m + ((xseq h n) ^ 2 + xseq h n) := by
  have hpc : pc (m + 1) ≤ pc m + 1 := pc_succ_le m
  have h1 : pc (m + 1) * xseq h n ≤ (pc m + 1) * xseq h n := Nat.mul_le_mul_right _ hpc
  simp only [zval]
  nlinarith [h1]

/-- **find-`m` (telescoping).** For `y ∈ [xₙ, x_{n+1})` there is a ladder index `m < 2^{h-1}` with the
residual `y − z_m` landing in the interval-cover window `[xₙ, 2^{h-2}xₙ² + xₙ)`. Take `m` to be the
greatest index with `z_m + xₙ ≤ y`: the lower bound is then immediate, and the upper bound follows
either from maximality (`z_{m+1} > y − xₙ` and the gap bound [[zval_succ_le]]) or, at the top
`m = 2^{h-1}−1`, from `y < x_{n+1}` and `z_{2^{h-1}−1} = (2^{h-1}−1)xₙ² + (h−1)xₙ`. This is the
selection step of the HHP07 p.6 covering; it composes with [[power_block_repr]] (both want
`m < 2^{h-1}`) and the interval cover (step A) to give `basis_covering_L`. -/
lemma find_ladder (h n y : ℕ) (hh : 3 ≤ h) (hlo : xseq h n ≤ y) (hhi : y < xseq h (n + 1)) :
    ∃ m, m < 2 ^ (h - 1) ∧ zval h n m + xseq h n ≤ y ∧
      y < zval h n m + (2 ^ (h - 2) * (xseq h n) ^ 2 + xseq h n) := by
  classical
  have hc2 := two_le_pow h hh
  have hx0 : 0 < xseq h n := xseq_pos h hh n
  have h21 : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
    rw [show h - 1 = (h - 2) + 1 by omega, pow_succ]; ring
  set P : ℕ → Prop := fun m => zval h n m + xseq h n ≤ y with hP
  have hP0 : P 0 := by simp only [hP, zval, pc_zero]; omega
  set m := Nat.findGreatest P (2 ^ (h - 1) - 1) with hmdef
  have hPm : P m := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmN : m ≤ 2 ^ (h - 1) - 1 := Nat.findGreatest_le _
  have hmlt : m < 2 ^ (h - 1) := by
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    omega
  refine ⟨m, hmlt, hPm, ?_⟩
  -- `X + xₙ ≤ 2^{h-2}·X` (the gap fits the interval-cover window)
  have hXx : (xseq h n) ^ 2 + xseq h n ≤ 2 ^ (h - 2) * (xseq h n) ^ 2 := by
    have h1 : 2 * (xseq h n) ^ 2 ≤ 2 ^ (h - 2) * (xseq h n) ^ 2 := by
      apply Nat.mul_le_mul_right; omega
    have h2 : xseq h n ≤ (xseq h n) ^ 2 := by
      rw [pow_two]; exact Nat.le_mul_of_pos_left _ hx0
    omega
  by_cases hmeq : m = 2 ^ (h - 1) - 1
  · have hzN : zval h n m
        = (2 ^ (h - 1) - 1) * (xseq h n) ^ 2 + (h - 1) * xseq h n := by
      rw [hmeq]; simp only [zval]; rw [pc_two_pow_sub_one]
    rw [hzN]
    rw [xseq_succ] at hhi
    have hgoal_eq : (2 ^ (h - 1) - 1) * (xseq h n) ^ 2 + (h - 1) * xseq h n
        + (2 ^ (h - 2) * (xseq h n) ^ 2 + xseq h n)
        = (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + h * xseq h n := by
      have c1 : 2 ^ (h - 1) - 1 + 2 ^ (h - 2) = 3 * 2 ^ (h - 2) - 1 := by omega
      have c2 : h - 1 + 1 = h := by omega
      calc (2 ^ (h - 1) - 1) * (xseq h n) ^ 2 + (h - 1) * xseq h n
            + (2 ^ (h - 2) * (xseq h n) ^ 2 + xseq h n)
          = ((2 ^ (h - 1) - 1) + 2 ^ (h - 2)) * (xseq h n) ^ 2
            + ((h - 1) + 1) * xseq h n := by ring
        _ = (3 * 2 ^ (h - 2) - 1) * (xseq h n) ^ 2 + h * xseq h n := by rw [c1, c2]
    rw [hgoal_eq]; exact hhi
  · have hnotP : y < zval h n (m + 1) + xseq h n := by
      by_contra hcon
      push Not at hcon
      have hle : m + 1 ≤ Nat.findGreatest P (2 ^ (h - 1) - 1) :=
        Nat.le_findGreatest (by omega) hcon
      omega
    have hgap := zval_succ_le h n m
    omega

/-- **Disjoint-union glue.** Two disjoint finite subsets of `constA h` of total size in `[1, L]` realise
their summed value as a `≤ L`-fold restricted sum. (In the covering, `P` = power part and `I` = interval
part, disjoint because `P ⊆ [xₙ+xₙ², ∞)` and `I ⊆ [0, xₙ+xₙ²)`.) -/
lemma mem_restrictedSums_disjoint_union (h L : ℕ) {P I : Finset ℕ}
    (hP : ↑P ⊆ constA h) (hI : ↑I ⊆ constA h) (_hdisj : Disjoint P I)
    (hpos : 1 ≤ (P ∪ I).card) (hcard : (P ∪ I).card ≤ L) :
    ∑ x ∈ (P ∪ I), x ∈ restrictedSums (constA h) L := by
  refine mem_restrictedSums (Finset.mem_Icc.mpr ⟨hpos, hcard⟩) ⟨P ∪ I, ?_, rfl, rfl⟩
  rw [Finset.coe_union]; exact Set.union_subset hP hI

/-- **Interval part (HHP07 p.6 step A).** For `n` large enough (`xₙ + 2^{h-2} ≤ xₙ²`) and a target
`T ≥ xₙ` within the maximal interval-sum bound, `T` is a sum of `≤ 2^{h-2}` *distinct* interval block
elements `xₙ + r` (`r < xₙ²`, so each `< xₙ + xₙ²` — disjoint from the power part), all in `constA h`.
A direct application of [[subset_sum_Icc_distinct]] with `a = xₙ`, `M = xₙ²−1`, `k = 2^{h-2}`. -/
lemma interval_block_repr (h n T : ℕ) (hh : 3 ≤ h)
    (hbig : xseq h n + 2 ^ (h - 2) ≤ (xseq h n) ^ 2) (hTlo : xseq h n ≤ T)
    (hbound : 2 * T + 2 ^ (h - 2) * (2 ^ (h - 2) - 1)
      ≤ 2 * 2 ^ (h - 2) * (xseq h n + ((xseq h n) ^ 2 - 1))) :
    ∃ I : Finset ℕ, (↑I ⊆ constA h) ∧ (∀ i ∈ I, i < xseq h n + (xseq h n) ^ 2) ∧
      I.card ≤ 2 ^ (h - 2) ∧ ∑ i ∈ I, i = T := by
  have hx0 : 0 < xseq h n := xseq_pos h hh n
  have hX0 : 0 < (xseq h n) ^ 2 := pow_pos hx0 2
  obtain ⟨R, hRsub, hRcard, hRsum⟩ :=
    subset_sum_Icc_distinct T (xseq h n) ((xseq h n) ^ 2 - 1) (2 ^ (h - 2)) (by omega) hTlo hbound
  refine ⟨R, ?_, ?_, hRcard, hRsum⟩
  · intro r hr
    have hrIcc := Finset.mem_Icc.mp (hRsub (Finset.mem_coe.mp hr))
    obtain ⟨b, rfl⟩ : ∃ b, r = xseq h n + b := ⟨r - xseq h n, by omega⟩
    exact mem_constA_block h n b (mem_block_interval h n b (by omega))
  · intro i hi
    have := Finset.mem_Icc.mp (hRsub hi)
    omega

/-- **Upper-half covering (HHP07 p.6).** For `n` large (`xₙ ≥ 2^{h-1}`), every `y ∈ [xₙ, x_{n+1})` is a
sum of `≤ 2^{h-2}+h−1` *distinct* elements of `constA h`: pick the ladder index `m` ([[find_ladder]]),
take the power part `P` ([[power_block_repr]], `∑P = z_m`) and the interval part `I`
([[interval_block_repr]], `∑I = y − z_m`); `P` and `I` are disjoint (the `xₙ+xₙ²` threshold), so
`P ∪ I` is a single restricted-sum witness of size `≤ (h−1)+2^{h-2}`. -/
lemma basis_covering_L (h n y : ℕ) (hh : 3 ≤ h) (hn0 : 2 ^ (h - 1) ≤ xseq h n)
    (hlo : xseq h n ≤ y) (hhi : y < xseq h (n + 1)) :
    y ∈ restrictedSums (constA h) (2 ^ (h - 2) + h - 1) := by
  obtain ⟨m, hmlt, hmlo, hmhi⟩ := find_ladder h n y hh hlo hhi
  obtain ⟨P, hPsub, hPge, hPcard, hPsum⟩ := power_block_repr h n m hh hmlt
  have hK2 : 2 ≤ 2 ^ (h - 2) := two_le_pow h hh
  have h21 : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
    rw [show h - 1 = (h - 2) + 1 by omega, pow_succ]; ring
  have hxge : 2 * 2 ^ (h - 2) ≤ xseq h n := by rw [← h21]; exact hn0
  have hX0 : 0 < (xseq h n) ^ 2 := pow_pos (xseq_pos h hh n) 2
  have hn0' : 2 * 2 ^ (h - 2) * xseq h n ≤ (xseq h n) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ hxge
  set T := y - zval h n m with hTdef
  have hzdef : zval h n m = m * (xseq h n) ^ 2 + pc m * xseq h n := rfl
  have hbig : xseq h n + 2 ^ (h - 2) ≤ (xseq h n) ^ 2 := by nlinarith [hn0', hxge, hK2]
  have hTlo : xseq h n ≤ T := by omega
  have hThi : T < 2 ^ (h - 2) * (xseq h n) ^ 2 + xseq h n := by omega
  have hbound : 2 * T + 2 ^ (h - 2) * (2 ^ (h - 2) - 1)
      ≤ 2 * 2 ^ (h - 2) * (xseq h n + ((xseq h n) ^ 2 - 1)) := by
    obtain ⟨K', hKK'⟩ : ∃ K', 2 ^ (h - 2) = K' + 2 := ⟨2 ^ (h - 2) - 2, by omega⟩
    obtain ⟨X', hXX'⟩ : ∃ X', (xseq h n) ^ 2 = X' + 1 := ⟨(xseq h n) ^ 2 - 1, by omega⟩
    rw [hKK'] at hxge
    rw [hKK', hXX'] at hThi ⊢
    have s1 : K' + 2 - 1 = K' + 1 := by omega
    have s2 : X' + 1 - 1 = X' := by omega
    rw [s1, s2]
    nlinarith [hThi, hxge]
  obtain ⟨I, hIsub, hIlt, hIcard, hIsum⟩ := interval_block_repr h n T hh hbig hTlo hbound
  have hdisj : Disjoint P I := by
    rw [Finset.disjoint_left]
    intro a haP haI
    have h1 := hPge a haP
    have h2 := hIlt a haI
    omega
  have hsumU : ∑ x ∈ (P ∪ I), x = y := by
    rw [Finset.sum_union hdisj, hPsum, hIsum, ← hzdef]; omega
  have hpos : 1 ≤ (P ∪ I).card := by
    rw [Nat.one_le_iff_ne_zero]
    intro hc
    rw [Finset.card_eq_zero] at hc
    rw [hc, Finset.sum_empty] at hsumU
    have : h ≤ y := le_trans (le_xseq h hh n) hlo
    omega
  have hcardle : (P ∪ I).card ≤ 2 ^ (h - 2) + h - 1 := by
    rw [Finset.card_union_of_disjoint hdisj]; omega
  rw [← hsumU]
  exact mem_restrictedSums_disjoint_union h _ hPsub hIsub hdisj hpos hcardle

/-- **HHP07 Theorem 4 — upper half.** `constA h` *is* a restricted basis of order `2^{h-2}+h−1`: every
sufficiently large integer (`≥ x_{n₀}` where `x_{n₀} ≥ 2^{h-1}`) lies in `[xₙ, x_{n+1})` for some
`n ≥ n₀` and is covered by [[basis_covering_L]]. Hence `ord_r(constA h) ≤ 2^{h-2}+h−1`. -/
lemma constA_isRestrictedBasis (h : ℕ) (hh : 3 ≤ h) :
    IsRestrictedBasisOfOrder (constA h) (2 ^ (h - 2) + h - 1) := by
  obtain ⟨n₀, hn₀⟩ := exists_xseq_ge h hh (2 ^ (h - 1))
  apply Set.Finite.subset (Set.finite_Iio (xseq h n₀))
  intro y hy
  rw [Set.mem_Iio]
  by_contra hlt
  rw [not_lt] at hlt
  have hyh : h ≤ y := le_trans (le_xseq h hh n₀) hlt
  obtain ⟨n, hn1, hn2⟩ := find_block h hh y hyh
  have hn0n : 2 ^ (h - 1) ≤ xseq h n := by
    rcases Nat.lt_or_ge n n₀ with hlt' | hge
    · exfalso
      have hmono : xseq h (n + 1) ≤ xseq h n₀ := xseq_mono h hh (by omega)
      omega
    · exact le_trans hn₀ (xseq_mono h hh hge)
  exact hy (basis_covering_L h n y hh hn0n hn1 hn2)

/-- **HHP07 Theorem 4 — `f(h) ≥ 2^{h-2}+h−1` (witness form).** For every `h ≥ 3` the witness basis
`constA h` has restricted order **exactly** `2^{h-2}+h−1`: it is a restricted basis of that order but
**not** of order `2^{h-2}+h−2`. (Monotonicity [[IsRestrictedBasisOfOrder.mono]] pins `ord_r` exactly.)
So `f(h) ≥ 2^{h-2}+h−1`. The `¬`-half is [[constA_not_restrictedBasis_pred]] (from Theorem 3); the
positive half is [[constA_isRestrictedBasis]]. (Witness form: `f`'s finiteness is open, like `k`'s.) -/
theorem erdos_880_thm4 (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧
      IsRestrictedBasisOfOrder A (2 ^ (h - 2) + h - 1) ∧
      ¬ IsRestrictedBasisOfOrder A (2 ^ (h - 2) + h - 2) :=
  ⟨constA h, constA_isBasis h hh, constA_isRestrictedBasis h hh,
    constA_not_restrictedBasis_pred h hh⟩

/-- **HHP07 Theorem 4, sharp form.** The restricted order of the witness basis is *exactly*
`2^{h-2}+h−1`: `ord_r(constA h) = 2^{h-2}+h−1`. (Upper bound from [[constA_isRestrictedBasis]]; lower
bound because `sInf` lands in the set so by [[IsRestrictedBasisOfOrder.mono]] any smaller order would
contradict [[constA_not_restrictedBasis_pred]].) -/
theorem constA_restrictedOrder_eq (h : ℕ) (hh : 3 ≤ h) :
    restrictedOrder (constA h) = 2 ^ (h - 2) + h - 1 := by
  have hne : {k : ℕ | IsRestrictedBasisOfOrder (constA h) k}.Nonempty :=
    ⟨_, constA_isRestrictedBasis h hh⟩
  refine le_antisymm (Nat.sInf_le (constA_isRestrictedBasis h hh)) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hmem : IsRestrictedBasisOfOrder (constA h) (restrictedOrder (constA h)) := Nat.sInf_mem hne
  have hle : restrictedOrder (constA h) ≤ 2 ^ (h - 2) + h - 2 := by omega
  exact constA_not_restrictedBasis_pred h hh (IsRestrictedBasisOfOrder.mono hle hmem)

end LeanGallery.Combinatorics.Erdos880
