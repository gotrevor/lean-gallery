/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Popcount minimality and `binary_min_rep`

The number-theoretic heart of the "order exactly `h`" crux (HHP07 p. 5). We prove, from scratch and
kernel-pure, that the **binary representation minimizes the digit sum**: any way of writing a number
as `∑ cⱼ·2ʲ` uses coefficient total at least its popcount (`pc`, the base-2 digit sum). From this:

* `pc_two_pow_sub_one`: `pc (2^N − 1) = N`;
* `binary_min_rep`: if `∑_{j<N} cⱼ·2ʲ = 2^N − 1` and `∑_{j<N} cⱼ ≤ N`, then every `cⱼ = 1`.

`binary_min_rep` is exactly the uniqueness fact the crux needs: the minimal-length power
representation of `2^N − 1` is the all-ones binary one. No `popCount` exists in mathlib, so this is
developed here directly via the digit recursion `pc n = n%2 + pc (n/2)`.
-/

namespace LeanGallery.Combinatorics.Erdos880
open Finset

/-- Popcount = sum of base-2 digits. -/
def pc (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp] lemma pc_zero : pc 0 = 0 := by simp [pc]

/-- Digit recursion, total (holds at 0 too). -/
lemma pc_rec (n : ℕ) : pc n = n % 2 + pc (n / 2) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [pc]
  · unfold pc
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 2) h]
    simp

/-- Splitting a `range (N+1)` weighted sum: peel index 0, factor 2 from the tail. -/
lemma weighted_split (N : ℕ) (c : ℕ → ℕ) :
    ∑ j ∈ range (N + 1), c j * 2 ^ j
      = c 0 + 2 * ∑ i ∈ range N, c (i + 1) * 2 ^ i := by
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]; ring

lemma card_split (N : ℕ) (c : ℕ → ℕ) :
    ∑ j ∈ range (N + 1), c j = c 0 + ∑ i ∈ range N, c (i + 1) := by
  rw [Finset.sum_range_succ']; ring

/-- Adding 1 raises popcount by at most 1. -/
lemma pc_succ_le (n : ℕ) : pc (n + 1) ≤ pc n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have e1 : pc (m + m) = pc m := by
        rw [pc_rec (m + m)]
        have ha : (m + m) % 2 = 0 := by omega
        have hb : (m + m) / 2 = m := by omega
        rw [ha, hb]; omega
      have e2 : pc (m + m + 1) = 1 + pc m := by
        rw [pc_rec (m + m + 1)]
        have h1 : (m + m + 1) % 2 = 1 := by omega
        have h2 : (m + m + 1) / 2 = m := by omega
        rw [h1, h2]
      omega
    · subst hm
      have e1 : pc (2 * m + 1) = 1 + pc m := by
        rw [pc_rec (2 * m + 1)]
        have h1 : (2 * m + 1) % 2 = 1 := by omega
        have h2 : (2 * m + 1) / 2 = m := by omega
        rw [h1, h2]
      have e2 : pc (2 * m + 1 + 1) = pc (m + 1) := by
        rw [pc_rec (2 * m + 1 + 1)]
        have h1 : (2 * m + 1 + 1) % 2 = 0 := by omega
        have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
        rw [h1, h2]; omega
      have ihm := ih m (by omega)
      omega

/-- Adding `t` raises popcount by at most `t`. -/
lemma pc_add_le (x t : ℕ) : pc (x + t) ≤ pc x + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hsl := pc_succ_le (x + t)
      have e : x + (t + 1) = (x + t) + 1 := by ring
      rw [e]; omega

lemma pc_le_self (n : ℕ) : pc n ≤ n := by
  have := pc_add_le 0 n; simpa using this

/-- A number `< 2^N` has at most `N` set bits: `pc m ≤ N` (it has `≤ N` binary digits, each `≤ 1`).
Peels the low bit via [[pc_rec]]: `pc m = m%2 + pc (m/2)` with `m/2 < 2^{N-1}`. -/
lemma pc_le_of_lt_pow : ∀ (N m : ℕ), m < 2 ^ N → pc m ≤ N := by
  intro N
  induction N with
  | zero => intro m hm; interval_cases m; simp
  | succ N ih =>
      intro m hm
      rw [pc_rec m]
      have hm2 : m / 2 < 2 ^ N := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hm; omega
      have := ih (m / 2) hm2
      omega

/-- Popcount of `2^N − 1` is `N` (all bits set). -/
lemma pc_two_pow_sub_one (N : ℕ) : pc (2 ^ N - 1) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hpow : (1 : ℕ) ≤ 2 ^ N := Nat.one_le_pow _ _ (by norm_num)
      have key : 2 ^ (N + 1) - 1 = 2 * (2 ^ N - 1) + 1 := by rw [pow_succ]; omega
      rw [key, pc_rec (2 * (2 ^ N - 1) + 1)]
      have h1 : (2 * (2 ^ N - 1) + 1) % 2 = 1 := by omega
      have h2 : (2 * (2 ^ N - 1) + 1) / 2 = 2 ^ N - 1 := by omega
      rw [h1, h2, ih]; omega

/-- **Min-weight (carry form).** Binary minimizes digit-sum. -/
lemma pc_carry_le : ∀ (N : ℕ) (c : ℕ → ℕ) (carry : ℕ),
    pc (carry + ∑ j ∈ range N, c j * 2 ^ j) ≤ pc carry + ∑ j ∈ range N, c j := by
  intro N
  induction N with
  | zero => intro c carry; simp
  | succ N ih =>
      intro c carry
      rw [weighted_split N c]
      have hval : carry + (c 0 + 2 * ∑ i ∈ range N, c (i + 1) * 2 ^ i)
          = (carry + c 0) + 2 * ∑ i ∈ range N, c (i + 1) * 2 ^ i := by ring
      rw [hval, pc_rec ((carry + c 0) + 2 * ∑ i ∈ range N, c (i + 1) * 2 ^ i)]
      have hmod : ((carry + c 0) + 2 * ∑ i ∈ range N, c (i + 1) * 2 ^ i) % 2
          = (carry + c 0) % 2 := by omega
      have hdiv : ((carry + c 0) + 2 * ∑ i ∈ range N, c (i + 1) * 2 ^ i) / 2
          = (carry + c 0) / 2 + ∑ i ∈ range N, c (i + 1) * 2 ^ i := by omega
      rw [hmod, hdiv]
      have hih := ih (fun i => c (i + 1)) ((carry + c 0) / 2)
      have hpcc := pc_rec (carry + c 0)
      have hadd := pc_add_le carry (c 0)
      rw [card_split N c]
      omega

/-- Carry-free corollary: popcount of a representation ≤ its coefficient sum. -/
lemma pc_sum_le (N : ℕ) (c : ℕ → ℕ) :
    pc (∑ j ∈ range N, c j * 2 ^ j) ≤ ∑ j ∈ range N, c j := by
  have := pc_carry_le N c 0; simpa using this

/-- **`binary_min_rep`.** The minimal-length power representation of `2^N − 1` is binary: if
`∑_{j<N} c j · 2^j = 2^N − 1` and the coefficient total is `≤ N`, then every `c j = 1`. -/
lemma binary_min_rep : ∀ (N : ℕ) (c : ℕ → ℕ),
    (∑ j ∈ range N, c j * 2 ^ j = 2 ^ N - 1) → (∑ j ∈ range N, c j ≤ N) →
    ∀ j ∈ range N, c j = 1 := by
  intro N
  induction N with
  | zero => intro c _ _ j hj; simp at hj
  | succ N ih =>
      intro c hsum hcard j hj
      have hpow : (1 : ℕ) ≤ 2 ^ N := Nat.one_le_pow _ _ (by norm_num)
      have hpowsucc : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
      set V := ∑ i ∈ range N, c (i + 1) * 2 ^ i with hV
      set W := ∑ i ∈ range N, c (i + 1) with hW
      have heq : c 0 + 2 * V = 2 ^ (N + 1) - 1 := by rw [hV, ← weighted_split N c]; exact hsum
      have hmw_all : pc (2 ^ (N + 1) - 1) ≤ ∑ j ∈ range (N + 1), c j := by
        rw [← hsum]; exact pc_sum_le (N + 1) c
      rw [pc_two_pow_sub_one] at hmw_all
      rw [card_split N c, ← hW] at hcard hmw_all
      have hweq : c 0 + W = N + 1 := by omega
      have hmwV : pc V ≤ W := by rw [hV]; exact pc_sum_le N (fun i => c (i + 1))
      obtain ⟨t, ht⟩ : ∃ t, c 0 = 2 * t + 1 := ⟨c 0 / 2, by omega⟩
      have hVle : V + t = 2 ^ N - 1 := by omega
      have hlow : pc (2 ^ N - 1) ≤ pc V + t := by rw [← hVle]; exact pc_add_le V t
      rw [pc_two_pow_sub_one] at hlow
      have ht0 : t = 0 := by omega
      have hc0 : c 0 = 1 := by omega
      have hVfull : V = 2 ^ N - 1 := by omega
      have hWfull : W ≤ N := by omega
      have harg1 : ∑ i ∈ range N, c (i + 1) * 2 ^ i = 2 ^ N - 1 := by rw [← hV]; exact hVfull
      have harg2 : ∑ i ∈ range N, c (i + 1) ≤ N := by rw [← hW]; exact hWfull
      have hihres := ih (fun i => c (i + 1)) harg1 harg2
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; exact hc0
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hi : i ∈ range N := by rw [Finset.mem_range] at hj ⊢; omega
        exact hihres i hi

/-- **Minimal-weight power representations are the binary digits.** Generalizes `binary_min_rep`
(the `n = 2^N − 1` case): if `∑_{j<N} c j · 2^j = n` with `n < 2^N` and the coefficient total is
minimal (`≤ pc n`), then every `c j` equals the `j`-th binary digit `n / 2^j % 2`. Equivalently, the
minimal-length representation of `n` over powers `< 2^N` is unique — its binary expansion. -/
lemma binary_rep_unique : ∀ (N : ℕ) (c : ℕ → ℕ) (n : ℕ),
    n < 2 ^ N → (∑ j ∈ range N, c j * 2 ^ j = n) → (∑ j ∈ range N, c j ≤ pc n) →
    ∀ j ∈ range N, c j = n / 2 ^ j % 2 := by
  intro N
  induction N with
  | zero => intro c n _ hsum _ j hj; simp at hj
  | succ N ih =>
      intro c n hn hsum hcard j hj
      rw [weighted_split N c] at hsum
      rw [card_split N c] at hcard
      set V := ∑ i ∈ range N, c (i + 1) * 2 ^ i with hVdef
      set W := ∑ i ∈ range N, c (i + 1) with hWdef
      have hprec := pc_rec n
      have hmwV : pc V ≤ W := by rw [hVdef, hWdef]; exact pc_sum_le N (fun i => c (i + 1))
      have hc0mod : c 0 % 2 = n % 2 := by omega
      obtain ⟨t, ht⟩ : ∃ t, c 0 = n % 2 + 2 * t := ⟨(c 0 - n % 2) / 2, by omega⟩
      have hVval : V = n / 2 - t := by omega
      have hVle : V + t = n / 2 := by omega
      have hlow : pc (n / 2) ≤ pc V + t := by rw [← hVle]; exact pc_add_le V t
      have ht0 : t = 0 := by omega
      have hc0 : c 0 = n % 2 := by omega
      have hVn2 : V = n / 2 := by omega
      have hWn2 : W ≤ pc (n / 2) := by omega
      have hn2 : n / 2 < 2 ^ N := by rw [pow_succ] at hn; omega
      have harg1 : ∑ i ∈ range N, c (i + 1) * 2 ^ i = n / 2 := by rw [← hVdef]; exact hVn2
      have harg2 : ∑ i ∈ range N, c (i + 1) ≤ pc (n / 2) := by rw [← hWdef]; exact hWn2
      have hihres := ih (fun i => c (i + 1)) (n / 2) hn2 harg1 harg2
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; rw [hc0]; simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hi : i ∈ range N := by rw [mem_range] at hj ⊢; omega
        rw [hihres i hi, Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-- **Binary-support card = popcount.** If a finite set `S` of (distinct, automatically) naturals has
`∑_{j∈S} 2^j = m`, then `|S| = pc m`. So *any* representation of `m` as a sum of distinct powers of two
has exactly `pc m` terms — there is only the binary one. Proof: strong induction on `m`, peeling the low
bit via [[pc_rec]] (`0 ∈ S ↔ m%2 = 1`, and `S' = (S.erase 0).image (·−1)` sums to `m/2`). Avoids the
circular use of [[binary_rep_unique]] (whose minimality hypothesis is exactly what is being shown). -/
lemma card_eq_pc : ∀ (m : ℕ) (S : Finset ℕ), (∑ j ∈ S, 2 ^ j = m) → S.card = pc m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hS
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hSe : S = ∅ := by
        rcases Finset.eq_empty_or_nonempty S with h | ⟨j, hj⟩
        · exact h
        · exfalso
          have h1 : 2 ^ j ≤ ∑ k ∈ S, 2 ^ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
          have h2 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
          omega
      subst hSe; simp
    · set T := S.erase 0 with hT
      have hTpos : ∀ j ∈ T, 1 ≤ j := fun j hj => by rw [hT, Finset.mem_erase] at hj; omega
      have hinj : ∀ a ∈ T, ∀ b ∈ T, a - 1 = b - 1 → a = b :=
        fun a ha b hb hab => by have := hTpos a ha; have := hTpos b hb; omega
      set S' := T.image (fun j => j - 1) with hS'
      have hQT : ∑ j ∈ S', 2 ^ j = ∑ j ∈ T, 2 ^ (j - 1) := by
        rw [hS', Finset.sum_image hinj]
      have hTsum : ∑ j ∈ T, 2 ^ j = 2 * ∑ j ∈ S', 2 ^ j := by
        rw [hQT, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj1 := hTpos j hj
        have hpow : 2 * 2 ^ (j - 1) = 2 ^ j := by rw [← pow_succ']; congr 1; omega
        exact hpow.symm
      have hsplit : (if 0 ∈ S then 1 else 0) + ∑ j ∈ T, 2 ^ j = m := by
        by_cases h0 : 0 ∈ S
        · simp only [h0, if_true]
          have := Finset.add_sum_erase S (fun j => 2 ^ j) h0
          simp only [pow_zero] at this; rw [hT, this]; exact hS
        · simp only [h0, if_false]
          rw [hT, Finset.erase_eq_of_notMem h0]; simpa using hS
      have hcardT : T.card = (if 0 ∈ S then S.card - 1 else S.card) := by
        by_cases h0 : 0 ∈ S
        · simp only [h0, if_true, hT, Finset.card_erase_of_mem h0]
        · simp only [h0, if_false, hT, Finset.erase_eq_of_notMem h0]
      have hcardS' : S'.card = T.card := by
        rw [hS', Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb)]
      -- m/2 = ∑_{S'} 2^j and m%2 = [0∈S]
      have hbit : m % 2 = (if 0 ∈ S then 1 else 0) := by
        have hb : (if 0 ∈ S then (1:ℕ) else 0) ≤ 1 := by by_cases h0 : 0 ∈ S <;> simp [h0]
        omega
      have hdiv : m / 2 = ∑ j ∈ S', 2 ^ j := by omega
      have hScard_pos : 1 ≤ S.card := by
        rcases Finset.eq_empty_or_nonempty S with h | h
        · subst h; simp at hS; omega
        · exact h.card_pos
      have hlt : ∑ j ∈ S', 2 ^ j < m := by omega
      have hih := ih (∑ j ∈ S', 2 ^ j) hlt S' rfl
      rw [pc_rec m, hdiv, ← hih, hbit, hcardS', hcardT]
      by_cases h0 : 0 ∈ S <;> simp [h0] ; omega

end LeanGallery.Combinatorics.Erdos880
