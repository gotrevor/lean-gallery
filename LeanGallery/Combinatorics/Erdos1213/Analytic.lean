/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Counting

/-!
The real-analysis bridge for Hegyvári Thm 3 (steps 3.6 + the §3 optimization).

The per-length real lower bound on the offset count is
`lb j := D/(K·j) − a₁/K − (j−1)/2`  (`(j-1)/2`, sharper than the paper's `j/2`, from the tight
`block_sum_bound`).  Summing over `j ∈ [1,A]` gives a closed form via the harmonic number, and the
"optimize `A = ⌊e^{K+1}⌋`" step shows that closed form is `≥ D` once `D ≥ L`.
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

/-- The per-length real lower bound `lb j = D/(K·j) − a₁/K − (j−1)/2`. -/
noncomputable def lb (a1 K : ℝ) (D : ℝ) (j : ℕ) : ℝ :=
  D / (K * j) - a1 / K - ((j : ℝ) - 1) / 2

private lemma sum_sub_one (A : ℕ) :
    ∑ j ∈ Finset.Icc 1 A, ((j : ℝ) - 1) = (A : ℝ) * ((A : ℝ) - 1) / 2 := by
  induction A with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

/-- **Closed form for `Σ_{j=1}^A lb j`** via the harmonic number `H_A = Σ 1/j`:
`Σ lb j = (D/K)·H_A − A·a₁/K − A(A−1)/4`. -/
theorem sum_lb_eq (a1 K D : ℝ) (hK : K ≠ 0) (A : ℕ) :
    ∑ j ∈ Finset.Icc 1 A, lb a1 K D j
      = (D / K) * (harmonic A : ℝ) - (A : ℝ) * a1 / K - (A : ℝ) * ((A : ℝ) - 1) / 4 := by
  simp only [lb]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- the three pieces
  have h1 : ∑ j ∈ Finset.Icc 1 A, D / (K * (j : ℝ)) = (D / K) * (harmonic A : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjne : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
  have h2 : ∑ j ∈ Finset.Icc 1 A, a1 / K = (A : ℝ) * a1 / K := by
    rw [Finset.sum_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    ring
  have h3 : ∑ j ∈ Finset.Icc 1 A, ((j : ℝ) - 1) / 2 = (A : ℝ) * ((A : ℝ) - 1) / 4 := by
    have : ∑ j ∈ Finset.Icc 1 A, ((j : ℝ) - 1) / 2
        = (∑ j ∈ Finset.Icc 1 A, ((j : ℝ) - 1)) / 2 := by
      rw [Finset.sum_div]
    rw [this, sum_sub_one]; ring
  rw [h1, h2, h3]

/-- **Optimization step (§3, `A = ⌊e^{K+1}⌋`).**  `S' := (D/K)·H_A − A(a+K/2)/K − (A+2)²/4 ≥ D`
once `D` exceeds the headline constant `L`.  Proof sketch (elementary real analysis): `H_A ≥
log(A+1) > K+1` so `H_A − K ≥ 1`; `A ≤ e^{K+1}` and `e^{K+1} ≥ 2` give `A(a+K/2)+K(A+2)²/4 ≤ L`;
then `K(S'−D) = D(H_A−K) − A(a+K/2) − K(A+2)²/4 ≥ D − L ≥ 0`.
Proof ported from Aristotle (project 07edceec / task 24d53d6d), verified in-kernel + axiom-clean. -/
private lemma exp_K1_ge_two (K : ℕ) :
    (2 : ℝ) ≤ Real.exp ((K : ℝ) + 1) := by
  linarith [Real.add_one_le_exp (K + 1)]

private lemma harmonic_gt_K1 (K A : ℕ)
    (hA : A = ⌊Real.exp ((K : ℝ) + 1)⌋₊) :
    (K : ℝ) + 1 < (harmonic A : ℝ) := by
  have h_log : Real.log (A + 1) > K + 1 := by
    exact Real.lt_log_iff_exp_lt (by positivity) |>.2
      (by linarith [Nat.lt_floor_add_one (Real.exp (K + 1)),
        show (A : ℝ) = ⌊Real.exp (K + 1)⌋₊ by exact_mod_cast hA])
  have h2 : Real.log ((A : ℝ) + 1) ≤ (harmonic A : ℝ) := by
    have h := log_add_one_le_harmonic A
    rwa [Nat.cast_add_one] at h
  linarith

private lemma A_plus2_sq_le (K A : ℕ)
    (hA : A = ⌊Real.exp ((K : ℝ) + 1)⌋₊) :
    ((A : ℝ) + 2) ^ 2 ≤ 4 * Real.exp (2 * (K : ℝ) + 2) := by
  exact le_trans
    (pow_le_pow_left₀ (by positivity)
      (show (A : ℝ) + 2 ≤ 2 * Real.exp (K + 1) from by
        nlinarith [Real.add_one_le_exp (K + 1),
          show (A : ℝ) ≤ Real.exp (K + 1) from
            hA ▸ Nat.floor_le (Real.exp_pos _ |> le_of_lt)]) 2)
    (by rw [mul_pow]; rw [← Real.exp_nat_mul]; ring_nf; norm_num)

theorem opt_bound (K a A : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ a) (D : ℝ)
    (hA : A = ⌊Real.exp ((K : ℝ) + 1)⌋₊)
    (hD : ((a : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
            + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) ≤ D) :
    D ≤ (D / (K : ℝ)) * (harmonic A : ℝ)
          - (A : ℝ) * ((a : ℝ) + (K : ℝ) / 2) / (K : ℝ)
          - ((A : ℝ) + 2) ^ 2 / 4 := by
  have h_harmonic_minus_K_gt_1 : harmonic A - K > 1 := by
    have := harmonic_gt_K1 K A hA
    rw [gt_iff_lt, lt_sub_iff_add_lt]; norm_cast at *
    rwa [add_comm]
  have h_K_A_plus2_sq_le_K_exp :
      (K : ℝ) * ((A : ℝ) + 2) ^ 2 / 4 ≤ (K : ℝ) * Real.exp (2 * K + 2) := by
    nlinarith [A_plus2_sq_le K A hA, (Nat.cast_nonneg K : (0:ℝ) ≤ (K:ℝ)), sq_nonneg ((A : ℝ) + 2)]
  have h_A_le_exp : (A : ℝ) ≤ Real.exp (K + 1) := by
    exact hA ▸ Nat.floor_le (by positivity)
  have h_D_harmonic_minus_K_ge_D : D * (harmonic A - K) ≥ D := by
    have h_D_nonneg : 0 ≤ D := le_trans (by positivity) hD
    exact le_mul_of_one_le_right h_D_nonneg (mod_cast h_harmonic_minus_K_gt_1.le)
  field_simp at *
  nlinarith [(by norm_cast : (1 : ℝ) ≤ K), (by norm_cast : (1 : ℝ) ≤ a)]

/-- **`Σ_{j=1}^A lb j ≥ D`** once `D ≥ L`, with `A = ⌊e^{K+1}⌋`.  Combines the closed form
`sum_lb_eq` with `opt_bound`: the sharper `lb` (using `(j−1)/2`) overshoots `S'` by `(7A+4)/4 ≥ 0`. -/
theorem sum_lb_ge_D (K a A : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ a) (D : ℝ)
    (hA : A = ⌊Real.exp ((K : ℝ) + 1)⌋₊)
    (hD : ((a : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
            + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) ≤ D) :
    D ≤ ∑ j ∈ Finset.Icc 1 A, lb (a : ℝ) (K : ℝ) D j := by
  have hKne : (K : ℝ) ≠ 0 := by positivity
  rw [sum_lb_eq (a : ℝ) (K : ℝ) D hKne A]
  have hopt := opt_bound K a A hK ha D hA hD
  -- `Σlb_closed = S' + (7A+4)/4`, and `(7A+4)/4 ≥ 0`
  have hgap : (D / (K : ℝ)) * (harmonic A : ℝ) - (A : ℝ) * (a : ℝ) / (K : ℝ)
        - (A : ℝ) * ((A : ℝ) - 1) / 4
      = ((D / (K : ℝ)) * (harmonic A : ℝ) - (A : ℝ) * ((a : ℝ) + (K : ℝ) / 2) / (K : ℝ)
          - ((A : ℝ) + 2) ^ 2 / 4) + (7 * (A : ℝ) + 4) / 4 := by
    field_simp
    ring
  rw [hgap]
  have hAnn : (0 : ℝ) ≤ (7 * (A : ℝ) + 4) / 4 := by positivity
  linarith

/-- **Per-length real lower bound on the offset count.**  For `1 ≤ j` and a fitting hypothesis
(every offset `i` below the real threshold `lb j` keeps the block inside `[1,s]`), the offset count
is at least `lb j` (as a real): the offsets `0,…,⌈lb j⌉−1` all satisfy the block-sum threshold (which
is *exactly* `i < lb j`) and fit, so `⌈lb j⌉ ≤ #offsetSet`. -/
theorem offsetSet_card_real_ge {a : ℕ → ℕ} {s K : ℕ}
    (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K) (hK : 1 ≤ K)
    (D j : ℕ) (hj : 1 ≤ j)
    (hfit : ∀ i : ℕ, (i : ℝ) < lb (a 1 : ℝ) (K : ℝ) (D : ℝ) j → i + j ≤ s) :
    lb (a 1 : ℝ) (K : ℝ) (D : ℝ) j ≤ ((offsetSet a s D j).card : ℝ) := by
  set L := lb (a 1 : ℝ) (K : ℝ) (D : ℝ) j with hL
  by_cases hLpos : 0 < L
  case neg =>
    push Not at hLpos
    exact le_trans hLpos (by positivity)
  -- key: the integer threshold for offset `i` is *equivalent* to `(i:ℝ) < L`
  have hKjpos : (0 : ℝ) < (K : ℝ) * j := by positivity
  have hjne : (j : ℝ) ≠ 0 := by positivity
  have hKne : (K : ℝ) ≠ 0 := by positivity
  have harith : ∀ i : ℕ, (i : ℝ) < L →
      2 * j * a 1 + K * (2 * i * j + j * (j - 1)) < 2 * D := by
    intro i hi
    rw [hL, lb] at hi
    -- multiply the threshold by `2Kj > 0` and simplify the RHS
    have hKj2 : (0 : ℝ) < 2 * (K : ℝ) * j := by positivity
    have hmul := mul_lt_mul_of_pos_right hi hKj2
    have hrhs : ((D : ℝ) / ((K : ℝ) * j) - (a 1 : ℝ) / K - ((j : ℝ) - 1) / 2) * (2 * (K : ℝ) * j)
        = 2 * D - 2 * j * a 1 - K * j * ((j : ℝ) - 1) := by
      field_simp
    rw [hrhs] at hmul
    -- now an integer inequality after casting `(j-1)`
    have hjcast : ((j : ℝ) - 1) = ((j - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hj]; norm_num
    have hreal : ((2 * j * a 1 + K * (2 * i * j + j * (j - 1)) : ℕ) : ℝ) < ((2 * D : ℕ) : ℝ) := by
      push_cast [hjcast] at hmul ⊢
      nlinarith [hmul]
    exact_mod_cast hreal
  -- with `m = ⌈L⌉₊`, both obligations of `offsetSet_card_ge` hold
  set m := ⌈L⌉₊ with hm
  have hmle : m ≤ (offsetSet a s D j).card := by
    apply offsetSet_card_ge hgap D j m
    · intro i hi
      have : (i : ℝ) < L := by rw [hm] at hi; exact (Nat.lt_ceil).mp hi
      exact hfit i this
    · intro i hi
      have : (i : ℝ) < L := by rw [hm] at hi; exact (Nat.lt_ceil).mp hi
      exact harith i this
  calc L ≤ (m : ℝ) := Nat.le_ceil L
    _ ≤ ((offsetSet a s D j).card : ℝ) := by exact_mod_cast hmle

end LeanGallery.Combinatorics.Erdos1213
