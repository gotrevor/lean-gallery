/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Basic
import LeanGallery.Combinatorics.Erdos1213.Counting
import LeanGallery.Combinatorics.Erdos1213.Analytic

/-!
Pigeonhole assembly:
* (3.7) `> D` blocks all with c-sum in `[1,D)` ⟹ two equal (contradicts `AllCSumsDistinct`)
        -- `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
* choose `A = ⌊e^{K+1}⌋` ⟹ the explicit bound. `hegyvari_thm3` lands here.
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

/-- **(3.7) Pigeonhole upper bound.**  If all c-sums are distinct and `a 1 ≥ 1`, the number of
blocks with c-sum `< D` is at most `D - 1`: each such block has a distinct c-sum lying in
`{1, …, D-1}`, a set of size `D - 1`. -/
theorem smallBlocks_card_le (a : ℕ → ℕ) (s D : ℕ) (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hdist : AllCSumsDistinct a s) :
    (smallBlocks a s D).card ≤ D - 1 := by
  -- map each block to its c-sum, landing injectively in `Icc 1 (D-1)`
  have hmaps : ∀ p : ℕ × ℕ, p ∈ smallBlocks a s D → csum a p.1 p.2 ∈ Finset.Icc 1 (D - 1) := by
    intro p hp
    simp only [smallBlocks, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hu1, hus⟩, _hv1, hvs⟩, huv, hlt⟩ := hp
    -- lower bound: `csum ≥ a p.1 ≥ a 1 ≥ 1`
    have hau : a 1 ≤ a p.1 := a_one_le hmono p.1 hu1 hus
    have hle : a p.1 ≤ csum a p.1 p.2 := by
      rw [csum]
      exact Finset.single_le_sum (f := a) (fun i _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨le_refl _, huv⟩)
    rw [Finset.mem_Icc]
    refine ⟨le_trans ha1 (le_trans hau hle), ?_⟩
    omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => csum a p.1 p.2) (smallBlocks a s D) := by
    intro p hp q hq hpq
    simp only [smallBlocks, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product,
      Finset.mem_Icc] at hp hq
    obtain ⟨⟨⟨hu1, _⟩, _, hvs⟩, huv, _⟩ := hp
    obtain ⟨⟨⟨hu1', _⟩, _, hvs'⟩, huv', _⟩ := hq
    simp only at hpq
    have := hdist p.1 p.2 q.1 q.2 hu1 huv hvs hu1' huv' hvs' hpq
    exact Prod.ext this.1 this.2
  have hcard := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => csum a p.1 p.2) hmaps hinj
  simpa [Nat.card_Icc] using hcard

/-- **Fitting condition.**  For `1 ≤ j ≤ A = ⌊e^{K+1}⌋` and an offset `i` below the real
threshold `lb j`, the block `(i+1, i+j)` lies inside `[1,s]`.  Uses `s ≥ (a_s − a₁)/K + 1`
(from `pointwise_bound`) together with `a_s ≥ L ≥ K·e^{2K+2} ≥ K·j` to show `i + j < s`. -/
theorem block_fits (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hbig : hegyvariBound a K ≤ (a s : ℝ))
    (j : ℕ) (hj : 1 ≤ j) (hjA : j ≤ ⌊Real.exp ((K : ℝ) + 1)⌋₊)
    (i : ℕ) (hi : (i : ℝ) < lb (a 1 : ℝ) (K : ℝ) (a s : ℝ) j) :
    i + j ≤ s := by
  simp only [lb] at hi
  -- Positivity helpers
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast show 0 < K by omega
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast show 0 < j by omega
  have hKjpos : (0 : ℝ) < (K : ℝ) * j := mul_pos hKpos hjpos
  -- Gap bound: a s ≤ a 1 + (s − 1)·K, cast to ℝ
  have hpb : a s ≤ a 1 + (s - 1) * K := by
    have h := pointwise_bound hgap (s - 1) (by omega)
    simpa [Nat.sub_add_cancel hs] using h
  have hpb_real : (a s : ℝ) ≤ (a 1 : ℝ) + ((s : ℝ) - 1) * (K : ℝ) := by
    have h : (a s : ℝ) ≤ (a 1 : ℝ) + ((s - 1 : ℕ) : ℝ) * K := by exact_mod_cast hpb
    simp only [Nat.cast_sub hs, Nat.cast_one] at h
    linarith
  -- Unpack the headline bound
  have hbig' : ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
      + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) ≤ (a s : ℝ) := by
    simpa [hegyvariBound] using hbig
  -- j ≤ e^{K+1}
  have hj_le_exp : (j : ℝ) ≤ Real.exp ((K : ℝ) + 1) :=
    calc (j : ℝ) ≤ (⌊Real.exp ((K : ℝ) + 1)⌋₊ : ℝ) := by exact_mod_cast hjA
      _ ≤ Real.exp ((K : ℝ) + 1) := Nat.floor_le (Real.exp_pos _ |>.le)
  -- K·j ≤ a s  (via K·j ≤ K·e^{K+1} ≤ K·e^{2K+2} ≤ a s)
  have hD_Kj : (K : ℝ) * j ≤ (a s : ℝ) := by
    have h_mono : Real.exp ((K : ℝ) + 1) ≤ Real.exp (2 * (K : ℝ) + 2) :=
      Real.exp_le_exp.mpr (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
    have h1 : (K : ℝ) * j ≤ (K : ℝ) * Real.exp ((K : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hj_le_exp (Nat.cast_nonneg _)
    have h2 : (K : ℝ) * Real.exp ((K : ℝ) + 1) ≤ (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left h_mono (Nat.cast_nonneg _)
    have h3 : (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) ≤ (a s : ℝ) := by
      nlinarith [Real.exp_pos ((K : ℝ) + 1), (Nat.cast_nonneg (a 1) : (0 : ℝ) ≤ (a 1 : ℝ))]
    linarith
  -- Cleared-denominator form of hi (via calc, avoiding ▸):
  -- i*(2*K*j) < 2*D - 2*a1*j - K*j*(j-1)
  have hmul : (i : ℝ) * (2 * (K : ℝ) * j) < 2 * (a s : ℝ) - 2 * (a 1 : ℝ) * j
      - (K : ℝ) * j * ((j : ℝ) - 1) :=
    calc (i : ℝ) * (2 * (K : ℝ) * j)
        < ((a s : ℝ) / ((K : ℝ) * j) - (a 1 : ℝ) / (K : ℝ) - ((j : ℝ) - 1) / 2)
            * (2 * (K : ℝ) * j) :=
          mul_lt_mul_of_pos_right hi (by linarith)
      _ = 2 * (a s : ℝ) - 2 * (a 1 : ℝ) * j - (K : ℝ) * j * ((j : ℝ) - 1) := by
          field_simp
  -- Key nonpositive product: (j-1) ≥ 0 and K*j - 2*D ≤ 0
  have hprod : ((j : ℝ) - 1) * ((K : ℝ) * j - 2 * (a s : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by linarith [show (1 : ℝ) ≤ j from by exact_mod_cast hj])
      (by linarith)
  -- Key product for combining: (j-1) * (D - a1 - (s-1)*K) ≤ 0  (≥0 × ≤0)
  have hprod2 : ((j : ℝ) - 1) * ((a s : ℝ) - (a 1 : ℝ) - ((s : ℝ) - 1) * K) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by linarith [show (1 : ℝ) ≤ j from by exact_mod_cast hj])
      (by linarith)
  -- Conclude (i : ℝ) + j < s by nlinarith, then cast to ℕ
  have hlt : (i : ℝ) + j < s := by
    have ha1_nn : (0 : ℝ) ≤ a 1 := Nat.cast_nonneg _
    have hi_nn : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    nlinarith [mul_pos hKjpos (show (0 : ℝ) < s by exact_mod_cast show 0 < s by omega)]
  have hlt_nat : i + j < s := by exact_mod_cast hlt
  omega

/-- **Counting lower bound.**  With `A = ⌊e^{K+1}⌋`, `D = a s`, and `a s ≥ L`, the number of
small-c-sum blocks is at least `a s`.  Chains the real lower bound `a s ≤ Σ lb j` (`sum_lb_ge_D`)
with the per-length count `lb j ≤ #offsetSet j` (`offsetSet_card_real_ge`, fed by `block_fits`). -/
theorem smallBlocks_card_ge_of_le (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (_hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap  : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hbig : hegyvariBound a K ≤ (a s : ℝ)) :
    a s ≤ ∑ j ∈ Finset.Icc 1 ⌊Real.exp ((K : ℝ) + 1)⌋₊, (offsetSet a s (a s) j).card := by
  set A := ⌊Real.exp ((K : ℝ) + 1)⌋₊ with hAdef
  -- per-length real lower bounds, summed
  have hpre : (∑ j ∈ Finset.Icc 1 A, lb (a 1 : ℝ) (K : ℝ) (a s : ℝ) j)
      ≤ ((∑ j ∈ Finset.Icc 1 A, (offsetSet a s (a s) j).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact offsetSet_card_real_ge hgap hK (a s) j hj.1
      (fun i hi => block_fits a s K hK hs hgap hbig j hj.1 hj.2 i hi)
  -- the analytic lower bound `a s ≤ Σ lb j`
  have hD' : ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
      + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) ≤ (a s : ℝ) := by
    simpa [hegyvariBound] using hbig
  have hge := sum_lb_ge_D K (a 1) A hK ha1 (a s : ℝ) hAdef hD'
  have : (a s : ℝ) ≤ ((∑ j ∈ Finset.Icc 1 A, (offsetSet a s (a s) j).card : ℕ) : ℝ) :=
    le_trans hge hpre
  exact_mod_cast this

/-- **HEADLINE — Hegyvári Thm 3.**  A strictly increasing sequence on `[1,s]` with gaps `≤ K` and all
consecutive-block sums distinct has last term below `L = (a₁ + K/2)·e^{K+1} + K·e^{2K+2}`.
(`1 ≤ a 1` is the paper's hypothesis that the sequence consists of positive integers.) -/
theorem hegyvari_thm3 (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap  : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hdist : AllCSumsDistinct a s) :
    (a s : ℝ) < hegyvariBound a K := by
  by_contra hcon
  push Not at hcon  -- hcon : hegyvariBound a K ≤ (a s : ℝ)
  set D := a s with hD
  -- `D ≥ 1` since `a s ≥ a 1 ≥ 1`
  have hD1 : 1 ≤ D := le_trans ha1 (a_one_le hmono s hs (le_refl s))
  -- lower bound: `D ≤ Σ_j #offsetSet ≤ #smallBlocks`
  have hlower : D ≤ ∑ j ∈ Finset.Icc 1 ⌊Real.exp ((K : ℝ) + 1)⌋₊, (offsetSet a s D j).card :=
    smallBlocks_card_ge_of_le a s K hK hs ha1 hmono hgap hcon
  have hmid : (∑ j ∈ Finset.Icc 1 ⌊Real.exp ((K : ℝ) + 1)⌋₊, (offsetSet a s D j).card)
      ≤ (smallBlocks a s D).card := sum_offsetSet_card_le a s D _
  -- upper bound: pigeonhole gives `#smallBlocks ≤ D - 1`
  have hupper : (smallBlocks a s D).card ≤ D - 1 := smallBlocks_card_le a s D ha1 hmono hdist
  omega

/-! ## Optional (step 6): `f(a,K)` as a supremum, bounded by `L`

`hegyvariF init K` is the paper's `f(a,K)`: the supremum of last terms of valid sequences.
We prove `hegyvariF init K ≤ hegyvariBound (fun _ => init) K` as a corollary.
-/

/-- The set of achievable last terms for starting value `a₁ = init`, gap bound `K`. -/
def validLastTerms (init K : ℕ) : Set ℕ :=
  {n | ∃ (s : ℕ) (seq : ℕ → ℕ), seq 1 = init ∧ 1 ≤ s ∧ seq s = n ∧
    (∀ i, 1 ≤ i → i < s → seq i < seq (i + 1)) ∧
    (∀ i, 1 ≤ i → i < s → seq (i + 1) ≤ seq i + K) ∧
    AllCSumsDistinct seq s}

/-- `f(a,K)` from the paper: the supremum of last terms of strictly-increasing sequences with first
term `a₁ = init`, gaps `≤ K`, and all consecutive-block sums distinct. -/
noncomputable def hegyvariF (init K : ℕ) : ℕ := sSup (validLastTerms init K)

/-- Every achievable last term lies strictly below the headline constant `L`. -/
theorem validLastTerms_lt_bound (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init)
    {n : ℕ} (hn : n ∈ validLastTerms init K) :
    (n : ℝ) < hegyvariBound (fun _ => init) K := by
  obtain ⟨s, seq, hseq1, hs, hseqn, hmono, hgap, hdist⟩ := hn
  have ha1 : 1 ≤ seq 1 := hseq1 ▸ ha
  have hlt := hegyvari_thm3 seq s K hK hs ha1 hmono hgap hdist
  -- unfold the bound in BOTH hlt and the goal so linarith sees a common form
  -- (`hegyvariBound seq K` and `hegyvariBound (fun _ => init) K` agree since `seq 1 = init`)
  simp only [hegyvariBound, hseq1] at hlt ⊢
  -- hlt : (seq s : ℝ) < ...,  hseqn : seq s = n
  have : (n : ℝ) = seq s := by exact_mod_cast hseqn.symm
  linarith

/-- **`f(a,K) ≤ L`** — Hegyvári Thm 3, supremum form.  The paper's `f` is finite and bounded
by `L = (a₁ + K/2)·e^{K+1} + K·e^{2K+2}`. -/
theorem hegyvariF_le_bound (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init) :
    (hegyvariF init K : ℝ) ≤ hegyvariBound (fun _ => init) K := by
  unfold hegyvariF
  -- Nonemptiness: the constant-init sequence (s=1) is valid
  have hne : (validLastTerms init K).Nonempty :=
    ⟨init, 1, fun _ => init, rfl, le_refl 1, rfl,
      fun _ h1 h2 => by omega, fun _ h1 h2 => by omega,
      fun _ _ _ _ hu1 _ hv1s _ _ hv2s _ => ⟨by omega, by omega⟩⟩
  -- Bound: L > 0
  have hLpos : (0 : ℝ) ≤ hegyvariBound (fun _ => init) K := by
    simp only [hegyvariBound]; positivity
  -- Every element is ≤ ⌊L⌋₊ as a ℕ (via floor monotonicity: n ≤ floor(n) ≤ floor(L))
  have hle : sSup (validLastTerms init K) ≤ ⌊hegyvariBound (fun _ => init) K⌋₊ :=
    csSup_le hne fun n hn => by
      have hlt := validLastTerms_lt_bound init K hK ha hn
      -- (n : ℝ) < L → n ≤ ⌊L⌋₊, via floor monotonicity
      have h1 : n = ⌊(n : ℝ)⌋₊ := (Nat.floor_natCast n).symm
      exact h1 ▸ Nat.floor_mono (le_of_lt hlt)
  -- Cast and use ⌊L⌋₊ ≤ L
  exact le_trans (by exact_mod_cast hle) (Nat.floor_le hLpos)

end LeanGallery.Combinatorics.Erdos1213
