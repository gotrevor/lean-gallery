/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.GeneralResidue
import LeanGallery.NumberTheory.Erdos1050.GeneralNumerator
import LeanGallery.NumberTheory.Erdos1050.General
import LeanGallery.NumberTheory.Erdos1050.Lemma3

/-!
# Borwein Lemma 3 (numerator integrality) — general `(q, C)` engine

Ports the `q = 2, C = 8/3` Lemma-3 assembly (`Lemma3.lean`) to general integer `q ≥ 2` and rational
`C = α/β`. The target is `AcorrG_int`: `∃ a : ℤ, (a : ℝ) = −(β^{2n}·Wₙ(C,q)·AcorrG n)`, i.e. the
rational correction of the residue identity clears to an integer once scaled by `β^{2n}·Wₙ`.

The route mirrors the `q = 2` one exactly (it is ~mechanical, per the lap-6 heuristic):
1. **reorg** `AcorrG n` into a `muW`-free Rrat-part (Gaussian binomials via q-Lagrange) plus a headS-part
   `∑_{h=1}^n u_h·N_h` with `N_h = NhG (q) n h` the q-Lagrange combination;
2. **clear** each part by `β^{2n}·Wₙ` = `WIG` (an integer): the Rrat-part via `RratG_int` + `borwein_div`,
   the headS-part via `uClearIntG` (clears `u_h` by `CPintG`'s `(β−α·q^h)` factor) and `NhG_int`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-! ## Section 1: reorganizing `AcorrG`'s headS-part (pure real-`q` algebra) -/

/-- `headSG` with the inner range sum reindexed to `Icc 1 (n+j−1)` (set `h = m'+1`). -/
lemma headSG_Icc (q C : ℝ) (i j n : ℕ) :
    headSG q C i j n = ∑ h ∈ Finset.Icc 1 (n + j - 1), (q ^ (i * h))⁻¹ * (1 - C * q ^ h)⁻¹ := by
  rw [headSG, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro m' _
  rw [Nat.add_comm 1 m']

/-- **Subset-product collapse** (signed, with a scalar `w`): `∑_{t⊆[1,m]} (∏_{k∈t}-q^k)·w^{|t|}
= ∏_{k=1}^m (1 - q^k·w)`. The engine of the headS reorganization. -/
lemma subset_prod_localG (q w : ℝ) (m : ℕ) :
    ∑ t ∈ (Finset.Icc 1 m).powerset, (∏ k ∈ t, (-q ^ k)) * w ^ t.card
      = ∏ k ∈ Finset.Icc 1 m, (1 - q ^ k * w) := by
  have hf : ∀ k, (1 : ℝ) - q ^ k * w = 1 + (-q ^ k) * w := by intro k; ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- `q^{t·j}·(q^{t·h})⁻¹ = (q^{j−h})^t` (mixing nat powers and a zpow base). -/
lemma wpowG {q : ℝ} (hq0 : q ≠ 0) (j h t : ℕ) :
    (q ^ (t * j) : ℝ) * (q ^ (t * h))⁻¹ = (q ^ ((j : ℤ) - h)) ^ t := by
  rw [← zpow_natCast (q ^ ((j : ℤ) - h)) t, ← zpow_mul, ← zpow_natCast q (t * j),
    ← zpow_natCast q (t * h), ← zpow_neg, ← zpow_add₀ hq0]
  congr 1
  push_cast; ring

/-- **Per-`j` headS reorganization.** Summing the subset `t ⊆ [1,n−1]` first collapses the headS-part
into a single product `∏_{k=1}^{n−1}(1−q^{k+j−h})` over the head index `h`. -/
lemma headPartG_inner {q : ℝ} (C : ℝ) (hq0 : q ≠ 0) (n j : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-q ^ k)) * (q ^ (t.card * j) * headSG q C t.card j n)
      = ∑ h ∈ Finset.Icc 1 (n + j - 1),
        (1 - C * q ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  have hstep : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset,
      (∏ k ∈ t, (-q ^ k)) * (q ^ (t.card * j) * headSG q C t.card j n)
        = ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - C * q ^ h)⁻¹ * ((∏ k ∈ t, (-q ^ k)) * (q ^ ((j : ℤ) - h)) ^ t.card) := by
    intro t _
    rw [headSG_Icc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← wpowG hq0 j h t.card]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ k * q ^ ((j : ℤ) - h)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [← zpow_natCast q k, ← zpow_add₀ hq0]
    congr 2
    ring
  rw [hprod, ← subset_prod_localG q (q ^ ((j : ℤ) - h)) (n - 1), Finset.mul_sum]

/-- The full headS-part of `AcorrG`, reorganized: pull `muWG n j` out and apply `headPartG_inner`. -/
lemma AccHG_reorg {q : ℝ} (C : ℝ) (hq0 : q ≠ 0) (n : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * headSG q C t.card j n)
      = ∑ j ∈ Finset.Icc 1 n, muWG q n j *
          ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - C * q ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← headPartG_inner C hq0 n j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **`AcorrG` reorganized** into its Rrat-part (first sum) and the reorganized headS-part (second
sum). -/
lemma AcorrG_reorg {q : ℝ} (C : ℝ) (hq0 : q ≠ 0) (n : ℕ) :
    AcorrG q C n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                  (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * RratG q C t.card))
              + ∑ j ∈ Finset.Icc 1 n, muWG q n j *
                  ∑ h ∈ Finset.Icc 1 (n + j - 1),
                    (1 - C * q ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  have key : (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * RratG q C t.card))
              - (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * headSG q C t.card j n))
            = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-q ^ k)) * muWG q n j
                  * (q ^ (t.card * j) * (RratG q C t.card - headSG q C t.card j n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [AcorrG, ← key, AccHG_reorg C hq0]
  abel

/-! ## Section 2: head truncation + q-Lagrange clearing → `AcorrG_clean` -/

/-- **Rrat-part via q-Lagrange** (integer `q ≥ 2`). Each `t`-term's `j`-sum
`∑_j μ_j (q^j)^{|t|}` is the Gaussian binomial `q^{|t|}·[n+|t|−1,n−1]_q` (`qLagG`, valid as
`|t| ≤ n−1 < n`), eliminating the Vandermonde `muWG` denominators. -/
lemma RratPartG_qLag {q : ℤ} (hq : 2 ≤ |q|) (C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-(q : ℝ) ^ k)) * muWG (q : ℝ) n j
          * ((q : ℝ) ^ (t.card * j) * RratG (q : ℝ) C t.card)
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) C t.card
            * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1
    omega
  have hpull : ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-(q : ℝ) ^ k)) * muWG (q : ℝ) n j
          * ((q : ℝ) ^ (t.card * j) * RratG (q : ℝ) C t.card)
      = (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) C t.card
          * ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ t.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm j t.card]; ring
  rw [hpull, qLagG_abs hq hn t.card hcard]

/-- **headS-part in `N_h` form** (integer `q`). After truncation (`head_truncate`) the (j,h)-sum swaps
and the inner `j`-sum extends to `[1,n]` (added `j<h` terms vanish by `prod_vanishG`), exposing the
q-Lagrange combination `N_h = ∑_j μ_j ∏_{k=1}^{n−1}(1−q^{k+j−h})`. -/
lemma headSPartG_NhForm {q : ℤ} (C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j *
        ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - C * (q : ℝ) ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 n, (1 - C * (q : ℝ) ^ h)⁻¹ *
          ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
            * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  have h1 : ∀ j ∈ Finset.Icc 1 n,
      muWG (q : ℝ) n j * ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - C * (q : ℝ) ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))
        = ∑ h ∈ Finset.Icc 1 j,
            muWG (q : ℝ) n j * ((1 - C * (q : ℝ) ^ h)⁻¹
              * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) := by
    intro j _
    rw [head_truncate (q : ℝ) (fun h => (1 - C * (q : ℝ) ^ h)⁻¹) n j hn, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (s := Finset.Icc 1 n) (t := fun j => Finset.Icc 1 j)
        (t' := Finset.Icc 1 n) (s' := fun h => Finset.Icc h n)
        (by intro j h
            show (j ∈ Finset.Icc 1 n ∧ h ∈ Finset.Icc 1 j)
              ↔ (j ∈ Finset.Icc h n ∧ h ∈ Finset.Icc 1 n)
            simp only [Finset.mem_Icc]; omega)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : (1 : ℕ) ≤ h))]
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j hj hjh
    rw [Finset.mem_Icc] at hj hjh
    have : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) = 0 :=
      prod_vanishG (by omega) (by omega) hh.2
    rw [this]; ring

/-- **`AcorrG` in clean form** (integer `q ≥ 2`, `C` real): the Rrat-part is now `muWG`-free
(Gaussian binomials), and the headS-part is `∑_{h=1}^n u_h·N_h` with `N_h = NhG q n h`. This is the
structural target of the elementary Lemma-3 route, ported to general `(q, C)`. -/
theorem AcorrG_clean {q : ℤ} (hq : 2 ≤ |q|) (C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    AcorrG (q : ℝ) C n
      = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) C t.card
              * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)))
        + ∑ h ∈ Finset.Icc 1 n, (1 - C * (q : ℝ) ^ h)⁻¹ *
            ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
              * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have hqz : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; exact absurd hq (by norm_num)
    exact_mod_cast hqz
  rw [AcorrG_reorg C hq0 n, RratPartG_qLag hq C n hn, headSPartG_NhForm C n hn]

/-! ## Section 3: the integer clearing factor `β^{2n}·Wₙ = WIG` and the numerator integrality -/

/-- The cleared **integer** form of `β^{2n}·Wₙ(C,q)`, `C = α/β`: since `β^n·∏(1−C·qᵏ) = CPintG` and
`∏(1−qᵏ) = QPintG`, this is `β^n·(n−2)!·CPintG·QPintG ∈ ℤ`. (Generalizes `WI`, the `q=2,C=8/3` case.) -/
def WIG (q α β : ℤ) (n : ℕ) : ℤ :=
  β ^ n * (Nat.factorial (n - 2)) * CPintG q α β n * QPintG q n

/-- `(WIG q α β n : ℝ) = β^{2n}·Wₙ(α/β,q)`: the clearing factor is a machine-checked integer. -/
lemma WIG_cast (q α β : ℤ) (hβ : β ≠ 0) (n : ℕ) :
    (WIG q α β n : ℝ) = (β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  rw [WIG, WtermG]
  push_cast
  rw [CPintG_cast q α β hβ, QPintG_cast q]
  have hb : (β : ℝ) ^ (2 * n) = (β : ℝ) ^ n * (β : ℝ) ^ n := by rw [← pow_add]; congr 1; omega
  rw [hb]; ring

/-- `(q^l − 1)` divides `QPintG q n` for `1 ≤ l ≤ n−1` (Borwein's note, via `borwein_div`). -/
lemma QPintG_dvd {q : ℤ} {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n - 1) :
    (q ^ l - 1) ∣ QPintG q n := by
  have h := borwein_div q n l hl (by omega)
  rw [QPintG]
  have hsign : (q ^ l - 1) = -(1 - q ^ l) := by ring
  rw [hsign]
  exact h.neg_left

/-- The integer witness for `β^{2n}·Wₙ·(C^{i−l}/(q^l−1))`: clears `α^{i−l}` by `β` and `q^l−1` by
`QPintG` (via `QPintG_dvd`). -/
def RratTermIntG (q α β : ℤ) (n i l : ℕ) : ℤ :=
  α ^ (i - l) * β ^ (n - (i - l)) * (Nat.factorial (n - 2)) * CPintG q α β n * (QPintG q n / (q ^ l - 1))

/-- **Per-term Rrat clearing**: `(RratTermIntG q α β n i l : ℝ) = WIG · (C^{i−l}/(q^l−1))` for
`1 ≤ l ≤ i ≤ n−1`. -/
lemma RratTermIntG_cast {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) {n i l : ℕ}
    (hl1 : 1 ≤ l) (hli : l ≤ i) (hin : i ≤ n - 1) :
    (RratTermIntG q α β n i l : ℝ)
      = (WIG q α β n : ℝ) * (((α : ℝ) / (β : ℝ)) ^ (i - l) / ((q : ℝ) ^ l - 1)) := by
  obtain ⟨d, hd⟩ := QPintG_dvd (q := q) hl1 (by omega : l ≤ n - 1)
  -- `q^l ≠ 1` since `|q^l| = |q|^l ≥ |q| ≥ 2 > 1` (works for both signs of `q`).
  have hne : (q ^ l - 1 : ℤ) ≠ 0 := by
    have habs : (2 : ℤ) ≤ |q ^ l| := by
      rw [abs_pow]
      calc (2 : ℤ) ≤ |q| := hq
        _ = |q| ^ 1 := (pow_one _).symm
        _ ≤ |q| ^ l := pow_le_pow_right₀ (by linarith) hl1
    have hne1 : (q ^ l : ℤ) ≠ 1 := by intro h; rw [h] at habs; norm_num at habs
    exact sub_ne_zero.mpr hne1
  have hdiv : QPintG q n / (q ^ l - 1) = d := by rw [hd]; exact Int.mul_ediv_cancel_left d hne
  have hqR : ((q : ℝ) ^ l - 1) ≠ 0 := by
    have hq2 : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
    have hgt : (1 : ℝ) < |(q : ℝ)| ^ l := by
      calc (1 : ℝ) < 2 := by norm_num
        _ ≤ |(q : ℝ)| := hq2
        _ = |(q : ℝ)| ^ 1 := (pow_one _).symm
        _ ≤ |(q : ℝ)| ^ l := pow_le_pow_right₀ (by linarith) hl1
    intro h; rw [sub_eq_zero] at h
    have hone : |(q : ℝ) ^ l| = 1 := by rw [h]; norm_num
    rw [abs_pow] at hone; linarith
  have hQ : (QPintG q n : ℝ) = ((q : ℝ) ^ l - 1) * (d : ℝ) := by
    have h1 : (QPintG q n : ℝ) = (((q ^ l - 1) * d : ℤ) : ℝ) := by rw [← hd]
    rw [h1]; push_cast; ring
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hbsplit : (β : ℝ) ^ n = (β : ℝ) ^ (i - l) * (β : ℝ) ^ (n - (i - l)) := by
    rw [← pow_add]; congr 1; omega
  rw [RratTermIntG, hdiv, WIG]
  push_cast
  rw [hQ, hbsplit, div_pow]
  field_simp

/-- Per-`t` integer witness for the whole Rrat-part of `AcorrG_clean`. -/
def RratCleanTermIntG (q α β : ℤ) (n : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-q ^ k)) * (q ^ t.card * qBin q (n + t.card - 1) (n - 1))
    * (∑ l ∈ Finset.Icc 1 t.card, RratTermIntG q α β n t.card l)

/-- Each Rrat-part `t`-term, times `β^{2n}·Wₙ`, is the integer `RratCleanTermIntG`. -/
lemma RratCleanTermIntG_cast {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) {n : ℕ} {t : Finset ℕ}
    (ht : t ∈ (Finset.Icc 1 (n - 1)).powerset) :
    (RratCleanTermIntG q α β n t : ℝ) = (WIG q α β n : ℝ) *
      ((∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) t.card
        * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1))) := by
  have hcard : t.card ≤ n - 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have hqr1 : (1 : ℝ) < |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by linarith : (1 : ℤ) < |q|)
  have e1 : ((∏ k ∈ t, (-q ^ k) : ℤ) : ℝ) = ∏ k ∈ t, (-(q : ℝ) ^ k) := by
    rw [Int.cast_prod]; apply Finset.prod_congr rfl; intro k _; push_cast; ring
  have e4 : ((∑ l ∈ Finset.Icc 1 t.card, RratTermIntG q α β n t.card l : ℤ) : ℝ)
      = (WIG q α β n : ℝ) * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) t.card := by
    rw [RratG_closed hqr1, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_Icc] at hl
    exact RratTermIntG_cast hq hβ hl.1 hl.2 hcard
  have hqb : qBin ((q : ℤ) : ℝ) (n + t.card - 1) (n - 1)
      = ((qBin q (n + t.card - 1) (n - 1) : ℤ) : ℝ) :=
    qBin_map (Int.castRingHom ℝ) q (n + t.card - 1) (n - 1)
  have e3 : ((q ^ t.card * qBin q (n + t.card - 1) (n - 1) : ℤ) : ℝ)
      = (q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1) := by
    rw [hqb]; push_cast; ring
  rw [RratCleanTermIntG, Int.cast_mul, Int.cast_mul, e4, e1, e3]
  ring

/-- **Rrat-part integrality.** `β^{2n}·Wₙ · (Rrat-part of `AcorrG_clean`) ∈ ℤ`. -/
lemma WIG_mul_RratClean_int {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) (n : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (WIG q α β n : ℝ) * ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) t.card
          * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, RratCleanTermIntG q α β n t, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact RratCleanTermIntG_cast hq hβ ht

/-- `CPintG` with its `h`-th factor `(β − α·q^h)` removed (`h ∈ [1,n]`). -/
def CPdropG (q α β : ℤ) (n h : ℕ) : ℤ := ∏ k ∈ (Finset.Icc 1 n).erase h, (β - α * q ^ k)

/-- `(β − α·q^h)·CPdropG = CPintG` for `h ∈ [1,n]`. -/
lemma CPintG_factor {q α β : ℤ} {n h : ℕ} (hh : h ∈ Finset.Icc 1 n) :
    (β - α * q ^ h) * CPdropG q α β n h = CPintG q α β n :=
  Finset.mul_prod_erase (Finset.Icc 1 n) (fun k => β - α * q ^ k) hh

/-- The integer witness for `β^{2n}·Wₙ·u_h = β^{n+1}·(n−2)!·QPintG·CPdropG`. -/
def uClearIntG (q α β : ℤ) (n h : ℕ) : ℤ :=
  β ^ (n + 1) * (Nat.factorial (n - 2)) * QPintG q n * CPdropG q α β n h

/-- **`u_h` clearing**: `(uClearIntG q α β n h : ℝ) = β^{2n}·Wₙ·(1−C·q^h)⁻¹` for `1 ≤ h ≤ n`, where
`C = α/β` and `C·q^h ≠ 1` (so the `(β − α·q^h)` factor of `CPintG` clears the `u_h` denominator). -/
lemma uClearIntG_cast {q α β : ℤ} (hβ : β ≠ 0) {n h : ℕ} (hh1 : 1 ≤ h) (hhn : h ≤ n)
    (hCh : ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1) :
    (uClearIntG q α β n h : ℝ)
      = (WIG q α β n : ℝ) * (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)⁻¹ := by
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hmem : h ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hh1, hhn⟩
  have hfac : (β - α * q ^ h) * CPdropG q α β n h = CPintG q α β n := CPintG_factor hmem
  have hu0 : (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h) ≠ 0 := sub_ne_zero.mpr (Ne.symm hCh)
  have hne : ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) ≠ 0 := by
    have hb : ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h)
        = (β : ℝ) * (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h) := by field_simp
    rw [hb]; exact mul_ne_zero hβ0 hu0
  have hu : (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)⁻¹
      = (β : ℝ) / ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) := by
    rw [show (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)
          = ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) / (β : ℝ) from by field_simp, inv_div]
  have hCP : (CPintG q α β n : ℝ)
      = ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) * (CPdropG q α β n h : ℝ) := by
    rw [← hfac]; push_cast; ring
  rw [uClearIntG, WIG]
  push_cast
  rw [hu, hCP]
  field_simp
  ring

/-- **headS-part integrality**, given integer witnesses `Nz h = N_h` and non-degeneracy `C·q^h ≠ 1`.
`β^{2n}·Wₙ·(headS-part) = ∑_h (β^{2n}·Wₙ·u_h)·N_h = ∑_h uClearIntG·Nz h ∈ ℤ`. -/
lemma WIG_mul_headS_int {q α β : ℤ} (hβ : β ≠ 0) (n : ℕ)
    (hCn : ∀ h, 1 ≤ h → h ≤ n → ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1)
    (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) :
    ∃ z : ℤ, (z : ℝ) = (WIG q α β n : ℝ) *
      ∑ h ∈ Finset.Icc 1 n, (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)⁻¹ *
        ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  refine ⟨∑ h ∈ Finset.Icc 1 n, uClearIntG q α β n h * Nz h, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Int.cast_mul, uClearIntG_cast hβ hh.1 hh.2 (hCn h hh.1 hh.2), hNz h hh.1 hh.2]
  ring

/-- **Borwein Lemma 3 (numerator integrality), general `(q,C)`, conditional on `N_h ∈ ℤ`.** Combines
the Rrat-part (`WIG_mul_RratClean_int`) and headS-part (`WIG_mul_headS_int`) integralities via
`AcorrG_clean` and `WIG_cast`: `−β^{2n}·Wₙ·AcorrG n ∈ ℤ`. -/
lemma AcorrG_int_of_Nz {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hCn : ∀ h, 1 ≤ h → h ≤ n → ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1)
    (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) :
    ∃ a : ℤ, (a : ℝ)
      = -((β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * AcorrG (q : ℝ) ((α : ℝ) / (β : ℝ)) n) := by
  obtain ⟨rInt, hr⟩ := WIG_mul_RratClean_int hq hβ n
  obtain ⟨hInt, hh⟩ := WIG_mul_headS_int hβ n hCn Nz hNz
  refine ⟨rInt - hInt, ?_⟩
  rw [← WIG_cast q α β hβ]
  push_cast
  rw [hr, hh, AcorrG_clean hq ((α : ℝ) / (β : ℝ)) n hn]
  ring

/-- Total integer witness function for `N_h` (zero off `[1,n]`), packaging `NhG_int`. -/
theorem NhG_integral {q : ℤ} (hq : 2 ≤ |q|) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Nz : ℕ → ℤ, ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  choose Nz hNz using fun h (hh1 : 1 ≤ h) (hhn : h ≤ n) => NhG_int_abs hq n h hn hh1 hhn
  refine ⟨fun h => if H : 1 ≤ h ∧ h ≤ n then Nz h H.1 H.2 else 0, fun h hh1 hhn => ?_⟩
  show ((dite (1 ≤ h ∧ h ≤ n) (fun H => Nz h H.1 H.2) (fun _ => 0) : ℤ) : ℝ) = _
  rw [dif_pos (⟨hh1, hhn⟩ : 1 ≤ h ∧ h ≤ n)]
  have hspec := hNz h hh1 hhn
  rw [hspec, NhG]

/-- **Borwein Lemma 3 (numerator integrality), general `(q,C)` — MILESTONE.** For integer `q ≥ 2`,
`C = α/β` with `β ≠ 0` and `C·q^h ≠ 1` (`1 ≤ h ≤ n`), the rational correction `AcorrG n` of the
residue identity clears to an integer when scaled by `β^{2n}·Wₙ`: `∃ a : ℤ, (a:ℝ) = −β^{2n}·Wₙ·AcorrG n`.
The general analog of `numerator_integrality` (the `q=2,C=8/3` case), discharging the Lemma-3
sub-obligation of `borwein_approximants` for the `(q,C)` range. -/
theorem AcorrG_int {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hCn : ∀ h, 1 ≤ h → h ≤ n → ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1) :
    ∃ a : ℤ, (a : ℝ)
      = -((β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * AcorrG (q : ℝ) ((α : ℝ) / (β : ℝ)) n) := by
  obtain ⟨Nz, hNz⟩ := NhG_integral hq n hn
  exact AcorrG_int_of_Nz hq hβ n hn hCn Nz hNz

/-! ## Section 4: general Lemmas 1+2+3 assembled — the integer approximant identity

With the residue identity (Lemma 1, `EtermG_eq_pValG`), denominator integrality (Lemma 2,
`BdenG_cast`) and numerator integrality (Lemma 3, `AcorrG_int`) all general and machine-checked, the
cleared error `β^{2n}·Wₙ·Eₙ` is exactly `bₙ·z − aₙ` for integer sequences `aₙ, bₙ` (`bₙ = −BdenG`,
`aₙ = −β^{2n}·Wₙ·AcorrG`). This is the general analog of `borwein_integrality` (`Lemma3.lean`). The only
sub-obligations of `borwein_approximants` still open are Lemma 4 (`bₙ·z − aₙ → 0`) and Lemma 5
(`bₙ·z − aₙ ≠ 0`), both requiring a magnitude condition `|C| ≥ 2`. -/

/-- **Borwein Lemmas 1+2+3, assembled, general `(q,C)`.** For integer `q ≥ 2` and `C = α/β` with
`α, β ≠ 0` and `C·q^h ≠ 1`, there are integer sequences `aₙ, bₙ` with
`bₙ·z − aₙ = β^{2n}·Wₙ(C,q)·Eₙ(C,q)` for all `n ≥ 1`, where `z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹`. The cleared
error of the q-Padé approximants is an explicit integer combination of `z`. (General analog of
`borwein_integrality`.) -/
theorem borwein_integralityG {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hCn : ∀ h : ℕ, ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1) ≠ 1) :
    ∃ a b : ℕ → ℤ, ∀ n, 1 ≤ n →
      (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n
        = (β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by linarith : (1 : ℤ) < |q|)
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hα0 : (α : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hα
  have hC0 : ((α : ℝ) / (β : ℝ)) ≠ 0 := div_ne_zero hα0 hβ0
  -- Lemma 3 gives a per-`n` integer numerator `aₙ = −β^{2n}·Wₙ·AcorrG n`.
  have key : ∀ n, 1 ≤ n → ∃ a : ℤ, (a : ℝ)
      = -((β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * AcorrG (q : ℝ) ((α : ℝ) / (β : ℝ)) n) := by
    intro n hn
    refine AcorrG_int hq hβ n hn ?_
    intro h hh1 _
    have hh := hCn (h - 1)
    rwa [Nat.sub_add_cancel hh1] at hh
  choose a ha using key
  refine ⟨fun n => if h : 1 ≤ n then a n h else 0, fun n => -BdenG q α β n, fun n hn => ?_⟩
  simp only [dif_pos hn]
  have hE := EtermG_eq_pValG hq1abs hC0 hCn hn
  have hB := BdenG_cast q α β hβ hn
  have hA := ha n hn
  rw [hE]
  push_cast
  rw [hB, hA]
  ring

end LeanGallery.NumberTheory.Erdos1050
