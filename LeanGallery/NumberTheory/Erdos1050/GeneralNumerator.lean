/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.General
import LeanGallery.NumberTheory.Erdos1050.QLagrange

/-!
# General numerator integrality (Borwein Lemma 3) — the genuine nub, for integer `q ≥ 2`

This file discharges the hardest sub-obligation of the general `borwein_approximants` axiom
(`General.lean`): **numerator integrality**, i.e. that the q-Lagrange combination

    `N_h(q,n) = ∑_{j=1}^n μ_j(q,n) · ∏_{k=1}^{n-1} (1 − q^{k+j−h})`,    `μ_j = ∏_{l≠j}(1 − q^l/q^j)⁻¹`,

is an **integer**, for every integer `q ≥ 2`. This is `PENDING_WORK.md` path 3a, generalized from the
`q = 2` case (`Lemma3.lean`, `Nh_int`) to all bases `q ≥ 2` (an infinite family).

The argument is the `q = 2` template with `2` replaced by a general integer `q`, made possible because
the underlying engine is already general: the q-Lagrange identity `qLagrange` (`QLagrange.lean`, valid
for real `q > 1`), the Gaussian binomial `qBin` (`QBinom.lean`, any `CommRing`), and the standalone
bricks `coprime_qpow_sub_one`, `borwein_div` (`General.lean`).

`N_h ∈ ℤ` follows from two *coprime* clearings:
* **part (a), q-adic** (`nh_qadic_int`): `(q^h)^{n−1}·N_h ∈ ℤ`. The factor `(q^h)^{n−1}` absorbs the
  negative q-powers; q-Lagrange collapses the `μ_j`-sum to Gaussian binomials. So `N_h ∈ ℤ[1/q]`.
* **part (b), coprime-to-q** (`DfullG_NhG_int`): `D·N_h ∈ ℤ` where `D = ∏_j ∏_{l≠j}(q^{|j−l|}−1)` is
  coprime to `q` (each `q^d − 1 ≡ −1 mod q`, `coprime_qpow_sub_one`). So `N_h ∈ ℤ[1/D]`.
The combine `int_of_coprime_clearings` (general `ℤ[1/e] ∩ ℤ[1/f] = ℤ` for `IsCoprime e f`) then gives
`N_h ∈ ℤ` (`NhG_int`).

(Only `q ≥ 2` — positive — is covered, because part (a) routes through `qLagrange`'s `1 < q`. The
`q ≤ −2` case needs the q-Lagrange node-distinctness re-derived for negative `q`; noted as a TODO.)

This file is additive; it does not touch `erdos_1050_irrational` (axiom-clean) and does not yet wire
`NhG_int` into a parametric `Eterm` (the residue-identity layer), which remains the open work toward
fully discharging `borwein_approximants`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Finset

/-! ### Generic facts for integer `q` with `2 ≤ |q|`. -/

/-- `(q : ℝ) ≠ 0` when `2 ≤ |q|`. -/
lemma qcast_ne_zero {q : ℤ} (hq : 2 ≤ |q|) : (q : ℝ) ≠ 0 := by
  have hq0 : q ≠ 0 := by rintro rfl; norm_num at hq
  exact Int.cast_ne_zero.mpr hq0

/-- `(q : ℝ)^d ≠ 1` for `d ≥ 1` when `2 ≤ |q|` (since `|q^d| = |q|^d ≥ 2`). -/
lemma qcast_pow_ne_one {q : ℤ} (hq : 2 ≤ |q|) {d : ℕ} (hd : 1 ≤ d) : (q : ℝ) ^ d ≠ 1 := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have h1 : (1 : ℝ) ≤ |(q : ℝ)| := by linarith
  have hge : (2 : ℝ) ≤ |(q : ℝ)| ^ d := by
    calc (2 : ℝ) ≤ |(q : ℝ)| := hqabs
      _ = |(q : ℝ)| ^ 1 := (pow_one _).symm
      _ ≤ |(q : ℝ)| ^ d := pow_le_pow_right₀ h1 hd
  intro h
  rw [← abs_pow, h, abs_one] at hge
  norm_num at hge

/-- General q-Lagrange weight `μ_j = ∏_{l∈[1,n], l≠j}(1 − q^l/q^j)⁻¹` (real `q`). -/
noncomputable def muWG (q : ℝ) (n j : ℕ) : ℝ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹

/-- General q-Lagrange combination `N_h(q,n) = ∑_j μ_j ∏_{k=1}^{n-1}(1 − q^{k+j−h})`. -/
noncomputable def NhG (q : ℝ) (n h : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muWG q n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h))

/-- **General coprime clearing** `ℤ[1/e] ∩ ℤ[1/f] = ℤ`: if `e·N` and `f·N` are integers with
`IsCoprime e f`, then `N` is an integer. Generalizes `int_of_clearings` (`2`/odd) to arbitrary
coprime denominators — the combine step of the general numerator integrality (path 3a). -/
lemma int_of_coprime_clearings {N : ℝ} {A B e f : ℤ} (hef : IsCoprime e f)
    (hA : (A : ℝ) = (e : ℝ) * N) (hB : (B : ℝ) = (f : ℝ) * N) :
    ∃ z : ℤ, (z : ℝ) = N := by
  obtain ⟨u, v, huv⟩ := hef
  refine ⟨u * A + v * B, ?_⟩
  have hcast : ((u * A + v * B : ℤ) : ℝ) = (u : ℝ) * (A : ℝ) + (v : ℝ) * (B : ℝ) := by
    push_cast; ring
  rw [hcast, hA, hB]
  have key : (u : ℝ) * ((e : ℝ) * N) + (v : ℝ) * ((f : ℝ) * N) = ((u * e + v * f : ℤ) : ℝ) * N := by
    push_cast; ring
  rw [key, huv, Int.cast_one, one_mul]

/-! ### Part (a): the q-adic clearing `(q^h)^{n−1}·N_h ∈ ℤ`. -/

/-- General q-Lagrange identity for integer `q ≥ 2`: `∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`, `i < n`. -/
theorem qLagG {q : ℤ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ i
      = (q : ℝ) ^ i * qBin (q : ℝ) (n + i - 1) (n - 1) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have h := qLagrange (q : ℝ) hq1 n hn i (by omega)
  simpa only [muWG] using h

/-- General q-Lagrange identity for `2 ≤ |q|` (both signs, e.g. negative base `q ≤ −2`):
`∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`. Same as `qLagG` but via `qLagrange_abs`. -/
theorem qLagG_abs {q : ℤ} (hq : 2 ≤ |q|) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ i
      = (q : ℝ) ^ i * qBin (q : ℝ) (n + i - 1) (n - 1) := by
  have hq1 : (1 : ℝ) < |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by omega : (1 : ℤ) < |q|)
  have h := qLagrange_abs (q : ℝ) hq1 n hn i (by omega)
  simpa only [muWG] using h

/-- Cleared product (general `q`): `(q^h)^{n-1}·∏(1−q^{k+j−h}) = ∏(q^h−q^{k+j})`. -/
lemma clearedProdG {q : ℤ} (hq : 2 ≤ |q|) (n j h : ℕ) :
    ((q : ℝ) ^ h) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))
      = ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j)) := by
  have hqne : (q : ℝ) ≠ 0 := qcast_ne_zero hq
  have hcard : ((q : ℝ) ^ h) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (q : ℝ) ^ h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [mul_sub, mul_one]
  congr 1
  rw [← zpow_natCast (q : ℝ) h, ← zpow_add₀ hqne, ← zpow_natCast (q : ℝ) (k + j)]
  congr 1
  push_cast
  ring

/-- Expand `∏(q^h − q^{k+j})` over subsets `t ⊆ [1,n-1]` as a polynomial in `q^j`. -/
lemma prod_diff_expandG (q : ℤ) (n j h : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ j) ^ t.card
            * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card) := by
  have hf : ∀ k, ((q : ℝ) ^ h - (q : ℝ) ^ (k + j) : ℝ) = (-(q : ℝ) ^ (k + j)) + (q : ℝ) ^ h :=
    fun k => by ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const]
  have hexp : ∏ k ∈ t, (-(q : ℝ) ^ (k + j))
      = (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ j) ^ t.card := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _; rw [pow_add]; ring
  rw [hexp]

/-- q-Lagrange reduction of the cleared `N_h` (the `muW`-free form). -/
lemma Nh_prod_qLagG {q : ℤ} (hq : 2 ≤ q) (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n,
        muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expandG q n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLagG hq hn t.card hcard]

/-- Per-`t` integer witness for the cleared `N_h`. -/
def Nh2TermIntG (q : ℤ) (n h : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-q ^ k)) * (q ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
    * (q ^ t.card * qBin q (n + t.card - 1) (n - 1))

/-- Each `Nh_prod_qLagG` `t`-term is the integer `Nh2TermIntG q n h t`. -/
lemma Nh2TermIntG_cast (q : ℤ) (n h : ℕ) (t : Finset ℕ) :
    (Nh2TermIntG q n h t : ℝ)
      = (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
        * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  have hbin : ((qBin q (n + t.card - 1) (n - 1) : ℤ) : ℝ) = qBin (q : ℝ) (n + t.card - 1) (n - 1) :=
    (qBin_map (Int.castRingHom ℝ) q (n + t.card - 1) (n - 1)).symm
  rw [Nh2TermIntG]
  push_cast [hbin]
  ring

/-- The clearing identity `(q^h)^{n−1}·N_h = ∑_j μ_j ∏(q^h − q^{k+j})`. -/
lemma Nh_2adicG {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) :
    ((q : ℝ) ^ h) ^ (n - 1) * NhG (q : ℝ) n h
      = ∑ j ∈ Finset.Icc 1 n,
          muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j)) := by
  rw [NhG, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, clearedProdG hq n j h]

/-- **Part (a): q-adic clearing.** `(q^h)^{n−1}·N_h ∈ ℤ`, so `N_h ∈ ℤ[1/q]`. -/
lemma nh_qadic_int {q : ℤ} (hq : 2 ≤ q) (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = ((q : ℝ) ^ h) ^ (n - 1) * NhG (q : ℝ) n h := by
  have habs : 2 ≤ |q| := by rw [abs_of_pos (by omega : (0 : ℤ) < q)]; exact hq
  rw [Nh_2adicG habs n h, Nh_prod_qLagG hq n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermIntG q n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermIntG_cast q n h t

/-! ### Part (b): the coprime-to-q clearing `D·N_h ∈ ℤ` with `IsCoprime D q`. -/

/-- The cleared `l`-factor value: `q^{j−l}` if `l<j`, else `−1`. -/
def zfacG (q : ℤ) (j l : ℕ) : ℤ := if l < j then q ^ (j - l) else -1

/-- Per-factor coprime clearing: `(q^{|j−l|}−1)·(1 − q^l/q^j)⁻¹ = zfacG q j l ∈ ℤ`. -/
lemma factor_clearG {q : ℤ} (hq : 2 ≤ |q|) {j l : ℕ} (hlj : l ≠ j) :
    ((zfacG q j l : ℤ) : ℝ)
      = (((q ^ (max j l - min j l) - 1 : ℤ)) : ℝ) * (1 - (q : ℝ) ^ l / (q : ℝ) ^ j)⁻¹ := by
  have hqne : (q : ℝ) ≠ 0 := qcast_ne_zero hq
  rw [zfacG]
  rcases lt_or_gt_of_ne hlj with hlt | hgt
  · rw [if_pos hlt]
    have hmm : max j l - min j l = j - l := by omega
    have hd1 : 1 ≤ j - l := by omega
    have ha1 : (q : ℝ) ^ (j - l) - 1 ≠ 0 := sub_ne_zero.mpr (qcast_pow_ne_one hq hd1)
    have hQ0 : (q : ℝ) ^ (j - l) ≠ 0 := pow_ne_zero _ hqne
    have hdiv : ((q : ℝ) ^ l / (q : ℝ) ^ j) = ((q : ℝ) ^ (j - l))⁻¹ := by
      rw [show (q : ℝ) ^ j = (q : ℝ) ^ (j - l) * (q : ℝ) ^ l from by
        rw [← pow_add]; congr 1; omega]
      rw [mul_comm]; field_simp
    rw [hmm, hdiv]
    push_cast
    field_simp
  · rw [if_neg (by omega)]
    have hmm : max j l - min j l = l - j := by omega
    have hd1 : 1 ≤ l - j := by omega
    have ha1 : (q : ℝ) ^ (l - j) - 1 ≠ 0 := sub_ne_zero.mpr (qcast_pow_ne_one hq hd1)
    have hdiv : ((q : ℝ) ^ l / (q : ℝ) ^ j) = (q : ℝ) ^ (l - j) := by
      rw [show (q : ℝ) ^ l = (q : ℝ) ^ (l - j) * (q : ℝ) ^ j from by
        rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    rw [show (1 : ℝ) - (q : ℝ) ^ (l - j) = -((q : ℝ) ^ (l - j) - 1) from by ring, inv_neg]
    field_simp

/-- The coprime-to-q clearing product `VgenW q n j = ∏_{l≠j}(q^{|j−l|}−1)`. -/
def VgenW (q : ℤ) (n j : ℕ) : ℤ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (q ^ (max j l - min j l) - 1)

/-- `VgenW q n j` is coprime to `q` (each factor `q^d − 1 ≡ −1 mod q`, `d ≥ 1`). -/
lemma VgenW_coprime (q : ℤ) (n j : ℕ) : IsCoprime (VgenW q n j) q := by
  rw [VgenW]
  apply IsCoprime.prod_left
  intro l hl
  rw [Finset.mem_erase] at hl
  obtain ⟨hlj, _⟩ := hl
  obtain ⟨d, hd⟩ : ∃ d, max j l - min j l = d + 1 := ⟨max j l - min j l - 1, by omega⟩
  rw [hd]
  exact coprime_qpow_sub_one q d

/-- `VgenW q n j · μ_j ∈ ℤ` — the coprime product clears `μ_j`'s denominator (per-factor). -/
lemma VgenW_muWG_int {q : ℤ} (hq : 2 ≤ |q|) (n j : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (VgenW q n j : ℝ) * muWG (q : ℝ) n j := by
  refine ⟨∏ l ∈ (Finset.Icc 1 n).erase j, zfacG q j l, ?_⟩
  rw [Int.cast_prod, VgenW, Int.cast_prod, muWG, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  exact factor_clearG hq (Finset.mem_erase.mp hl).1

/-- The coprime common denominator `DfullG q n = ∏_{j∈[1,n]} VgenW q n j`, clearing every `μ_j`. -/
def DfullG (q : ℤ) (n : ℕ) : ℤ := ∏ j ∈ Finset.Icc 1 n, VgenW q n j

/-- `DfullG q n` is coprime to `q`. -/
lemma DfullG_coprime (q : ℤ) (n : ℕ) : IsCoprime (DfullG q n) q := by
  rw [DfullG]
  apply IsCoprime.prod_left
  intro j _
  exact VgenW_coprime q n j

/-- `DfullG q n · μ_j ∈ ℤ` for `j ∈ [1,n]`. -/
lemma DfullG_muWG_int {q : ℤ} (hq : 2 ≤ |q|) {n j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    ∃ m : ℤ, (m : ℝ) = (DfullG q n : ℝ) * muWG (q : ℝ) n j := by
  obtain ⟨z, hz⟩ := VgenW_muWG_int hq n j
  refine ⟨(∏ j' ∈ (Finset.Icc 1 n).erase j, VgenW q n j') * z, ?_⟩
  rw [DfullG, ← Finset.mul_prod_erase (Finset.Icc 1 n) (VgenW q n) hj]
  push_cast
  rw [hz]
  ring

/-- `P_j = ∏_{k=1}^{n−1}(1 − q^{k+j−h})` is an integer when `j ≥ h` (all exponents `≥ 1`). -/
lemma PjG_int {q : ℤ} {n j h : ℕ} (hjh : h ≤ j) :
    ∃ p : ℤ, (p : ℝ) = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  refine ⟨∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ (k + j - h)), ?_⟩
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [show ((k : ℤ) + j - h) = ((k + j - h : ℕ) : ℤ) from by omega, zpow_natCast]
  norm_cast

/-- `P_j = 0` when `1 ≤ j < h ≤ n` (the factor with exponent `0` vanishes). -/
lemma prod_vanishG {q : ℤ} {n j h : ℕ} (hj : 1 ≤ j) (hjh : j < h) (hhn : h ≤ n) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) = 0 := by
  apply Finset.prod_eq_zero (i := h - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have : ((h - j : ℕ) : ℤ) + j - h = 0 := by rw [Nat.cast_sub (by omega)]; ring
  rw [this, zpow_zero, sub_self]

/-- **Part (b): the coprime-to-q clearing of `N_h`.** `DfullG q n · N_h ∈ ℤ`, with
`IsCoprime (DfullG q n) q`. So `N_h ∈ ℤ[1/D]` for `D` coprime to `q`. -/
lemma DfullG_NhG_int {q : ℤ} (hq : 2 ≤ |q|) {n : ℕ} (h : ℕ) (_hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (DfullG q n : ℝ) * NhG (q : ℝ) n h := by
  rw [NhG, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc 1 n, ∃ b : ℤ, (b : ℝ) = (DfullG q n : ℝ) *
      (muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) := by
    intro j hj
    rcases Nat.lt_or_ge j h with hlt | hge
    · refine ⟨0, ?_⟩
      rw [Finset.mem_Icc] at hj
      have hv : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) = 0 :=
        prod_vanishG hj.1 hlt hhn
      rw [hv]; push_cast; ring
    · obtain ⟨m, hm⟩ := DfullG_muWG_int hq hj
      obtain ⟨p, hp⟩ := PjG_int (q := q) (n := n) hge
      exact ⟨m * p, by push_cast; rw [hm, hp]; ring⟩
  choose b hb using hterm
  refine ⟨∑ j ∈ (Finset.Icc 1 n).attach, b j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.Icc 1 n) _]
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  exact hb j hj

/-! ### Combine: `N_h ∈ ℤ` for integer `q ≥ 2`. -/

/-- **General numerator integrality (Borwein Lemma 3), for integer `q ≥ 2`.** The q-Lagrange
combination `N_h(q,n) = ∑_j μ_j ∏_{k=1}^{n-1}(1 − q^{k+j−h})` is an integer. Combine the q-adic
clearing (part a, `nh_qadic_int`) and the coprime-to-q clearing (part b, `DfullG_NhG_int`) via
`int_of_coprime_clearings`, using `IsCoprime (q^{(n-1)h}) (DfullG q n)` (a power of `q` is coprime to
`DfullG`, which is coprime to `q`). This discharges the genuine nub of the general
`borwein_approximants` for every base `q ≥ 2`. -/
theorem NhG_int {q : ℤ} (hq : 2 ≤ q) (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = NhG (q : ℝ) n h := by
  have habs : 2 ≤ |q| := by rw [abs_of_pos (by omega : (0 : ℤ) < q)]; exact hq
  obtain ⟨A, hA⟩ := nh_qadic_int hq n h hn
  obtain ⟨B, hB⟩ := DfullG_NhG_int habs h hh1 hhn
  -- part (a) gives `(q^h)^{n−1}·N_h = q^{(n−1)h}·N_h`.
  have hA' : (A : ℝ) = (q : ℝ) ^ ((n - 1) * h) * NhG (q : ℝ) n h := by
    rw [hA, ← pow_mul, mul_comm h (n - 1)]
  -- `q^{(n−1)h}` is coprime to `DfullG q n` (power of q vs coprime-to-q).
  have hcop : IsCoprime ((q : ℤ) ^ ((n - 1) * h)) (DfullG q n) :=
    (IsCoprime.pow_left ((DfullG_coprime q n).symm))
  have hA'' : ((A : ℤ) : ℝ) = ((q ^ ((n - 1) * h) : ℤ) : ℝ) * NhG (q : ℝ) n h := by
    push_cast; exact hA'
  exact int_of_coprime_clearings hcop hA'' hB

/-! ### Negative base `q ≤ −2`: the numerator nub `N_h ∈ ℤ` for `2 ≤ |q|`.

The magnitude bricks (`clearedProdG`, `Nh_2adicG`, `DfullG_NhG_int`, `DfullG_coprime`) already hold for
`2 ≤ |q|`; only the q-Lagrange reduction needed the positive variant. With `qLagG_abs` the whole q-adic
clearing — and hence `N_h ∈ ℤ` — generalizes to `2 ≤ |q|`, covering negative base. -/

/-- q-Lagrange reduction of the cleared `N_h` for `2 ≤ |q|` (via `qLagG_abs`). -/
lemma Nh_prod_qLagG_abs {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n,
        muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expandG q n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLagG_abs hq hn t.card hcard]

/-- **Part (a) for `2 ≤ |q|`**: `(q^h)^{n−1}·N_h ∈ ℤ`. -/
lemma nh_qadic_int_abs {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = ((q : ℝ) ^ h) ^ (n - 1) * NhG (q : ℝ) n h := by
  rw [Nh_2adicG hq n h, Nh_prod_qLagG_abs hq n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermIntG q n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermIntG_cast q n h t

/-- **Borwein Lemma 3 numerator nub for `2 ≤ |q|`** (both signs, incl. negative base `q ≤ −2`):
the q-Lagrange combination `N_h = NhG q n h ∈ ℤ`. Via the q-adic clearing (`nh_qadic_int_abs`) and the
coprime-to-q clearing (`DfullG_NhG_int`, already general). A brick toward `AcorrG_int` for negative base. -/
theorem NhG_int_abs {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = NhG (q : ℝ) n h := by
  obtain ⟨A, hA⟩ := nh_qadic_int_abs hq n h hn
  obtain ⟨B, hB⟩ := DfullG_NhG_int hq h hh1 hhn
  have hA' : (A : ℝ) = (q : ℝ) ^ ((n - 1) * h) * NhG (q : ℝ) n h := by
    rw [hA, ← pow_mul, mul_comm h (n - 1)]
  have hcop : IsCoprime ((q : ℤ) ^ ((n - 1) * h)) (DfullG q n) :=
    (IsCoprime.pow_left ((DfullG_coprime q n).symm))
  have hA'' : ((A : ℤ) : ℝ) = ((q ^ ((n - 1) * h) : ℤ) : ℝ) * NhG (q : ℝ) n h := by
    push_cast; exact hA'
  exact int_of_coprime_clearings hcop hA'' hB

/-! ### General first-form = second-form denominator identity (Borwein Lemma 2, "Piece III").

`pₙ(C,q)` has a *first* form (a `μ_j`-weighted sum, the residue form) and a *second* form (the
Gaussian-binomial `pValG`). They agree (`pFirstG_eq_pValG`), via the Cauchy q-binomial expansion
(`cprod_cauchyG`) and the general q-Lagrange identity (`qLagrange`). This is a building block of the
general residue identity (Lemma 1), parametric in `(q, C)`. -/

/-- q-Lagrange identity in `muWG` form for `1 < |q|` (both signs, negative base allowed). -/
lemma qLagrange_muWG {q : ℝ} (hq1 : 1 < |q|) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muWG q n j * (q ^ j) ^ i = q ^ i * qBin q (n + i - 1) (n - 1) := by
  have h := qLagrange_abs q hq1 n hn i (by omega)
  simpa only [muWG] using h

/-- Exponent bookkeeping `i(i−1)/2 + 2i = i(i+3)/2`. -/
private lemma exp_idenG (i : ℕ) : i * (i - 1) / 2 + 2 * i = i * (i + 3) / 2 := by
  rcases i with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1) * (m + 1 + 3) = (c + 2 * (m + 1)) + (c + 2 * (m + 1)) := by
      have : (m + 1) * (m + 1 + 3) = m * (m + 1) + 4 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- The Cauchy expansion of the `c`-product (general `q, C`). -/
lemma cprod_cauchyG (q C : ℝ) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))
      = ∑ i ∈ Finset.range n,
          q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ ((j + 1) * i) := by
  have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.prod_Ico_eq_prod_range]
  have hterm : ∀ k, (1 - C * q ^ (1 + k + j)) = 1 + q ^ k * (-C * q ^ (j + 1)) := by
    intro k
    rw [show 1 + k + j = k + (j + 1) from by ring, pow_add]; ring
  rw [Finset.prod_congr rfl (fun k _ => hterm k), qBin_cauchy q (-C * q ^ (j + 1)) (n - 1),
    Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← pow_mul]
  ring

/-- Borwein's q-Padé denominator in **first form** `pₙ = ∑_{j=1}^n μ_j·∏_{k=1}^{n-1}(1−C q^{k+j})`. -/
noncomputable def pFirstG (q C : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muWG q n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))

/-- **First form = second form** (Borwein Lemma 2), general `(q, C)`, `1 < |q|` (negative base
allowed): `pFirstG = pValG`. -/
theorem pFirstG_eq_pValG {q : ℝ} (hq1 : 1 < |q|) (C : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    pFirstG q C n = pValG q C n := by
  rw [pFirstG, pValG]
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muWG q n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))
        = ∑ i ∈ Finset.range n,
            muWG q n j * (q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ ((j + 1) * i)) := by
    intro j _
    rw [cprod_cauchyG q C hn j, Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hfac : ∀ j ∈ Finset.Icc 1 n,
      muWG q n j * (q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ ((j + 1) * i))
        = (q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ i)
          * (muWG q n j * (q ^ j) ^ i) := by
    intro j _
    rw [show (j + 1) * i = i + j * i from by ring, pow_add, pow_mul]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, qLagrange_muWG hq1 hn i hi]
  rw [show i * (i + 3) / 2 = i * (i - 1) / 2 + 2 * i from (exp_idenG i).symm, pow_add]
  ring

end LeanGallery.NumberTheory.Erdos1050
