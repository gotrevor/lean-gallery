/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.GeneralResidue
import LeanGallery.NumberTheory.Erdos1050.Approximants

/-!
# Borwein Lemma 5 (non-vanishing) and the summable majorant — general `(q, C)`

Ports the `q = 2, C = 8/3` error-sign machinery (`Approximants.lean`, Lemma 5) to general real `q ≥ 2`
and `C > 2` (Borwein's shifted magnitude regime; `cB = 8/3 > 2` is the concrete instance). Every term
`ItermG q C n m` (`m ≥ n ≥ 1`) has the same nonzero sign `(-1)^{n-1}`, so the error
`EtermG q C n = ∑_{j} ItermG q C n (n+j)` cannot vanish.

The summable geometric majorant `|ItermG q C n (n+j)| ≤ (q⁻¹)^j` (also used for `EtermG_summable`,
the Lemma-4 convergence half) is proved here too.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

variable {q C : ℝ}

/-- `q^a ≥ 2` for `a ≥ 1` when `q ≥ 2` (zpow version). -/
lemma qzpow_ge_two (hq : 2 ≤ q) {a : ℤ} (ha : 1 ≤ a) : (2 : ℝ) ≤ q ^ a := by
  have hq1 : (1 : ℝ) < q := by linarith
  calc (2 : ℝ) ≤ q := hq
    _ = q ^ (1 : ℤ) := (zpow_one q).symm
    _ ≤ q ^ a := zpow_le_zpow_right₀ (le_of_lt hq1) ha

/-- **Magnitude bound** (sign-independent): for `|C| > 2`, `q ≥ 2`, `a ≥ 1`, `|(1 − C·q^a)⁻¹| ≤ q^{-a}`.
Reverse triangle: `|1 − C·q^a| ≥ |C|·q^a − 1 ≥ 2q^a − 1 ≥ q^a`. -/
lemma inv_cqpowG_le (hq : 2 ≤ q) (hC : 2 < |C|) {a : ℤ} (ha : 1 ≤ a) :
    |(1 - C * q ^ a)⁻¹| ≤ q ^ (-a) := by
  have hqa : (2 : ℝ) ≤ q ^ a := qzpow_ge_two hq ha
  have hqpos : (0 : ℝ) < q ^ a := zpow_pos (by linarith) a
  have hge : q ^ a ≤ |1 - C * q ^ a| := by
    have h1 : |C * q ^ a| - |(1 : ℝ)| ≤ |C * q ^ a - 1| := abs_sub_abs_le_abs_sub _ _
    have h2 : |C * q ^ a| = |C| * q ^ a := by rw [abs_mul, abs_of_pos hqpos]
    have h3 : |C * q ^ a - 1| = |1 - C * q ^ a| := abs_sub_comm _ _
    rw [h2, abs_one, h3] at h1
    nlinarith [h1, hqa, hC, hqpos, mul_pos (show (0 : ℝ) < |C| - 2 by linarith) hqpos]
  rw [abs_inv, zpow_neg]
  exact inv_anti₀ hqpos hge

/-! ### Negative-BASE (`q ≤ -2`, i.e. `2 ≤ |q|`) magnitude bounds — Lemma 4 convergence half.

For negative base the powers `q^a` alternate sign, so the bounds must be stated in terms of `|q|`.
The reverse-triangle estimate `|1 − C·q^a| ≥ |C|·|q|^a − 1 ≥ |q|^a` (using `|C| > 2`) survives unchanged,
and although the cross factor `|1 − q^{k−m}|` now costs `≤ 2` (vs `≤ 1` for positive `q`), the extra
`2`'s are harmless: `2·|q|⁻¹ ≤ 1` since `|q| ≥ 2`, so the geometric majorant `(|q|⁻¹)^j` is recovered
exactly. These feed `EtermG_summable_abs`, the negative-base analog of `EtermG_summable`. -/

/-- **Cross-factor positivity** (negative base): for `2 ≤ |q|` and `k < m`, the factor
`1 − q^{k−m} > 0`, because `|q^{k−m}| = |q|^{k−m} ≤ |q|⁻¹ ≤ 1/2 < 1` (the exponent `k−m ≤ −1`).
This holds for BOTH signs of `q` and is the reason the cross product never affects the sign of
`ItermG` — a key brick for the negative-base non-vanishing (Lemma 5) sign analysis. -/
lemma one_sub_qzpow_pos (hq : 2 ≤ |q|) {k m : ℕ} (hkm : k < m) :
    0 < 1 - q ^ ((k : ℤ) - m) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hlt : q ^ ((k : ℤ) - m) < 1 := by
    have h1 : |q ^ ((k : ℤ) - m)| ≤ |q| ^ (-1 : ℤ) := by
      rw [abs_zpow]; exact zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
    have h2 : |q| ^ (-1 : ℤ) < 1 := by
      rw [zpow_neg, zpow_one]; exact inv_lt_one_of_one_lt₀ hqabs1
    calc q ^ ((k : ℤ) - m) ≤ |q ^ ((k : ℤ) - m)| := le_abs_self _
      _ ≤ |q| ^ (-1 : ℤ) := h1
      _ < 1 := h2
  linarith

/-- **Magnitude bound, both signs of `q`**: for `2 ≤ |q|`, `2 < |C|`, `a ≥ 1`,
`|(1 − C·q^a)⁻¹| ≤ |q|^{-a}`. -/
lemma inv_cqpow_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {a : ℤ} (ha : 1 ≤ a) :
    |(1 - C * q ^ a)⁻¹| ≤ |q| ^ (-a) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqa : (2 : ℝ) ≤ |q| ^ a := by
    calc (2 : ℝ) ≤ |q| := hq
      _ = |q| ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ |q| ^ a := zpow_le_zpow_right₀ (le_of_lt hqabs1) ha
  have hqpos : (0 : ℝ) < |q| ^ a := zpow_pos (by linarith) a
  have hge : |q| ^ a ≤ |1 - C * q ^ a| := by
    have h1 : |C * q ^ a| - |(1 : ℝ)| ≤ |C * q ^ a - 1| := abs_sub_abs_le_abs_sub _ _
    have h2 : |C * q ^ a| = |C| * |q| ^ a := by rw [abs_mul, abs_zpow]
    have h3 : |C * q ^ a - 1| = |1 - C * q ^ a| := abs_sub_comm _ _
    rw [h2, abs_one, h3] at h1
    nlinarith [h1, hqa, hC, hqpos, mul_pos (show (0 : ℝ) < |C| - 2 by linarith) hqpos]
  rw [abs_inv, zpow_neg]
  exact inv_anti₀ hqpos hge

/-- Each product factor has `|·| ≤ 2·|q|⁻¹` for `1 ≤ k < m`, `2 ≤ |q|`, `2 < |C|`. The cross factor
`|1 − q^{k−m}| ≤ 1 + |q|^{k−m} ≤ 2` and the leading inverse `≤ |q|^{−(k+m)} ≤ |q|⁻¹`. -/
lemma factor_bound_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ 2 * |q|⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  rw [abs_mul]
  have hle1 : |q| ^ ((k : ℤ) - m) ≤ 1 := by
    calc |q| ^ ((k : ℤ) - m) ≤ |q| ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
      _ = 1 := by norm_num
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 2 := by
    calc |1 - q ^ ((k : ℤ) - m)| = |(1 : ℝ) + -(q ^ ((k : ℤ) - m))| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-(q ^ ((k : ℤ) - m))| := abs_add_le _ _
      _ = 1 + |q| ^ ((k : ℤ) - m) := by rw [abs_one, abs_neg, abs_zpow]
      _ ≤ 2 := by linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ |q| ^ (-((k : ℤ) + m)) := inv_cqpow_le_abs hq hC (by omega)
  have h3 : |q| ^ (-((k : ℤ) + m)) ≤ |q|⁻¹ := by
    calc |q| ^ (-((k : ℤ) + m)) ≤ |q| ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
      _ = |q|⁻¹ := by rw [zpow_neg, zpow_one]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 2 * |q| ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ ≤ 2 * |q|⁻¹ := mul_le_mul_of_nonneg_left h3 (by norm_num)

/-- Crude per-term bound (negative base): `|ItermG q C n m| ≤ |q|^{-(m+n)}·(2|q|⁻¹)^{n−1}`. -/
lemma ItermG_abs_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ |q| ^ (-((m : ℤ) + n)) * (2 * |q|⁻¹) ^ (n - 1) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  rw [ItermG, abs_mul, abs_neg]
  have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ |q| ^ (-((m : ℤ) + n)) := inv_cqpow_le_abs hq hC (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ (2 * |q|⁻¹) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), (2 * |q|⁻¹) :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_bound_abs hq hC hk.1 (by omega))
      _ = (2 * |q|⁻¹) ^ (n - 1) := by rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ |q| ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos (by linarith) _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- The reindexed term `ItermG q C n (n+j)` is bounded by `(|q|⁻¹)^j` (negative base). The `(2|q|⁻¹)^{n−1}`
constant is `≤ 1` because `2|q|⁻¹ ≤ 1`, so the geometric majorant is recovered exactly. -/
lemma ItermG_shift_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    |ItermG q C n (n + j)| ≤ (|q|⁻¹) ^ j := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have h := ItermG_abs_le_abs hq hC hn (Nat.le_add_right n j)
  have hexp : |q| ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ |q| ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt hqabs1); push_cast; omega
  have hjeq : |q| ^ (-(j : ℤ)) = (|q|⁻¹) ^ j := by rw [zpow_neg, zpow_natCast, inv_pow]
  have hconst : (2 * |q|⁻¹) ≤ 1 := by
    have hinv : |q|⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
    calc 2 * |q|⁻¹ ≤ 2 * (2 : ℝ)⁻¹ := by linarith
      _ = 1 := by norm_num
  have hconst' : (2 * |q|⁻¹) ^ (n - 1) ≤ 1 := pow_le_one₀ (by positivity) hconst
  calc |ItermG q C n (n + j)| ≤ |q| ^ (-(((n + j : ℕ) : ℤ) + n)) * (2 * |q|⁻¹) ^ (n - 1) := h
    _ ≤ |q| ^ (-(j : ℤ)) * 1 :=
        mul_le_mul hexp hconst' (by positivity) (le_of_lt (zpow_pos (by linarith) _))
    _ = (|q|⁻¹) ^ j := by rw [mul_one, hjeq]

/-- **Error series summable, negative base** `q ≤ -2` (`2 ≤ |q|`, `2 < |C|`, `n ≥ 1`). The Lemma-4
convergence half for the negative-base regime. -/
lemma EtermG_summable_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun j => ItermG q C n (n + j)) := by
  have hr : |q|⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  apply Summable.of_norm_bounded (g := fun j => (|q|⁻¹) ^ j)
  · exact summable_geometric_of_lt_one (by positivity) hr
  · intro j; rw [Real.norm_eq_abs]; exact ItermG_shift_le_abs hq hC hn j

/-! ### Sharp negative-base error bound (Lemma 4 endgame for `q ≤ -2`). -/

/-- Sharp per-factor bound (negative base): `|(1−q^{k−m})(1−C·q^{k+m})⁻¹| ≤ 2·(|q|^{k+m})⁻¹`. -/
lemma factor_abs_le_sharp_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ 2 * (|q| ^ (k + m))⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  rw [abs_mul]
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 2 := by
    have hle1 : |q| ^ ((k : ℤ) - m) ≤ 1 := by
      calc |q| ^ ((k : ℤ) - m) ≤ |q| ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
        _ = 1 := by norm_num
    calc |1 - q ^ ((k : ℤ) - m)| = |(1 : ℝ) + -(q ^ ((k : ℤ) - m))| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-(q ^ ((k : ℤ) - m))| := abs_add_le _ _
      _ = 1 + |q| ^ ((k : ℤ) - m) := by rw [abs_one, abs_neg, abs_zpow]
      _ ≤ 2 := by linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ |q| ^ (-((k : ℤ) + m)) := inv_cqpow_le_abs hq hC (by omega)
  have h3 : |q| ^ (-((k : ℤ) + m)) = (|q| ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast |q| (k + m), Nat.cast_add]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 2 * |q| ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 2 * (|q| ^ (k + m))⁻¹ := by rw [h3]

/-- Closed-form sharp per-term bound (negative base): `|Iₘ| ≤ 2^{n−1}·Cₙ·((|q|^n)⁻¹)^m` with
`Cₙ = (|q|^{n + ∑_{k<n} k})⁻¹`. The `2^{n−1}` (one `2` per cross factor) is a harmless constant. -/
lemma ItermG_abs_le_geom_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ m := by
  have hqabs : (0 : ℝ) < |q| := by linarith
  have hsharp : |ItermG q C n m|
      ≤ (|q| ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (2 * (|q| ^ (k + m))⁻¹) := by
    rw [ItermG, abs_mul, abs_neg]
    have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ (|q| ^ (m + n))⁻¹ := by
      have h := inv_cqpow_le_abs hq hC (a := (m : ℤ) + n) (by omega)
      have he : |q| ^ (-((m : ℤ) + n)) = (|q| ^ (m + n))⁻¹ := by
        rw [zpow_neg, ← zpow_natCast |q| (m + n), Nat.cast_add]
      rwa [he] at h
    have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (2 * (|q| ^ (k + m))⁻¹) := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k hk; rw [Finset.mem_Icc] at hk
      exact factor_abs_le_sharp_abs hq hC hk.1 (by omega)
    exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos hqabs _)))
  refine hsharp.trans (le_of_eq ?_)
  have hL : (|q| ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (2 * (|q| ^ (k + m))⁻¹)
      = 2 ^ (n - 1) * (|q| ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel,
      Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
    rw [show (|q| ^ (m + n))⁻¹ * (2 ^ (n - 1) * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹)
          = 2 ^ (n - 1) * ((|q| ^ (m + n))⁻¹ * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹) from by
        ring]
    rw [← mul_inv, ← pow_add]
  have hR : 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ m
      = 2 ^ (n - 1) * (|q| ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_assoc, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- The error bound (negative base): `|Eₙ| ≤ 2^{n−1}·Cₙ·(|q|^{-n})ⁿ·(1 − |q|^{-n})⁻¹`. -/
lemma EtermG_abs_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ n
        * (1 - (|q| ^ n)⁻¹)⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hr1lt : |q|⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  set r : ℝ := (|q| ^ n)⁻¹ with hr_def
  set Cn : ℝ := 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos hqpos n))
  have hqn1 : (1 : ℝ) < |q| ^ n := by
    calc (1 : ℝ) < |q| := hqabs1
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ n := pow_le_pow_right₀ (le_of_lt hqabs1) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |ItermG q C n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ItermG_shift_le_abs hq hC hn j)
      (summable_geometric_of_lt_one (by positivity) hr1lt)
  have h1 : |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => ItermG q C n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [EtermG, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |ItermG q C n (n + j)| ≤ Cn * r ^ (n + j) := fun j => by
    have h := ItermG_abs_le_geom_abs hq hC hn (Nat.le_add_right n j)
    rw [hCn_def, hr_def]; exact h
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |ItermG q C n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed-form error bound (negative base): `|Eₙ| ≤ 2ⁿ·(|q|^{n + ∑_{k<n}k + n²})⁻¹`. -/
lemma EtermG_abs_le'_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ 2 ^ n * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  refine (EtermG_abs_le_abs hq hC hn).trans ?_
  have hC' : (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ n
      = (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ |q| ^ n := by
    calc (2 : ℝ) ≤ |q| := hq
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ n := pow_le_pow_right₀ (le_of_lt hqabs1) hn
  have h1 : (|q| ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (|q| ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (|q| ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    have := pow_pos hqpos (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2); positivity
  have h2n : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
  calc 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ n
        * (1 - (|q| ^ n)⁻¹)⁻¹
      = 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
          * (1 - (|q| ^ n)⁻¹)⁻¹ := by rw [mul_assoc (2 ^ (n - 1)), hC']
    _ ≤ 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 ^ n * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
        rw [show 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2
              = 2 ^ (n - 1) * 2 * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ from by ring,
          h2n]

/-- The leading factor `(1 − C·q^a)⁻¹` is negative for `a ≥ 1`, `C > 2`. -/
lemma leading_negG (hq : 2 ≤ q) (hC : 2 < C) {a : ℤ} (ha : 1 ≤ a) : (1 - C * q ^ a)⁻¹ < 0 := by
  have h2 : (2 : ℝ) ≤ q ^ a := qzpow_ge_two hq ha
  have hneg : (1 - C * q ^ a) < 0 := by nlinarith [h2, hC, zpow_pos (show (0:ℝ) < q by linarith) a]
  exact inv_neg''.mpr hneg

/-- Each product factor `(1 − q^{k−m})·(1 − C·q^{k+m})⁻¹` is negative for `1 ≤ k < m`. -/
lemma factor_negG (hq : 2 ≤ q) (hC : 2 < C) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹ < 0 := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hnum : 0 < 1 - q ^ ((k : ℤ) - m) := by
    have hle : q ^ ((k : ℤ) - m) ≤ q ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
    rw [zpow_zero] at hle
    have hpos : 0 < q ^ ((k : ℤ) - m) := zpow_pos (by linarith) _
    -- strict: the exponent is < 0, so q^{k-m} < 1
    have hlt : q ^ ((k : ℤ) - m) < 1 := by
      have : q ^ ((k : ℤ) - m) ≤ q ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
      have hq1' : q ^ (-1 : ℤ) < 1 := by
        rw [zpow_neg, zpow_one]; rw [inv_lt_one_iff₀]; right; linarith
      linarith
    linarith
  exact mul_neg_of_pos_of_neg hnum (leading_negG hq hC (by omega))

/-- `(-1)^{n-1}` times the product of the `n−1` (negative) factors is positive. -/
lemma prod_factor_signG (hq : 2 ≤ q) (hC : 2 < C) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹ := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h1 : (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) := by
    rw [Finset.prod_const, hcard]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hf := factor_negG hq hC hk.1 (show k < m by omega)
  linarith

/-- The sign of `ItermG q C n m` (for `m ≥ n ≥ 1`) is exactly `(-1)^{n-1}`, nonzero. -/
lemma ItermG_sign (hq : 2 ≤ q) (hC : 2 < C) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ItermG q C n m := by
  rw [ItermG]
  have hL : (1 - C * q ^ ((m : ℤ) + n))⁻¹ < 0 := leading_negG hq hC (by omega)
  have hP := prod_factor_signG hq hC hn hnm
  have hnegL : (0 : ℝ) < -(1 - C * q ^ ((m : ℤ) + n))⁻¹ := by linarith
  have := mul_pos hnegL hP
  convert this using 1 <;> first | rfl | ring

/-! ### Summable geometric majorant `|ItermG q C n (n+j)| ≤ (q⁻¹)^j`. -/

/-- Each product factor has absolute value at most `q⁻¹` (for `1 ≤ k < m`, `q ≥ 2`, `C > 2`). -/
lemma factor_boundG (hq : 2 ≤ q) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ q⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  rw [abs_mul]
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : q ^ ((k : ℤ) - m) ≤ 1 := by
      calc q ^ ((k : ℤ) - m) ≤ q ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) hexp
        _ = 1 := by norm_num
    have hpos : 0 < q ^ ((k : ℤ) - m) := zpow_pos (by linarith) _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ q ^ (-((k : ℤ) + m)) := inv_cqpowG_le hq hC (by omega)
  have h3 : q ^ (-((k : ℤ) + m)) ≤ q⁻¹ := by
    calc q ^ (-((k : ℤ) + m)) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
      _ = q⁻¹ := by rw [zpow_neg, zpow_one]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * q⁻¹ := mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
    _ = q⁻¹ := by ring

/-- Crude per-term bound: `|ItermG q C n m| ≤ q^{-(m+n)}·(q⁻¹)^{n-1}` for `1 ≤ n ≤ m`. -/
lemma ItermG_abs_le (hq : 2 ≤ q) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ q ^ (-((m : ℤ) + n)) * (q⁻¹) ^ (n - 1) := by
  have hq1 : (1 : ℝ) < q := by linarith
  rw [ItermG, abs_mul, abs_neg]
  have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ q ^ (-((m : ℤ) + n)) := inv_cqpowG_le hq hC (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ (q⁻¹) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), q⁻¹ :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_boundG hq hC hk.1 (by omega))
      _ = (q⁻¹) ^ (Finset.Icc 1 (n - 1)).card := by rw [Finset.prod_const]
      _ = (q⁻¹) ^ (n - 1) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ q ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos (by linarith) _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- The reindexed term `ItermG q C n (n+j)` is bounded by `(q⁻¹)^j`. -/
lemma ItermG_shift_le (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    |ItermG q C n (n + j)| ≤ (q⁻¹) ^ j := by
  have hq1 : (1 : ℝ) < q := by linarith
  have h := ItermG_abs_le hq hC hn (Nat.le_add_right n j)
  have hexp : q ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ q ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt hq1)
    push_cast; omega
  have hpow1 : (q⁻¹) ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [inv_le_one_iff₀]; right; linarith)
  have hjeq : q ^ (-(j : ℤ)) = (q⁻¹) ^ j := by rw [zpow_neg, zpow_natCast, inv_pow]
  calc |ItermG q C n (n + j)| ≤ q ^ (-(((n + j : ℕ) : ℤ) + n)) * (q⁻¹) ^ (n - 1) := h
    _ ≤ q ^ (-(j : ℤ)) * 1 := mul_le_mul hexp hpow1 (by positivity) (le_of_lt (zpow_pos (by linarith) _))
    _ = (q⁻¹) ^ j := by rw [mul_one, hjeq]

/-- The error series `EtermG q C n = ∑_j ItermG q C n (n+j)` is summable (`q ≥ 2, C > 2`). The
Lemma-4 convergence half. -/
lemma EtermG_summable (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun j => ItermG q C n (n + j)) := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hr : q⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  apply Summable.of_norm_bounded (g := fun j => (q⁻¹) ^ j)
  · exact summable_geometric_of_lt_one (by positivity) hr
  · intro j; rw [Real.norm_eq_abs]; exact ItermG_shift_le hq hC hn j

/-- **Borwein Lemma 5 (non-vanishing), general `(q,C)`.** `EtermG q C n ≠ 0` for `n ≥ 1`, `q ≥ 2`,
`C > 2`: the error is a tsum of same-sign nonzero terms `(-1)^{n-1}·ItermG > 0`. -/
theorem EtermG_ne_zero (hq : 2 ≤ q) (hC : 2 < C) {n : ℕ} (hn : 1 ≤ n) : EtermG q C n ≠ 0 := by
  have hCabs : 2 < |C| := by rw [abs_of_pos (by linarith)]; exact hC
  have hsum : Summable (fun j => (-1 : ℝ) ^ (n - 1) * ItermG q C n (n + j)) :=
    (EtermG_summable hq hCabs hn).mul_left _
  have hpos : ∀ j, 0 < (-1 : ℝ) ^ (n - 1) * ItermG q C n (n + j) :=
    fun j => ItermG_sign hq hC hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, (-1 : ℝ) ^ (n - 1) * ItermG q C n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, ItermG q C n (n + j)) = EtermG q C n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/-! ### Negative regime `C < -2`: non-vanishing (no alternation — all terms same sign). -/

/-- For `C < -2`, `q ≥ 2`: every term `ItermG q C n m` is strictly negative (`1 ≤ n ≤ m`). The leading
inverse and each product factor are positive (since `C < 0`), so `ItermG = -(positive) < 0`. -/
lemma ItermG_neg (hq : 2 ≤ q) (hC : C < -2) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    ItermG q C n m < 0 := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hL : 0 < (1 - C * q ^ ((m : ℤ) + n))⁻¹ := by
    apply inv_pos.mpr
    nlinarith [zpow_pos hqpos ((m : ℤ) + n), hC,
      mul_pos (show (0 : ℝ) < -C by linarith) (zpow_pos hqpos ((m : ℤ) + n))]
  have hPprod : 0 < ∏ k ∈ Finset.Icc 1 (n - 1),
      (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹ := by
    apply Finset.prod_pos
    intro k hk; rw [Finset.mem_Icc] at hk
    have hf1 : 0 < 1 - q ^ ((k : ℤ) - m) := by
      have hle : q ^ ((k : ℤ) - m) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
      have hlt1 : q ^ (-1 : ℤ) < 1 := by rw [zpow_neg, zpow_one, inv_lt_one_iff₀]; right; linarith
      linarith
    have hf2 : 0 < (1 - C * q ^ ((k : ℤ) + m))⁻¹ := by
      apply inv_pos.mpr
      nlinarith [zpow_pos hqpos ((k : ℤ) + m), hC,
        mul_pos (show (0 : ℝ) < -C by linarith) (zpow_pos hqpos ((k : ℤ) + m))]
    exact mul_pos hf1 hf2
  rw [ItermG, neg_mul]
  have := mul_pos hL hPprod
  linarith

/-- **Borwein Lemma 5 (non-vanishing), negative regime.** `EtermG q C n ≠ 0` for `n ≥ 1`, `q ≥ 2`,
`C < -2`: the error is a tsum of strictly negative summable terms. -/
theorem EtermG_ne_zero_neg (hq : 2 ≤ q) (hC : C < -2) {n : ℕ} (hn : 1 ≤ n) : EtermG q C n ≠ 0 := by
  have hCabs : 2 < |C| := by rw [abs_of_neg (by linarith)]; linarith
  have hsum : Summable (fun j => ItermG q C n (n + j)) := EtermG_summable hq hCabs hn
  have hneg : ∀ j, ItermG q C n (n + j) < 0 := fun j => ItermG_neg hq hC hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, -ItermG q C n (n + j) :=
    hsum.neg.tsum_pos (fun j => by linarith [hneg j]) 0 (by linarith [hneg 0])
  rw [tsum_neg] at hp
  intro h0
  rw [show (∑' j, ItermG q C n (n + j)) = EtermG q C n from rfl, h0, neg_zero] at hp
  exact lt_irrefl 0 hp

/-! ### Negative BASE `q ≤ -2` non-vanishing (Borwein Lemma 5): the sign DICHOTOMY.

For negative base the powers `q^a` alternate, so terms `Iₙ(n+j)` do NOT share a sign. The exact
structure (worked out and numerically verified): with the cross factors `1 − q^{k−m}` always
positive (`one_sub_qzpow_pos`) and each inverse factor `(1 − C·q^a)⁻¹` carrying the sign
`sign(C)·(−1)^{a+1}` (since `|C·q^a| > 1`), the sign of `Iₙ(n+j)` is `sₙ·(−1)^{n·j}` for a fixed
`sₙ`. Hence the **dichotomy**: `n` even ⟹ all terms share sign `sₙ` (same-sign tsum, `≠ 0`);
`n` odd ⟹ terms alternate (alternating-series bracket, `≠ 0`).

The bookkeeping is captured by an explicit sign multiplier `EsignG C n m` with
`0 < EsignG C n m · Iₙ(m)` and the recurrence `EsignG C n (m+1) = (−1)^n · EsignG C n m`. -/

/-- If `0 < z·w` then `0 < z·w⁻¹` (same-sign of `w` and `w⁻¹`). -/
lemma pos_of_pos_mul_inv {z w : ℝ} (h : 0 < z * w) : 0 < z * w⁻¹ := by
  rw [← div_eq_mul_inv, div_pos_iff]
  rcases mul_pos_iff.mp h with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · exact Or.inl ⟨hz, hw⟩
  · exact Or.inr ⟨hz, hw⟩

/-- **Inverse-factor sign (negative base).** For `q ≤ -2`, `2 < |C|`, `a ≥ 1`:
`0 < C·(−1)^{a+1}·(1 − C·q^a)⁻¹`. Writing `q^a = (−1)^a·|q|^a`, the factor `1 − C·q^a` has sign
`sign(C)·(−1)^{a+1}` (its magnitude exceeds `1`), matching the multiplier `C·(−1)^{a+1}`. -/
lemma inv_factor_sign_neg (hq : q ≤ -2) (hC : 2 < |C|) (a : ℕ) (ha : 1 ≤ a) :
    0 < C * (-1) ^ (a + 1) * (1 - C * q ^ a)⁻¹ := by
  have hqneg : q < 0 := by linarith
  have habs : |q| = -q := abs_of_neg hqneg
  have hq2 : (2 : ℝ) ≤ |q| := by rw [habs]; linarith
  have hCsq : (4 : ℝ) < C ^ 2 := by nlinarith [hC, abs_nonneg C, sq_abs C]
  have hq_eq : q = -|q| := by rw [habs]; ring
  set s : ℝ := (-1) ^ a with hs
  set Q : ℝ := |q| ^ a with hQdef
  have hss : s ^ 2 = 1 := by rw [hs, ← pow_mul]; exact Even.neg_one_pow ⟨a, by ring⟩
  have hQ2 : (2 : ℝ) ≤ Q := by
    rw [hQdef]
    calc (2 : ℝ) ≤ |q| := hq2
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ a := pow_le_pow_right₀ (by linarith) ha
  have hqa : q ^ a = s * Q := by
    rw [hs, hQdef]
    conv_lhs => rw [hq_eq]
    rw [neg_pow]
  have key : 0 < (C * (-1) ^ (a + 1)) * (1 - C * q ^ a) := by
    have hexp : (-1 : ℝ) ^ (a + 1) = -s := by rw [pow_succ, hs]; ring
    rw [hexp, hqa]
    have heq : (C * -s) * (1 - C * (s * Q)) = -(C * s) + C ^ 2 * s ^ 2 * Q := by ring
    rw [heq, hss, mul_one]
    have hbound : 2 * (C * s) ≤ C ^ 2 + 1 := by nlinarith [sq_nonneg (C * s - 1), hss, sq_nonneg C]
    nlinarith [hbound, hQ2, hCsq, sq_nonneg C]
  exact pos_of_pos_mul_inv key

/-! The explicit per-`m` sign multiplier. `EsignG C n m · Iₙ(m) > 0`, and the recurrence
`EsignG C n (m+1) = (−1)^n · EsignG C n m` gives `EsignG C n (n+j) = (−1)^{nj}·EsignG C n n`. -/

/-- Sign multiplier making `EsignG C n m · ItermG q C n m > 0` for negative base. -/
noncomputable def EsignG (C : ℝ) (n m : ℕ) : ℝ :=
  -C ^ n * (-1) ^ (m + n + 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + m + 1)

/-- **The per-term sign positivity (negative base).** `0 < EsignG C n m · Iₙ(m)` for `q ≤ -2`,
`2 < |C|`, `1 ≤ n ≤ m`. The cross factors `1 − q^{k−m} > 0`, the leading & inner inverse factors
each pair with their `C·(−1)^{a+1}` multiplier into a positive (`inv_factor_sign_neg`). -/
lemma ItermG_sign_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < EsignG C n m * ItermG q C n m := by
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg (show q < 0 by linarith)]; linarith
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hCn : C ^ n = C * ∏ _k ∈ Finset.Icc 1 (n - 1), C := by
    rw [Finset.prod_const, hcard, ← pow_succ', Nat.sub_add_cancel hn]
  -- leading positive bracket
  have hlead : 0 < C * (-1) ^ (m + n + 1) * (1 - C * q ^ ((m : ℤ) + n))⁻¹ := by
    have h := inv_factor_sign_neg hq hC (m + n) (by omega)
    rwa [show q ^ (m + n) = q ^ ((m : ℤ) + n) by rw [← Nat.cast_add, zpow_natCast]] at h
  -- each positive `k`-bracket
  have hk : ∀ k ∈ Finset.Icc 1 (n - 1),
      0 < C * (-1) ^ (k + m + 1) * ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹) := by
    intro k hk'
    rw [Finset.mem_Icc] at hk'
    have hkm : k < m := by omega
    have h1 := inv_factor_sign_neg hq hC (k + m) (by omega)
    rw [show q ^ (k + m) = q ^ ((k : ℤ) + m) by rw [← Nat.cast_add, zpow_natCast]] at h1
    have h2 := one_sub_qzpow_pos hqabs hkm
    nlinarith [mul_pos h1 h2]
  -- the product identity, then positivity
  have hsplit : ∏ k ∈ Finset.Icc 1 (n - 1),
        (C * (-1) ^ (k + m + 1) * ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹))
      = (∏ _k ∈ Finset.Icc 1 (n - 1), C) * (∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + m + 1))
        * (∏ k ∈ Finset.Icc 1 (n - 1), ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have heq : EsignG C n m * ItermG q C n m
      = (C * (-1) ^ (m + n + 1) * (1 - C * q ^ ((m : ℤ) + n))⁻¹)
        * ∏ k ∈ Finset.Icc 1 (n - 1),
            (C * (-1) ^ (k + m + 1) * ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹)) := by
    rw [hsplit, EsignG, ItermG, hCn]; ring
  rw [heq]
  exact mul_pos hlead (Finset.prod_pos hk)

/-- **Sign recurrence**: `EsignG C n (m+1) = (−1)^n · EsignG C n m`. Each `(−1)`-exponent in the
multiplier gains one `m`, and there are exactly `1 + (n−1) = n` of them. -/
lemma EsignG_step {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    EsignG C n (m + 1) = (-1) ^ n * EsignG C n m := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hprod : ∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + (m + 1) + 1)
      = (∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + m + 1)) * (-1) ^ (n - 1) := by
    rw [show (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) by rw [Finset.prod_const, hcard],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => by rw [show k + (m + 1) + 1 = (k + m + 1) + 1 from by ring, pow_succ])
  rw [EsignG, EsignG, hprod,
    show (-1 : ℝ) ^ (m + 1 + n + 1) = (-1) ^ (m + n + 1) * (-1) by
      rw [show m + 1 + n + 1 = (m + n + 1) + 1 from by ring, pow_succ],
    show (-1 : ℝ) ^ n = (-1) ^ (n - 1) * (-1) by rw [← pow_succ, Nat.sub_add_cancel hn]]
  ring

/-- `EsignG C n (n+j) = (−1)^{nj} · EsignG C n n`. -/
lemma EsignG_shift {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    EsignG C n (n + j) = (-1) ^ (n * j) * EsignG C n n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show n + (j + 1) = (n + j) + 1 from by ring, EsignG_step hn, ih, ← mul_assoc, ← pow_add,
      show n * (j + 1) = n + n * j from by ring]

/-- **Lemma 5, negative base, `n` even.** `(−1)^{nj}=1`, so all terms `EsignG C n n · Iₙ(n+j)`
are strictly positive ⟹ the error tsum is nonzero. -/
theorem EtermG_ne_zero_even_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n : ℕ}
    (hn : 1 ≤ n) (hne : Even n) : EtermG q C n ≠ 0 := by
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg (show q < 0 by linarith)]; linarith
  have hpos : ∀ j, 0 < EsignG C n n * ItermG q C n (n + j) := by
    intro j
    have h := ItermG_sign_negbase hq hC hn (Nat.le_add_right n j)
    rwa [EsignG_shift hn, Even.neg_one_pow (hne.mul_right j), one_mul] at h
  have hsum : Summable (fun j => EsignG C n n * ItermG q C n (n + j)) :=
    (EtermG_summable_abs hqabs hC hn).mul_left _
  have hp : 0 < ∑' j, EsignG C n n * ItermG q C n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, ItermG q C n (n + j)) = EtermG q C n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/-! ### Magnitude antitonicity `|Iₙ(m+1)| < |Iₙ(m)|` (negative base) — the odd-case prerequisite.

The consecutive ratio of magnitudes **telescopes**: the inverse factors form a contiguous block
`∏_{a=M+1}^{M+n}|1−C·q^a|⁻¹` and the cross factors a contiguous block, so
`|Iₙ(m+1)|/|Iₙ(m)| = [|1−q^{−m}|·|1−C·q^{m+1}|] / [|1−q^{(n−1)−m}|·|1−C·q^{m+n+1}|]`, reducing the whole
inequality to the single two-factor estimate `|1−q^{−m}|·|1−C·q^{m+1}| < |1−q^{(n−1)−m}|·|1−C·q^{m+n+1}|`
(split `n=1` / `n≥2`). -/

/-- Magnitude factorization `|Iₙ(M)| = (∏ cross)·∏ inv`. -/
lemma ItermG_abs_factor (n M : ℕ) (hn : 1 ≤ n) :
    |ItermG q C n M|
      = (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - M)|)
        * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + M)|⁻¹ := by
  rw [ItermG_prod_form n M hn, abs_neg, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  exact Finset.prod_congr rfl (fun k _ => abs_inv _)

/-- Generic shift-telescope over `range`: `(∏_{i<N} g i)·g N = (∏_{i<N} g(i+1))·g 0`. -/
lemma prod_range_shift_telescope (g : ℕ → ℝ) (N : ℕ) :
    (∏ i ∈ Finset.range N, g i) * g N = (∏ i ∈ Finset.range N, g (i + 1)) * g 0 := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']

/-- `∏_{k∈Icc 1 N} f k = ∏_{i<N} f (i+1)`. -/
lemma prod_Icc_one_eq_range (f : ℕ → ℝ) (N : ℕ) :
    ∏ k ∈ Finset.Icc 1 N, f k = ∏ i ∈ Finset.range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Finset.prod_range_succ]

/-- Cross-factor telescoping: `Across(m+1)·c(n−1−m) = Across(m)·c(−m)`. -/
lemma cross_telescopeG (q : ℝ) (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - ((m + 1 : ℕ) : ℤ))|)
        * |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))|
      = (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m : ℤ))|)
        * |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| := by
  rw [prod_Icc_one_eq_range, prod_Icc_one_eq_range]
  have key := prod_range_shift_telescope (fun i => |1 - q ^ ((i : ℤ) - (m : ℤ))|) (n - 1)
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring_nf)
  · rfl

/-- Inverse-denominator telescoping: `Dinv(m+1)·d(m+1) = Dinv(m)·d(m+n+1)`. -/
lemma inv_telescopeG (q C : ℝ) (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + ((m + 1 : ℕ) : ℤ))|)
        * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
      = (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m : ℤ))|)
        * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
  rw [prod_Icc_one_eq_range, prod_Icc_one_eq_range]
  have key := prod_range_shift_telescope (fun i => |1 - C * q ^ ((i : ℤ) + ((m + 1 : ℕ) : ℤ))|) n
  refine Eq.trans ?_ (key.symm.trans ?_)
  · rfl
  · congr 1
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring_nf)

/-- The **reduced two-factor inequality**: `|1−q^{−m}|·|1−C·q^{m+1}| < |1−q^{(n−1)−m}|·|1−C·q^{m+n+1}|`,
to which the whole magnitude antitonicity collapses after telescoping. Split `n=1` (cross factors equal,
reduce to the inverse comparison) / `n≥2` (crude `3/2`,`1/2` cross bounds, since `|q|^n ≥ 4`). -/
lemma reduced_two_factor (hq : q ≤ -2) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
      < |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
  have hqneg : q < 0 := by linarith
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg hqneg]; linarith
  have hq1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hq0 : |q| ≠ 0 := by linarith
  have hCpos : (0 : ℝ) < |C| := by linarith
  -- triangle helpers
  have tri_up : ∀ x : ℝ, |1 - x| ≤ 1 + |x| := fun x => by
    calc |1 - x| = |(1 : ℝ) + (-x)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |-x| := abs_add_le _ _
      _ = 1 + |x| := by rw [abs_one, abs_neg]
  have tri_lo : ∀ x : ℝ, 1 - |x| ≤ |1 - x| := fun x => by
    have := abs_sub_abs_le_abs_sub (1 : ℝ) x; rw [abs_one] at this; linarith
  -- cross-factor bounds (exponent ≤ -1)
  have cross_le : ∀ e : ℤ, e ≤ -1 → |1 - q ^ e| ≤ 3 / 2 := by
    intro e he
    have hqe : |q| ^ e ≤ 1 / 2 := by
      calc |q| ^ e ≤ |q| ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) he
        _ = |q|⁻¹ := by rw [zpow_neg, zpow_one]
        _ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqabs
    calc |1 - q ^ e| ≤ 1 + |q ^ e| := tri_up _
      _ = 1 + |q| ^ e := by rw [abs_zpow]
      _ ≤ 3 / 2 := by linarith
  have cross_ge : ∀ e : ℤ, e ≤ -1 → 1 / 2 ≤ |1 - q ^ e| := by
    intro e he
    have hqe : |q| ^ e ≤ 1 / 2 := by
      calc |q| ^ e ≤ |q| ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) he
        _ = |q|⁻¹ := by rw [zpow_neg, zpow_one]
        _ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqabs
    calc (1 : ℝ) / 2 ≤ 1 - |q| ^ e := by linarith
      _ = 1 - |q ^ e| := by rw [abs_zpow]
      _ ≤ |1 - q ^ e| := tri_lo _
  have cross_pos : ∀ e : ℤ, e ≤ -1 → 0 < |1 - q ^ e| := fun e he => by
    have := cross_ge e he; linarith
  -- inverse-denominator bounds (exponent ≥ 1)
  have inv_le : ∀ a : ℤ, |1 - C * q ^ a| ≤ 1 + |C| * |q| ^ a := fun a => by
    calc |1 - C * q ^ a| ≤ 1 + |C * q ^ a| := tri_up _
      _ = 1 + |C| * |q| ^ a := by rw [abs_mul, abs_zpow]
  have inv_ge : ∀ a : ℤ, |C| * |q| ^ a - 1 ≤ |1 - C * q ^ a| := fun a => by
    have h2 := abs_sub_abs_le_abs_sub (C * q ^ a) 1
    rw [abs_one, abs_sub_comm] at h2
    calc |C| * |q| ^ a - 1 = |C * q ^ a| - 1 := by rw [abs_mul, abs_zpow]
      _ ≤ |1 - C * q ^ a| := h2
  -- abbreviations
  set P : ℝ := |C| * |q| ^ (m + 1) with hP
  have hqm1 : (4 : ℝ) ≤ |q| ^ (m + 1) := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ |q| * |q| := by nlinarith [hqabs]
      _ = |q| ^ 2 := by ring
      _ ≤ |q| ^ (m + 1) := pow_le_pow_right₀ (le_of_lt hq1) (by omega)
  have hP8 : (8 : ℝ) ≤ P := by rw [hP]; nlinarith [hqm1, hC, hCpos]
  -- D0 = |1 - C q^{m+1}|, exponent normalizations
  have hexpD0 : (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ)) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  have hD0le : |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| ≤ P + 1 := by
    rw [hexpD0, zpow_natCast, hP]
    have h := inv_le ((m + 1 : ℕ) : ℤ)
    rw [zpow_natCast, zpow_natCast] at h
    linarith [h]
  have hD0pos : 0 < |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
    rw [hexpD0]; apply abs_pos.mpr; rw [sub_ne_zero]
    intro h
    have hmag : |C * q ^ ((m + 1 : ℕ) : ℤ)| = |C| * |q| ^ (m + 1) := by rw [abs_mul, abs_zpow, zpow_natCast]
    have : |C * q ^ ((m + 1 : ℕ) : ℤ)| = 1 := by rw [← h, abs_one]
    rw [hmag] at this; nlinarith [hqm1, hC, hCpos, this]
  -- A0 = |1 - q^{-m}|
  have hA0pos : 0 < |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| := cross_pos _ (by push_cast; omega)
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · -- n = 1: cross factors coincide, reduce to D0 < D1
    subst hn1
    have hDn : |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| ≥ 2 * P - 1 := by
      have he : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [he]
      have := inv_ge ((m + 2 : ℕ) : ℤ)
      rw [zpow_natCast] at this
      have h2 : |q| ^ (m + 2) = |q| * |q| ^ (m + 1) := by rw [pow_succ]; ring
      rw [hP]; nlinarith [this, h2, hqabs, hCpos, mul_pos hCpos (pow_pos hqpos (m + 1))]
    have : |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| < |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
      have h1 := hD0le; nlinarith [h1, hDn, hP8]
    calc |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
        < |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| :=
          mul_lt_mul_of_pos_left this hA0pos
      _ = |1 - q ^ (((1 - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
          norm_num
  · -- n ≥ 2: crude bounds
    have hA0le : |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| ≤ 3 / 2 := cross_le _ (by push_cast; omega)
    have hAnge : 1 / 2 ≤ |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| := cross_ge _ (by
      have : (1 : ℕ) ≤ n - 1 := by omega
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; omega)
    have hqn4 : (4 : ℝ) ≤ |q| ^ n := by
      calc (4 : ℝ) = 2 * 2 := by norm_num
        _ ≤ |q| * |q| := by nlinarith [hqabs]
        _ = |q| ^ 2 := by ring
        _ ≤ |q| ^ n := pow_le_pow_right₀ (le_of_lt hq1) (by omega)
    have hDnge : P * |q| ^ n - 1 ≤ |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
      have he : (n : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + (n : ℤ) := by push_cast; ring
      rw [he]
      have hzadd : |q| ^ (((m + 1 : ℕ) : ℤ) + (n : ℤ)) = |q| ^ (m + 1) * |q| ^ n := by
        rw [zpow_add₀ hq0, zpow_natCast, zpow_natCast]
      have hge := inv_ge (((m + 1 : ℕ) : ℤ) + (n : ℤ))
      rw [hzadd] at hge
      rw [hP]; nlinarith [hge]
    have hD0nn : (0 : ℝ) ≤ P + 1 := by linarith [hP8]
    have hub : |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
        ≤ (3 / 2) * (P + 1) :=
      mul_le_mul hA0le hD0le (le_of_lt hD0pos) (by norm_num)
    have hPqn0 : (0 : ℝ) ≤ P * |q| ^ n - 1 := by nlinarith [hP8, hqn4]
    have hlb : (1 / 2) * (P * |q| ^ n - 1)
        ≤ |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| :=
      mul_le_mul hAnge hDnge hPqn0 (by linarith [hAnge])
    have hmid : (3 / 2) * (P + 1) < (1 / 2) * (P * |q| ^ n - 1) := by
      nlinarith [hP8, hqn4, mul_nonneg (show (0:ℝ) ≤ P by linarith) (show (0:ℝ) ≤ |q| ^ n - 4 by linarith)]
    exact (hub.trans_lt hmid).trans_le hlb

/-- **Magnitude antitonicity (negative base).** `|Iₙ(m+1)| < |Iₙ(m)|` for `q ≤ -2`, `2 < |C|`,
`1 ≤ n ≤ m`. The consecutive ratio telescopes (`cross_telescopeG`, `inv_telescopeG`) and collapses to
`reduced_two_factor`. This is the odd-case prerequisite for non-vanishing. -/
lemma ItermG_abs_anti_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n (m + 1)| < |ItermG q C n m| := by
  have hqneg : q < 0 := by linarith
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg hqneg]; linarith
  have hq1 : (1 : ℝ) < |q| := by linarith
  have hCpos : (0 : ℝ) < |C| := by linarith
  -- positivity of factors
  have cross_pos : ∀ M k : ℕ, k < M → 0 < |1 - q ^ ((k : ℤ) - M)| := by
    intro M k hkM; rw [abs_of_pos (one_sub_qzpow_pos hqabs hkM)]; exact one_sub_qzpow_pos hqabs hkM
  have inv_pos' : ∀ a : ℤ, 1 ≤ a → 0 < |1 - C * q ^ a| := by
    intro a ha
    rw [abs_pos, sub_ne_zero]; intro h
    have hqa : (2 : ℝ) ≤ |q| ^ a := by
      calc (2 : ℝ) ≤ |q| := hqabs
        _ = |q| ^ (1 : ℤ) := (zpow_one _).symm
        _ ≤ |q| ^ a := zpow_le_zpow_right₀ (le_of_lt hq1) ha
    have hmag : |C * q ^ a| = |C| * |q| ^ a := by rw [abs_mul, abs_zpow]
    have heq1 : |C| * |q| ^ a = 1 := by rw [← hmag, ← h, abs_one]
    nlinarith [hqa, hC, hCpos, heq1, mul_le_mul (le_of_lt hC) hqa (by norm_num) (le_of_lt hCpos)]
  have hDinv_pos : ∀ M : ℕ, 0 < ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + M)| := fun M => by
    apply Finset.prod_pos; intro k hk; rw [Finset.mem_Icc] at hk; exact inv_pos' _ (by omega)
  have hAcr_pos : ∀ M : ℕ, n ≤ M → 0 < ∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - M)| := by
    intro M hM; apply Finset.prod_pos; intro k hk; rw [Finset.mem_Icc] at hk; exact cross_pos M k (by omega)
  -- magnitude in division form
  have hdiv : ∀ M : ℕ, |ItermG q C n M|
      = (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - M)|)
        / (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + M)|) := by
    intro M; rw [ItermG_abs_factor n M hn, Finset.prod_inv_distrib, div_eq_mul_inv]
  rw [hdiv m, hdiv (m + 1), div_lt_div_iff₀ (hDinv_pos (m + 1)) (hDinv_pos m)]
  -- endpoint factors
  have hcc0 : 0 < |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| := cross_pos m 0 (by omega)
  have hccn : 0 < |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| := cross_pos m (n - 1) (by omega)
  have hdd0 : 0 < |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| := inv_pos' _ (by push_cast; omega)
  have hpos : 0 < |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| :=
    mul_pos hccn hdd0
  have hADpos : 0 < (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
      * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)| := mul_pos (hAcr_pos m hnm) (hDinv_pos m)
  refine lt_of_mul_lt_mul_right ?_ hpos.le
  have e1 : (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m + 1 : ℕ))|)
        * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
        * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
      = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
        * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
        * (|1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|) := by
    rw [show (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m + 1 : ℕ))|)
          * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
          * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
        = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m + 1 : ℕ))|)
            * |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))|)
          * ((∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
            * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|) from by ring,
      cross_telescopeG q n m]
    ring
  have e2 : (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
        * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m + 1 : ℕ))|)
        * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
      = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
        * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
        * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))|) := by
    rw [show (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
          * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m + 1 : ℕ))|)
          * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
        = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
            * |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))|)
          * ((∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m + 1 : ℕ))|)
            * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|) from by ring,
      inv_telescopeG q C n m]
    ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left (reduced_two_factor hq hC hn hnm) hADpos

/-! ### Sharp super-exponential error bound (Borwein Lemma 4) and the cleared error `→ 0`. -/

open Filter Topology

/-- Tight per-factor bound: `|(1 − q^{k−m})·(1 − C·q^{k+m})⁻¹| ≤ (q^{k+m})⁻¹` for `1 ≤ k < m`. -/
lemma factor_abs_leG (hq : 2 ≤ q) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ (q ^ (k + m))⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  rw [abs_mul]
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : q ^ ((k : ℤ) - m) ≤ 1 := by
      calc q ^ ((k : ℤ) - m) ≤ q ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) hexp
        _ = 1 := by norm_num
    have hpos : 0 < q ^ ((k : ℤ) - m) := zpow_pos (by linarith) _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ q ^ (-((k : ℤ) + m)) := inv_cqpowG_le hq hC (by omega)
  have h3 : q ^ (-((k : ℤ) + m)) = (q ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast q (k + m), Nat.cast_add]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * q ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (q ^ (k + m))⁻¹ := by rw [one_mul, h3]

/-- Sharp per-term bound in product form. -/
lemma ItermG_abs_le_sharp (hq : 2 ≤ q) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ (q ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (q ^ (k + m))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by linarith
  rw [ItermG, abs_mul, abs_neg]
  have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ (q ^ (m + n))⁻¹ := by
    have h := inv_cqpowG_le hq hC (a := (m : ℤ) + n) (by omega)
    have he : q ^ (-((m : ℤ) + n)) = (q ^ (m + n))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast q (m + n), Nat.cast_add]
    rwa [he] at h
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (q ^ (k + m))⁻¹ := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
    intro k hk; rw [Finset.mem_Icc] at hk
    exact factor_abs_leG hq hC hk.1 (by omega)
  exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos hqpos _)))

/-- Closed-form sharp per-term bound: `|Iₘ| ≤ Cₙ·(q^{-n})^m` with `Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. -/
lemma ItermG_abs_le_geom (hq : 2 ≤ q) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ m := by
  have hqpos : (0 : ℝ) < q := by linarith
  refine (ItermG_abs_le_sharp hq hC hn hnm).trans (le_of_eq ?_)
  have hL : (q ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (q ^ (k + m))⁻¹
      = (q ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
  have hR : (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ m
      = (q ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- The error bound `|Eₙ| ≤ Cₙ·(q^{-n})ⁿ·(1 − q^{-n})⁻¹`. -/
lemma EtermG_abs_le (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ n
        * (1 - (q ^ n)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hr1lt : q⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  set r : ℝ := (q ^ n)⁻¹ with hr_def
  set Cn : ℝ := (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos hqpos n))
  have hqn1 : (1 : ℝ) < q ^ n := by
    calc (1 : ℝ) < q := hq1
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := pow_le_pow_right₀ (le_of_lt hq1) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |ItermG q C n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ItermG_shift_le hq hC hn j)
      (summable_geometric_of_lt_one (by positivity) hr1lt)
  have h1 : |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => ItermG q C n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [EtermG, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |ItermG q C n (n + j)| ≤ Cn * r ^ (n + j) := fun j =>
    ItermG_abs_le_geom hq hC hn (Nat.le_add_right n j)
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |ItermG q C n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed form: `|Eₙ| ≤ 2·(q^{n + ∑_{k<n}k + n²})⁻¹`. -/
lemma EtermG_abs_le' (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ 2 * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  refine (EtermG_abs_le hq hC hn).trans ?_
  have hC' : (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ n
      = (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ q ^ n := by
    calc (2 : ℝ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := pow_le_pow_right₀ (le_of_lt hq1) hn
  have h1 : (q ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (q ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (q ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos hqpos _))
  calc (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ n * (1 - (q ^ n)⁻¹)⁻¹
      = (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * (1 - (q ^ n)⁻¹)⁻¹ := by rw [hC']
    _ ≤ (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by ring

/-- **Wₙ growth bound** (sign-independent). `|Wₙ(C,q)| ≤ (n−2)!·(2|C|)ⁿ·(q^{∑_{k≤n}k})²` for `q ≥ 2`,
`|C| > 2`. Each `|1 − C·q^k| ≤ 1 + |C|q^k ≤ 2|C|q^k`. -/
lemma WtermG_abs_le (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |WtermG q C n| ≤ (Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n
        * q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hCnn : (0 : ℝ) ≤ 2 * |C| := by positivity
  have hfac : (0:ℝ) ≤ (Nat.factorial (n-2) : ℝ) := by positivity
  have hqS : (0:ℝ) ≤ q ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt hqpos) _
  rw [WtermG, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)| ≤ (2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, (2 * |C|) * q ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          have hqkpos : (0:ℝ) < q ^ k := pow_pos hqpos k
          have hqk1 : (1:ℝ) ≤ q ^ k := one_le_pow₀ (le_of_lt hq1)
          have htri : |1 - C * q ^ k| ≤ 1 + |C| * q ^ k := by
            rw [show (1:ℝ) - C * q ^ k = 1 + -(C * q ^ k) from by ring]
            calc |(1:ℝ) + -(C * q ^ k)| ≤ |(1:ℝ)| + |-(C * q ^ k)| := abs_add_le _ _
              _ = 1 + |C| * q ^ k := by rw [abs_one, abs_neg, abs_mul, abs_of_pos hqkpos]
          have h2le : (2:ℝ) * 1 ≤ |C| * q ^ k :=
            mul_le_mul (le_of_lt hC) hqk1 (by norm_num) (by linarith)
          nlinarith [htri, h2le]
      _ = (2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)| ≤ q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - q ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, q ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          have hqk1 : (1:ℝ) ≤ q ^ k := one_le_pow₀ (le_of_lt hq1)
          rw [abs_of_nonpos (by linarith : (1 - q ^ k) ≤ 0)]
          linarith
      _ = q ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ q ^ (∑ k ∈ Finset.Icc 1 n, k) :=
          pow_le_pow_right₀ (le_of_lt hq1)
            (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (le_refl n)))
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * ((2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k))
          * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg hCnn n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k)
          * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by ring

/-- **The combine majorant** (sign-independent, abstract clearing factor `B`). The cleared error
`B^{2n}·Wₙ·Eₙ` is bounded by `2·(n−2)!·(B²·2|C|)ⁿ·(q^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_leG (hq : 2 ≤ q) (hC : 2 < |C|) {B : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    |B ^ (2 * n) * WtermG q C n * EtermG q C n|
      ≤ 2 * (Nat.factorial (n - 2) : ℝ) * (B ^ 2 * (2 * |C|)) ^ n
          * (q ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by linarith
  have hCnn : (0 : ℝ) ≤ 2 * |C| := by positivity
  have hB2 : (B : ℝ) ^ (2 * n) = (B ^ 2) ^ n := by rw [pow_mul]
  have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [← two_mul, gauss_Icc n]; ring
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by omega
  have hqcancel : q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (q ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hqpos _)), one_mul]
  have hWnn : (0:ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n
      * q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg hCnn n)) ?_) ?_ <;> exact pow_nonneg (le_of_lt hqpos) _
  have hBnn : (0:ℝ) ≤ (B : ℝ) ^ (2 * n) := by rw [hB2]; positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hBnn]
  calc (B : ℝ) ^ (2 * n) * |WtermG q C n| * |EtermG q C n|
      ≤ (B : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n
          * q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (EtermG_abs_le' hq hC hn) (abs_nonneg _)
          (mul_nonneg hBnn hWnn)
        exact mul_le_mul_of_nonneg_left (WtermG_abs_le hq hC hn) hBnn
    _ = 2 * (Nat.factorial (n - 2) : ℝ) * (B ^ 2 * (2 * |C|)) ^ n
          * (q ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hB2, mul_pow, ← hqcancel]; ring

/-- **Borwein Lemma 4 (error → 0), general `(q,C)`** (sign-independent). The cleared error
`B^{2n}·Wₙ·Eₙ → 0` for `q ≥ 2`, `|C| > 2`, any nonzero `B`. Squeeze `cleared_error_leG` against
`combine_asymptotic q (B²·2|C|)`. -/
theorem cleared_error_tendstoG (hq : 2 ≤ q) (hC : 2 < |C|) {B : ℝ} (hB : B ≠ 0) :
    Tendsto (fun n => B ^ (2 * n) * WtermG q C n * EtermG q C n) atTop (𝓝 0) := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hBC : (0 : ℝ) < B ^ 2 * (2 * |C|) := by
    have hB2 : (0:ℝ) < B ^ 2 := by positivity
    have hCp : (0:ℝ) < 2 * |C| := by positivity
    positivity
  have hg : Tendsto (fun n => 2 * ((Nat.factorial (n - 2) : ℝ) * (B ^ 2 * (2 * |C|)) ^ n
      * (q ^ (n * (n - 1) / 2))⁻¹)) atTop (𝓝 0) := by
    simpa using (combine_asymptotic q (B ^ 2 * (2 * |C|)) hq1 hBC).const_mul 2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_leG hq hC (B := B) hn
  rw [gauss_Icc' n] at h
  refine h.trans (le_of_eq ?_)
  ring

/-! ### Cleared error → 0 for negative base `q ≤ -2` (Lemma 4 endgame, `2 ≤ |q|`). -/

/-- **Wₙ growth bound, negative base** `|Wₙ(C,q)| ≤ (n−2)!·(4|C|)ⁿ·|q|^{2∑_{k≤n}k}`. Each
`|1 − C·q^k| ≤ 2|C||q|^k` and `|1 − q^k| ≤ 2|q|^k` (the cross-term `2`'s give the `4ⁿ` vs the
positive-base `2ⁿ`). -/
lemma WtermG_abs_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |WtermG q C n| ≤ (Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n
        * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hfac : (0 : ℝ) ≤ (Nat.factorial (n - 2) : ℝ) := by positivity
  have hqS : (0 : ℝ) ≤ |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt hqpos) _
  rw [WtermG, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)|
      ≤ (2 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, (2 * |C|) * |q| ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          have hqk1 : (1 : ℝ) ≤ |q| ^ k := one_le_pow₀ (le_of_lt hqabs1)
          have htri : |1 - C * q ^ k| ≤ 1 + |C| * |q| ^ k := by
            calc |1 - C * q ^ k| = |(1 : ℝ) + -(C * q ^ k)| := by rw [sub_eq_add_neg]
              _ ≤ |(1 : ℝ)| + |-(C * q ^ k)| := abs_add_le _ _
              _ = 1 + |C| * |q| ^ k := by rw [abs_one, abs_neg, abs_mul, abs_pow]
          have h2le : (2 : ℝ) * 1 ≤ |C| * |q| ^ k :=
            mul_le_mul (le_of_lt hC) hqk1 (by norm_num) (by linarith)
          nlinarith [htri, h2le]
      _ = (2 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)|
      ≤ 2 ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - q ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (2 * |q| ^ k) := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk
          have hqk1 : (1 : ℝ) ≤ |q| ^ k := one_le_pow₀ (le_of_lt hqabs1)
          calc |1 - q ^ k| = |(1 : ℝ) + -(q ^ k)| := by rw [sub_eq_add_neg]
            _ ≤ |(1 : ℝ)| + |-(q ^ k)| := abs_add_le _ _
            _ = 1 + |q| ^ k := by rw [abs_one, abs_neg, abs_pow]
            _ ≤ 2 * |q| ^ k := by linarith
      _ = 2 ^ ((Finset.Icc ((n + 1) / 2) n).card) * |q| ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
      _ ≤ 2 ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          have hsub : Finset.Icc ((n + 1) / 2) n ⊆ Finset.Icc 1 n :=
            Finset.Icc_subset_Icc (by omega) (le_refl n)
          have hcard : (Finset.Icc ((n + 1) / 2) n).card ≤ n := by
            calc (Finset.Icc ((n + 1) / 2) n).card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
              _ = n := by rw [Nat.card_Icc, Nat.add_sub_cancel]
          apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard)
            (pow_le_pow_right₀ (le_of_lt hqabs1) (Finset.sum_le_sum_of_subset hsub))
            (pow_nonneg (le_of_lt hqpos) _) (by positivity)
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * ((2 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k)) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg (by positivity) n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k)
          * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        have hconst : (4 * |C|) ^ n = (2 * |C|) ^ n * 2 ^ n := by rw [← mul_pow]; congr 1; ring
        rw [hconst]; ring

/-- **The combine majorant, negative base** (abstract clearing factor `B`): the cleared error
`B^{2n}·Wₙ·Eₙ` is bounded by `(n−2)!·(8·B²·|C|)ⁿ·(|q|^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_leG_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {B : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    |B ^ (2 * n) * WtermG q C n * EtermG q C n|
      ≤ (Nat.factorial (n - 2) : ℝ) * (8 * (B ^ 2 * |C|)) ^ n
          * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hB2 : (B : ℝ) ^ (2 * n) = (B ^ 2) ^ n := by rw [pow_mul]
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by
    have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
      rw [← two_mul, gauss_Icc n]; ring
    omega
  have hqcancel : |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hqpos _)), one_mul]
  have hWnn : (0 : ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n
      * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_) ?_ <;>
      exact pow_nonneg (le_of_lt hqpos) _
  have hBnn : (0 : ℝ) ≤ (B : ℝ) ^ (2 * n) := by rw [hB2]; positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hBnn]
  calc (B : ℝ) ^ (2 * n) * |WtermG q C n| * |EtermG q C n|
      ≤ (B : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n
          * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 ^ n * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (EtermG_abs_le'_abs hq hC hn) (abs_nonneg _) (mul_nonneg hBnn hWnn)
        exact mul_le_mul_of_nonneg_left (WtermG_abs_le_abs hq hC hn) hBnn
    _ = (Nat.factorial (n - 2) : ℝ) * (8 * (B ^ 2 * |C|)) ^ n
          * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hB2, show (8 : ℝ) * (B ^ 2 * |C|) = B ^ 2 * (4 * |C|) * 2 from by ring,
          mul_pow, mul_pow, ← hqcancel]; ring

/-- **Borwein Lemma 4 (error → 0), negative base** `q ≤ -2` (`2 ≤ |q|`, `2 < |C|`, any nonzero `B`).
The cleared error `B^{2n}·Wₙ·Eₙ → 0`, squeezing `cleared_error_leG_abs` against
`combine_asymptotic |q| (8·B²·|C|)`. -/
theorem cleared_error_tendstoG_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {B : ℝ} (hB : B ≠ 0) :
    Tendsto (fun n => B ^ (2 * n) * WtermG q C n * EtermG q C n) atTop (𝓝 0) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hBC : (0 : ℝ) < 8 * (B ^ 2 * |C|) := by
    have hB2 : (0 : ℝ) < B ^ 2 := by positivity
    have hCp : (0 : ℝ) < |C| := by linarith
    positivity
  have hg : Tendsto (fun n => (Nat.factorial (n - 2) : ℝ) * (8 * (B ^ 2 * |C|)) ^ n
      * (|q| ^ (n * (n - 1) / 2))⁻¹) atTop (𝓝 0) := by
    simpa using combine_asymptotic |q| (8 * (B ^ 2 * |C|)) hqabs1 hBC
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_leG_abs hq hC (B := B) hn
  rw [gauss_Icc' n] at h
  exact h

/-- **Lemma 5, negative base, `n` odd.** `(−1)^{nj}=(−1)^j`, so the terms `EsignG C n n · Iₙ(n+j)`
ALTERNATE in sign, with magnitudes `f j = |σ|·|Iₙ(n+j)|` strictly antitone (`ItermG_abs_anti_negbase`)
and `f 0 > f 1`. The alternating-series bracket gives `σ·Eₙ ≥ f 0 − f 1 > 0`, hence `Eₙ ≠ 0`. -/
theorem EtermG_ne_zero_odd_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n : ℕ}
    (hn : 1 ≤ n) (hno : Odd n) : EtermG q C n ≠ 0 := by
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg (show q < 0 by linarith)]; linarith
  set σ := EsignG C n n with hσ
  set f : ℕ → ℝ := fun j => (-1) ^ j * σ * ItermG q C n (n + j) with hf
  have hfpos : ∀ j, 0 < f j := by
    intro j
    have h := ItermG_sign_negbase hq hC hn (Nat.le_add_right n j)
    rw [EsignG_shift hn, ← hσ] at h
    have hpar : (-1 : ℝ) ^ (n * j) = (-1) ^ j := by
      rcases hno with ⟨t, ht⟩
      rw [ht, show (2 * t + 1) * j = 2 * (t * j) + j from by ring, pow_add, pow_mul, neg_one_sq,
        one_pow, one_mul]
    rw [hpar] at h
    exact h
  have hσne : σ ≠ 0 := fun h0 => by
    have h := hfpos 0
    rw [hf] at h
    simp only [pow_zero, one_mul, Nat.add_zero] at h
    rw [h0, zero_mul] at h
    exact lt_irrefl 0 h
  have hfeq : ∀ j, f j = |σ| * |ItermG q C n (n + j)| := by
    intro j
    rw [← abs_of_pos (hfpos j), hf]
    simp only
    rw [abs_mul, abs_mul, abs_pow, show |(-1 : ℝ)| = 1 from by norm_num, one_pow, one_mul]
  have hf_anti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro j
    rw [hfeq, hfeq]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)
    rw [show n + (j + 1) = (n + j) + 1 from by ring]
    exact le_of_lt (ItermG_abs_anti_negbase hq hC hn (by omega))
  have hf01 : f 1 < f 0 := by
    rw [hfeq, hfeq, show n + 0 = n from by ring]
    exact mul_lt_mul_of_pos_left (ItermG_abs_anti_negbase hq hC hn (le_refl n)) (abs_pos.mpr hσne)
  have hfsum : Summable f := by
    apply Summable.of_norm_bounded (g := fun j => |σ| * (|q|⁻¹) ^ j)
    · exact (summable_geometric_of_lt_one (by positivity)
        (show |q|⁻¹ < 1 by rw [inv_lt_one_iff₀]; right; linarith)).mul_left _
    · intro j
      rw [Real.norm_eq_abs, abs_of_pos (hfpos j), hfeq j]
      exact mul_le_mul_of_nonneg_left (ItermG_shift_le_abs hqabs hC hn j) (abs_nonneg σ)
  have htend := hfsum.tendsto_alternating_series_tsum
  have hbr := hf_anti.alternating_series_le_tendsto htend 1
  simp only [Nat.mul_one] at hbr
  have hsum2 : (∑ i ∈ Finset.range 2, (-1 : ℝ) ^ i * f i) = f 0 - f 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]; ring
  rw [hsum2] at hbr
  have hlval : (∑' i, (-1 : ℝ) ^ i * f i) = σ * EtermG q C n := by
    have hterm : ∀ i, (-1 : ℝ) ^ i * f i = σ * ItermG q C n (n + i) := by
      intro i
      rw [hf]
      simp only
      rw [show (-1 : ℝ) ^ i * ((-1) ^ i * σ * ItermG q C n (n + i))
            = ((-1) ^ i * (-1) ^ i) * (σ * ItermG q C n (n + i)) from by ring,
        show (-1 : ℝ) ^ i * (-1) ^ i = 1 from by rw [← pow_add]; exact Even.neg_one_pow ⟨i, rfl⟩,
        one_mul]
    rw [tsum_congr hterm, tsum_mul_left]; rfl
  rw [hlval] at hbr
  have hSE : 0 < σ * EtermG q C n := lt_of_lt_of_le (by linarith [hf01]) hbr
  intro h0
  rw [h0, mul_zero] at hSE
  exact lt_irrefl 0 hSE

/-- **Borwein Lemma 5 (non-vanishing), negative base `q ≤ -2`.** `EtermG q C n ≠ 0` for `n ≥ 1`,
`2 < |C|`. The sign DICHOTOMY: `n` even ⟹ same-sign terms (`EtermG_ne_zero_even_negbase`);
`n` odd ⟹ alternating series (`EtermG_ne_zero_odd_negbase`). -/
theorem EtermG_ne_zero_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n ≠ 0 := by
  rcases Nat.even_or_odd n with he | ho
  · exact EtermG_ne_zero_even_negbase hq hC hn he
  · exact EtermG_ne_zero_odd_negbase hq hC hn ho

end LeanGallery.NumberTheory.Erdos1050
