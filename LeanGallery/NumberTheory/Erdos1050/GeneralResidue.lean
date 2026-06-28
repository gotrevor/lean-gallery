/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.GeneralNumerator

/-!
# General residue identity, Piece II — the auxiliary-series collapse (parametric in `(q, C)`)

Toward discharging the general `borwein_approximants` (`General.lean`), this file ports Borwein's
"Piece II" — the collapse of the auxiliary series

    `T_i(q,C) = ∑_{j≥0} q^{−i(j+1)}·(1 − C·q^{j+1})⁻¹`

into `T_i = C^i·z + R_i`, where `z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹` is the q-harmonic value and
`R_i = ∑_{l=1}^i C^{i−l}/(q^l − 1)` is a rational correction — from the `q = 2, C = 8/3` case
(`Residue.lean`, `Tser_collapse`) to all real `q > 1` and `C ≠ 0`.

This is the analytic heart of the residue identity (Lemma 1): every inner tail series of `Eterm`
reindexes onto the `T_i` grid, and this collapse is what produces the `−pVal·z + (rational)` form.
All summability is genuine (geometric majorant, same estimate as `qharmonic_summable`); nothing is
cited. Restricted to `q > 1` (positive `q`) because the geometric sums use a nonneg ratio `q^{−1}`;
the `q < −1` case needs the alternating-geometric variant (TODO).

Additive; does not touch `erdos_1050_irrational` (axiom-clean).
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Filter Topology

/-- The general q-harmonic value `z = ∑_{j≥0} (1 − C·q^{j+1})⁻¹` (the value in `borwein_approximants`). -/
noncomputable def zG (q C : ℝ) : ℝ := ∑' j : ℕ, (1 - C * q ^ (j + 1))⁻¹

/-- The rational correction `R_i = ∑_{l=1}^i C^{i−l}/(q^l − 1)`, via `R_{i+1} = 1/(q^{i+1}−1) + C·R_i`. -/
noncomputable def RratG (q C : ℝ) : ℕ → ℝ
  | 0 => 0
  | (i + 1) => 1 / (q ^ (i + 1) - 1) + C * RratG q C i

/-- The auxiliary series `T_i = ∑_{j≥0} q^{−i(j+1)}·(1 − C·q^{j+1})⁻¹`. -/
noncomputable def TserG (q C : ℝ) (i : ℕ) : ℝ :=
  ∑' j : ℕ, (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹

variable {q C : ℝ}

/-- For `q > 1`, `q^k − 1 ≠ 0` (any `k ≥ 1`). -/
private lemma qpowk_sub_one_ne (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) : q ^ k - 1 ≠ 0 := by
  have : (1 : ℝ) < q ^ k := by
    calc (1 : ℝ) < q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := pow_le_pow_right₀ (le_of_lt hq) hk
  linarith

/-- Per-term collapse identity. With `P = q^{j+1}`: `(P^{i+1})⁻¹(1−CP)⁻¹ = (P^{i+1})⁻¹ + C(P^i)⁻¹(1−CP)⁻¹`. -/
private lemma key_termG (P : ℝ) (i : ℕ) (hP : P ≠ 0) (hcP : 1 - C * P ≠ 0) :
    (P ^ (i + 1))⁻¹ * (1 - C * P)⁻¹
      = (P ^ (i + 1))⁻¹ + C * (P ^ i)⁻¹ * (1 - C * P)⁻¹ := by
  have hPi : P ^ i ≠ 0 := pow_ne_zero i hP
  have hPi1 : P ^ (i + 1) ≠ 0 := pow_ne_zero (i + 1) hP
  field_simp
  ring

/-- The non-degeneracy hypothesis `C·q^{j+1} ≠ 1` makes `1 − C·q^{j+1} ≠ 0`. -/
private lemma one_sub_ne (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) (j : ℕ) : 1 - C * q ^ (j + 1) ≠ 0 := by
  intro h; exact hCn j (by linarith)

/-- **Summability of `T_i`** (geometric majorant `|q|⁻¹`; works for both signs of `q`, `1 < |q|`). -/
lemma TserG_summable (hq : 1 < |q|) (hC : C ≠ 0) (i : ℕ) :
    Summable (fun j : ℕ => (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹) := by
  have hqabs : 0 < |q| := by linarith
  have hCpos : 0 < |C| := abs_pos.mpr hC
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeo : Summable (fun j : ℕ => (2 / |C|) * (|q|⁻¹) ^ (j + 1)) :=
    (((summable_geometric_of_lt_one (by positivity) hinvlt).comp_injective
      (add_left_injective 1)).mul_left (2 / |C|))
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun j => (2 / |C|) * (|q|⁻¹) ^ (j + 1)) hgeo ?_
  have htend : Filter.Tendsto (fun j : ℕ => |C| * |q| ^ (j + 1)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hCpos
      ((tendsto_pow_atTop_atTop_of_one_lt hq).comp (Filter.tendsto_add_atTop_nat 1))
  filter_upwards [htend.eventually_ge_atTop 2] with j hj
  rw [Real.norm_eq_abs, abs_mul]
  have hqpw : 0 < |q| ^ (j + 1) := pow_pos hqabs _
  -- |(q^{i(j+1)})⁻¹| ≤ 1
  have hA : |(q ^ (i * (j + 1)))⁻¹| ≤ 1 := by
    rw [abs_inv, abs_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hq))
  -- |(1 - C q^{j+1})⁻¹| ≤ (2/|C|)·(|q|⁻¹)^{j+1}
  have hlow : |C| * |q| ^ (j + 1) / 2 ≤ |1 - C * q ^ (j + 1)| := by
    have htri := abs_sub_abs_le_abs_sub (C * q ^ (j + 1)) 1
    rw [abs_one, abs_mul, abs_pow, abs_sub_comm] at htri
    linarith [htri, hj]
  have h2pos : 0 < |C| * |q| ^ (j + 1) / 2 := by positivity
  have hB : |(1 - C * q ^ (j + 1))⁻¹| ≤ (2 / |C|) * (|q|⁻¹) ^ (j + 1) := by
    rw [abs_inv]
    calc |1 - C * q ^ (j + 1)|⁻¹ ≤ (|C| * |q| ^ (j + 1) / 2)⁻¹ := inv_anti₀ h2pos hlow
      _ = (2 / |C|) * (|q|⁻¹) ^ (j + 1) := by rw [inv_pow]; field_simp
  calc |(q ^ (i * (j + 1)))⁻¹| * |(1 - C * q ^ (j + 1))⁻¹|
      ≤ 1 * ((2 / |C|) * (|q|⁻¹) ^ (j + 1)) :=
        mul_le_mul hA hB (abs_nonneg _) (by norm_num)
    _ = (2 / |C|) * (|q|⁻¹) ^ (j + 1) := by rw [one_mul]

/-- `T_0 = z`. -/
lemma TserG_zero : TserG q C 0 = zG q C := by
  unfold TserG zG
  apply tsum_congr
  intro j
  simp

/-- The geometric piece `∑_j q^{−(i+1)(j+1)} = 1/(q^{i+1} − 1)` (norm-geometric; `1 < |q|`, any sign). -/
lemma geom_pieceG (hq : 1 < |q|) (i : ℕ) :
    ∑' j : ℕ, (q ^ ((i + 1) * (j + 1)))⁻¹ = 1 / (q ^ (i + 1) - 1) := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  set r : ℝ := (q ^ (i + 1))⁻¹ with hr
  have hqgt : (1 : ℝ) < |q| ^ (i + 1) := by
    calc (1 : ℝ) < |q| := hq
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ (i + 1) := pow_le_pow_right₀ (le_of_lt hq) (by omega)
  have hrnorm : ‖r‖ < 1 := by
    rw [hr, Real.norm_eq_abs, abs_inv, abs_pow]
    exact inv_lt_one_of_one_lt₀ hqgt
  have hconv : ∀ j : ℕ, (q ^ ((i + 1) * (j + 1)))⁻¹ = r * r ^ j := by
    intro j; rw [hr, ← pow_succ', inv_pow, ← pow_mul]
  rw [tsum_congr hconv, tsum_mul_left, tsum_geometric_of_norm_lt_one hrnorm, hr]
  have hx0 : (q : ℝ) ^ (i + 1) ≠ 0 := pow_ne_zero _ hqne
  have hx2 : (q : ℝ) ^ (i + 1) - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h
    have habs : |q ^ (i + 1)| = 1 := by rw [h]; norm_num
    rw [abs_pow] at habs; linarith
  field_simp

/-- The geometric piece is summable (`|q|⁻¹` majorant). -/
lemma geom_summableG (hq : 1 < |q|) (i : ℕ) :
    Summable (fun j : ℕ => (q ^ ((i + 1) * (j + 1)))⁻¹) := by
  have hqabs : 0 < |q| := by linarith
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeo : Summable (fun j : ℕ => (|q|⁻¹) ^ (j + 1)) :=
    (summable_geometric_of_lt_one (by positivity) hinvlt).comp_injective (add_left_injective 1)
  apply Summable.of_norm_bounded hgeo
  intro j
  rw [Real.norm_eq_abs, abs_inv, abs_pow, inv_pow]
  exact inv_anti₀ (pow_pos hqabs _) (pow_le_pow_right₀ (le_of_lt hq) (by rw [Nat.succ_mul]; omega))

/-- **The collapse recurrence** `T_{i+1} = 1/(q^{i+1} − 1) + C·T_i` (`1 < |q|`, any sign). -/
lemma TserG_succ (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) (i : ℕ) :
    TserG q C (i + 1) = 1 / (q ^ (i + 1) - 1) + C * TserG q C i := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  unfold TserG
  have hterm : ∀ j : ℕ,
      (q ^ ((i + 1) * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹
        = (q ^ ((i + 1) * (j + 1)))⁻¹
          + C * (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹ := by
    intro j
    have hk := key_termG (C := C) (q ^ (j + 1)) i (pow_ne_zero _ hqne) (one_sub_ne hCn j)
    have e1 : q ^ ((i + 1) * (j + 1)) = (q ^ (j + 1)) ^ (i + 1) := by rw [← pow_mul, Nat.mul_comm]
    have e2 : q ^ (i * (j + 1)) = (q ^ (j + 1)) ^ i := by rw [← pow_mul, Nat.mul_comm]
    rw [e1, e2]; exact hk
  rw [tsum_congr hterm]
  have hsum_rest : Summable
      (fun j : ℕ => C * (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹) := by
    simp_rw [mul_assoc]
    exact (TserG_summable hq hC i).mul_left C
  rw [Summable.tsum_add (geom_summableG hq i) hsum_rest, geom_pieceG hq i]
  congr 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- **Piece II — the collapse** `T_i = C^i·z + R_i` (induction from the recurrence; `1 < |q|`). -/
theorem TserG_collapse (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) (i : ℕ) :
    TserG q C i = C ^ i * zG q C + RratG q C i := by
  induction i with
  | zero => rw [TserG_zero, show RratG q C 0 = 0 from rfl]; ring
  | succ i ih =>
      rw [TserG_succ hq hC hCn, ih, show RratG q C (i + 1) = 1 / (q ^ (i + 1) - 1) + C * RratG q C i from rfl]
      ring

/-! ### Assembly bricks for the residue identity (Lemma 1, first form), parametric in `(q, C)`. -/

/-- The `m`-th term of the explicit (contour-free) error series, general `(q, C)`. -/
noncomputable def ItermG (q C : ℝ) (n m : ℕ) : ℝ :=
  -(1 - C * q ^ ((m : ℤ) + n))⁻¹ *
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹

/-- The error term `Eₙ = ∑_{m≥n} Iₘ`, reindexed `∑_{j≥0} I_{n}(n+j)`, general `(q, C)`. -/
noncomputable def EtermG (q C : ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, ItermG q C n (n + j)

/-- `Iₘ = −(∏_{k=1}^{n-1}(1−q^{k−m}))·∏_{k=1}^{n}(1−C·q^{k+m})⁻¹` (for `n ≥ 1`). -/
lemma ItermG_prod_form (n m : ℕ) (hn : 1 ≤ n) :
    ItermG q C n m
      = -((∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) - m)))
          * ∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ ((k : ℤ) + m))⁻¹) := by
  rw [ItermG, Finset.prod_mul_distrib,
    show ((m : ℤ) + n) = ((n : ℤ) + m) from by ring,
    show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) from by rw [Nat.sub_add_cancel hn],
    Finset.prod_Icc_succ_top (by omega : 1 ≤ (n - 1) + 1), Nat.sub_add_cancel hn]
  ring

/-- **`q`-numerator expansion** `∏_{k=1}^{n-1}(1−q^{k−m}) = ∑_t (∏_{k∈t}−q^k)·(q^{−m})^{|t|}`. -/
lemma DtermG_expand (hq : 1 < |q|) (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) - m)))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-q ^ k)) * ((q ^ m)⁻¹) ^ t.card := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have hfac : ∀ k : ℕ, (1 : ℝ) - q ^ ((k : ℤ) - m) = 1 + (-(q ^ k)) * (q ^ m)⁻¹ := by
    intro k
    rw [zpow_sub₀ hqne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The inner tail series `∑_{m≥0} q^{−i(n+m)}·u_{(n+m)+j}` of the assembly. -/
noncomputable def StailG (q C : ℝ) (i j n : ℕ) : ℝ :=
  ∑' m : ℕ, (q ^ (i * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹

/-- The finite rational "head" removed when reindexing `StailG` onto the `TserG` grid. -/
noncomputable def headSG (q C : ℝ) (i j n : ℕ) : ℝ :=
  ∑ m' ∈ Finset.range (n + j - 1), (q ^ (i * (m' + 1)))⁻¹ * (1 - C * q ^ (m' + 1))⁻¹

/-- **Tail collapse**: `StailG = q^{ij}·(TserG i − headSG)`, a finite reindex onto the `TserG` grid. -/
lemma StailG_collapse (hq : 1 < |q|) (hC : C ≠ 0) (i j n : ℕ) (hnj : 1 ≤ n + j) :
    StailG q C i j n = q ^ (i * j) * (TserG q C i - headSG q C i j n) := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have hterm : ∀ m : ℕ,
      (q ^ (i * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹
        = q ^ (i * j) * ((q ^ (i * ((m + (n + j - 1)) + 1)))⁻¹
            * (1 - C * q ^ ((m + (n + j - 1)) + 1))⁻¹) := by
    intro m
    have h1 : (m + (n + j - 1)) + 1 = (n + m) + j := by omega
    have hw : (q ^ (i * (n + m)))⁻¹ = q ^ (i * j) * (q ^ (i * ((n + m) + j)))⁻¹ := by
      rw [show i * ((n + m) + j) = i * j + i * (n + m) from by ring, pow_add, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hqne), one_mul]
    rw [h1, hw]; ring
  rw [StailG, tsum_congr hterm, tsum_mul_left]
  congr 1
  have hsum := Summable.sum_add_tsum_nat_add (n + j - 1) (TserG_summable hq hC i)
  rw [show TserG q C i = ∑' m : ℕ, (q ^ (i * (m + 1)))⁻¹ * (1 - C * q ^ (m + 1))⁻¹ from rfl, headSG]
  linarith [hsum]

/-- **z-coefficient bridge**: `pFirstG` re-expanded over the same subsets `t ⊆ [1,n−1]` that the
`q`-numerator `DtermG_expand` produces. -/
lemma pFirstG_powerset (n : ℕ) :
    pFirstG q C n = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-C * q ^ k)) * ∑ j ∈ Finset.Icc 1 n, muWG q n j * (q ^ j) ^ t.card := by
  rw [pFirstG]
  have hexp : ∀ j, ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-C * q ^ k)) * (q ^ j) ^ t.card := by
    intro j
    have hf : ∀ k, (1 : ℝ) - C * q ^ (k + j) = 1 + (-C * q ^ k) * q ^ j := by
      intro k; rw [pow_add]; ring
    rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hexp j])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `StailG`'s summand is summable (geometric majorant `|q|⁻¹`; `1 < |q|`, any sign). -/
lemma StailG_summable (hq : 1 < |q|) (hC : C ≠ 0) (n i j : ℕ) :
    Summable (fun m : ℕ => (q ^ (i * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹) := by
  have hqabs : 0 < |q| := by linarith
  have hCpos : 0 < |C| := abs_pos.mpr hC
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeo : Summable (fun m : ℕ => ((2 / |C|) * (|q|⁻¹) ^ (n + j)) * (|q|⁻¹) ^ m) :=
    (summable_geometric_of_lt_one (by positivity) hinvlt).mul_left _
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun m => ((2 / |C|) * (|q|⁻¹) ^ (n + j)) * (|q|⁻¹) ^ m) hgeo ?_
  have hexp : ∀ m : ℕ, (n + m) + j = m + (n + j) := fun m => by omega
  have htend : Filter.Tendsto (fun m : ℕ => |C| * |q| ^ ((n + m) + j)) Filter.atTop Filter.atTop := by
    have h : Filter.Tendsto (fun m : ℕ => |C| * |q| ^ (m + (n + j))) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hCpos
        ((tendsto_pow_atTop_atTop_of_one_lt hq).comp (Filter.tendsto_add_atTop_nat (n + j)))
    simpa only [hexp] using h
  filter_upwards [htend.eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, abs_mul]
  have hqpw : 0 < |q| ^ ((n + m) + j) := pow_pos hqabs _
  have hA : |(q ^ (i * (n + m)))⁻¹| ≤ 1 := by
    rw [abs_inv, abs_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hq))
  have hlow : |C| * |q| ^ ((n + m) + j) / 2 ≤ |1 - C * q ^ ((n + m) + j)| := by
    have htri := abs_sub_abs_le_abs_sub (C * q ^ ((n + m) + j)) 1
    rw [abs_one, abs_mul, abs_pow, abs_sub_comm] at htri
    linarith [htri, hm]
  have h2pos : 0 < |C| * |q| ^ ((n + m) + j) / 2 := by positivity
  have hB : |(1 - C * q ^ ((n + m) + j))⁻¹| ≤ (2 / |C|) * (|q|⁻¹) ^ ((n + m) + j) := by
    rw [abs_inv]
    calc |1 - C * q ^ ((n + m) + j)|⁻¹ ≤ (|C| * |q| ^ ((n + m) + j) / 2)⁻¹ := inv_anti₀ h2pos hlow
      _ = (2 / |C|) * (|q|⁻¹) ^ ((n + m) + j) := by rw [inv_pow]; field_simp
  have hsplit : (|q|⁻¹) ^ ((n + m) + j) = (|q|⁻¹) ^ (n + j) * (|q|⁻¹) ^ m := by
    rw [← pow_add]; congr 1; omega
  calc |(q ^ (i * (n + m)))⁻¹| * |(1 - C * q ^ ((n + m) + j))⁻¹|
      ≤ 1 * ((2 / |C|) * (|q|⁻¹) ^ ((n + m) + j)) := mul_le_mul hA hB (abs_nonneg _) (by norm_num)
    _ = ((2 / |C|) * (|q|⁻¹) ^ (n + j)) * (|q|⁻¹) ^ m := by rw [one_mul, hsplit]; ring

/-- Each `Iₘ` (here `M` general) as a finite double sum over subsets `t ⊆ [1,n−1]` and poles
`j ∈ [1,n]`, via `ItermG_prod_form` + `partial_fraction` (Piece I, general) + `DtermG_expand`. -/
lemma ItermG_triple (hq : 1 < |q|) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    ItermG q C n M
      = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ t, (-q ^ k)) * muWG q n j
            * (((q ^ M)⁻¹) ^ t.card * (1 - C * q ^ (M + j))⁻¹) := by
  have hpm : ∀ a : ℕ, C * q ^ M * q ^ a = C * q ^ (M + a) := by
    intro a; rw [pow_add]; ring
  have hCprod : ∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ ((k : ℤ) + M))⁻¹
      = ∑ j ∈ Finset.Icc 1 n, muWG q n j * (1 - C * q ^ (M + j))⁻¹ := by
    have hconv : ∀ k : ℕ, (1 : ℝ) - C * q ^ ((k : ℤ) + M) = 1 - C * q ^ M * q ^ k := by
      intro k
      have he : ((k : ℤ) + M) = ((k + M : ℕ) : ℤ) := by push_cast; ring
      rw [he, zpow_natCast, pow_add]; ring
    have hx : ∀ k, 1 ≤ k → k ≤ n → 1 - C * q ^ M * q ^ k ≠ 0 := by
      intro k hk1 _
      rw [hpm k]
      obtain ⟨h', hh'⟩ : ∃ h', M + k = h' + 1 := ⟨M + k - 1, by omega⟩
      rw [hh']; exact one_sub_ne hCn h'
    have hprodeq : ∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ ((k : ℤ) + M))⁻¹
        = (∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ M * q ^ k))⁻¹ := by
      simp only [hconv, Finset.prod_inv_distrib]
    rw [hprodeq, partial_fraction_abs q hq n hn (C * q ^ M) hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpm j]
    rfl
  rw [ItermG_prod_form n M hn, hCprod, DtermG_expand hq n M]
  rw [Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- **The pull-out**: `EtermG n` as a finite double sum of `StailG`'s. -/
lemma EtermG_eq_StailG (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-q ^ k)) * muWG q n j * StailG q C t.card j n := by
  have hStail : ∀ (t : Finset ℕ) (j : ℕ),
      (fun m : ℕ => (∏ k ∈ t, (-q ^ k)) * muWG q n j
          * (((q ^ (n + m))⁻¹) ^ t.card * (1 - C * q ^ ((n + m) + j))⁻¹))
        = (fun m : ℕ => (∏ k ∈ t, (-q ^ k)) * muWG q n j
          * ((q ^ (t.card * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹)) := by
    intro t j; funext m
    rw [inv_pow, ← pow_mul, mul_comm (n + m) t.card]
  have hsum : ∀ (t : Finset ℕ) (j : ℕ), Summable (fun m : ℕ =>
      (∏ k ∈ t, (-q ^ k)) * muWG q n j
        * (((q ^ (n + m))⁻¹) ^ t.card * (1 - C * q ^ ((n + m) + j))⁻¹)) := by
    intro t j
    rw [hStail t j]
    exact ((StailG_summable hq hC n t.card j).mul_left _)
  rw [EtermG, tsum_congr (fun m => ItermG_triple hq hCn hn (n + m)), tsum_neg]
  congr 1
  rw [Summable.tsum_finsetSum (fun t _ => summable_sum (fun j _ => hsum t j))]
  apply Finset.sum_congr rfl; intro t _
  rw [Summable.tsum_finsetSum (fun j _ => hsum t j)]
  apply Finset.sum_congr rfl; intro j _
  rw [hStail t j, tsum_mul_left]
  congr 1

/-- The explicit **rational correction** `Aₙ` of the residue identity `Eₙ = −pFirst·z + Aₙ`. -/
noncomputable def AcorrG (q C : ℝ) (n : ℕ) : ℝ :=
  -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
    (∏ k ∈ t, (-q ^ k)) * muWG q n j
      * (q ^ (t.card * j) * (RratG q C t.card - headSG q C t.card j n))

/-- **The residue identity** (contour-free, first form): `Eₙ = −pFirstG n · z + AcorrG n`. The general
`(q, C)` analog of `Eterm_eq_pFirst` (Borwein Lemma 1). -/
theorem EtermG_eq_pFirstG (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n = -pFirstG q C n * zG q C + AcorrG q C n := by
  have key : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∀ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-q ^ k)) * muWG q n j * StailG q C t.card j n
        = ((∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * C ^ t.card)) * zG q C
          + (∏ k ∈ t, (-q ^ k)) * muWG q n j
              * (q ^ (t.card * j) * (RratG q C t.card - headSG q C t.card j n)) := by
    intro t _ j _
    rw [StailG_collapse hq hC t.card j n (by omega), TserG_collapse hq hC hCn]
    ring
  have hzcoef : ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * C ^ t.card) = pFirstG q C n := by
    rw [pFirstG_powerset n]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hpt : ∏ k ∈ t, (-C * q ^ k) = C ^ t.card * ∏ k ∈ t, (-q ^ k) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun k _ => by ring)
    have hqp : ((q ^ j) ^ t.card : ℝ) = q ^ (t.card * j) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpt, hqp]; ring
  rw [EtermG_eq_StailG hq hC hCn hn,
    Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun j hj => key t ht j hj))]
  simp_rw [Finset.sum_add_distrib]
  rw [neg_add, AcorrG]
  congr 1
  rw [← hzcoef, neg_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_mul]

/-- **The residue identity with the `pValG` denominator**: `Eₙ = −pValG n · z + AcorrG n`, for real
`q > 1` and non-degenerate `C ≠ 0`. The general `(q, C)` analog of `Eterm_eq_pVal` (Borwein Lemma 1
with the Gaussian-binomial denominator). This is the full parametric residue identity. -/
theorem EtermG_eq_pValG (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n = -pValG q C n * zG q C + AcorrG q C n := by
  rw [EtermG_eq_pFirstG hq hC hCn hn, pFirstG_eq_pValG hq C hn]

/-! ### Denominator-exposing closed forms (toward the general Lemma-3 numerator integrality).

`AcorrG`'s denominators come from `muWG`, `RratG`, `headSG`. Exposing them as the products
`∏_{l≠j}(q^j − q^l)`, `q^l − 1`, and `β − α·q^{m'+1}` is the entry point to showing `β^{2n}·Wₙ·AcorrG`
is an integer (Borwein Lemma 3). These generalize `muW_closed`/`Rrat_closed`/`headS_clear`. -/

/-- `q^j − q^l ≠ 0` for `j ≠ l` (q-powers distinct since `q > 1`). -/
lemma qpowG_sub_ne (hq : 1 < q) {j l : ℕ} (hlj : l ≠ j) : (q ^ j - q ^ l : ℝ) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  apply hlj
  rcases Nat.lt_trichotomy l j with hlt | heq | hgt
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_right₀ hq hlt))
  · exact heq
  · exact absurd h (ne_of_lt (pow_lt_pow_right₀ hq hgt))

/-- **Denominator-exposing closed form** of the q-Lagrange weight:
`μ_j = (q^j)^{|erase j|}·(∏_{l≠j}(q^j − q^l))⁻¹`. -/
lemma muWG_closed (hq : 1 < q) (n j : ℕ) :
    muWG q n j = (q ^ j) ^ ((Finset.Icc 1 n).erase j).card
      * (∏ l ∈ (Finset.Icc 1 n).erase j, (q ^ j - q ^ l))⁻¹ := by
  have hqpos : 0 < q := by linarith
  rw [muWG]
  have hfac : ∀ l ∈ (Finset.Icc 1 n).erase j,
      (1 - q ^ l / q ^ j)⁻¹ = q ^ j * (q ^ j - q ^ l)⁻¹ := by
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hjne : (q ^ j : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hqpos)
    have hsub : (q ^ j - q ^ l : ℝ) ≠ 0 := qpowG_sub_ne hq hlj
    rw [show (1 - q ^ l / q ^ j : ℝ) = (q ^ j - q ^ l) / q ^ j from by field_simp,
      inv_div, div_eq_mul_inv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    ← Finset.prod_inv_distrib]

/-- **Closed form of the rational correction** `RratG i = ∑_{l=1}^i C^{i-l}/(q^l − 1)`, exposing the
denominators `(q^l − 1)` and the `C`-powers. -/
lemma RratG_closed (_hq : 1 < |q|) (i : ℕ) :
    RratG q C i = ∑ l ∈ Finset.Icc 1 i, C ^ (i - l) / (q ^ l - 1) := by
  induction i with
  | zero => simp [RratG]
  | succ i ih =>
    rw [show RratG q C (i + 1) = 1 / (q ^ (i + 1) - 1) + C * RratG q C i from rfl, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1), Nat.sub_self, pow_zero, Finset.mul_sum,
      add_comm (1 / (q ^ (i + 1) - 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Icc] at hl
    rw [show (i + 1) - l = (i - l) + 1 from by omega, pow_succ]
    ring

/-- **`headSG` with denominators exposed**: with `C = α/β`, each factor `(1 − C·q^{m'+1})⁻¹` clears to
`β·(β − α·q^{m'+1})⁻¹`, surfacing the integer denominators `β − α·q^{m'+1}` that `Wₙ`'s `∏(1−C·q^k)`
clears. -/
lemma headSG_clear (α β : ℝ) (hβ : β ≠ 0) (i j n : ℕ) :
    headSG q (α / β) i j n = ∑ m' ∈ Finset.range (n + j - 1),
      β * (q ^ (i * (m' + 1)))⁻¹ * (β - α * q ^ (m' + 1))⁻¹ := by
  rw [headSG]
  apply Finset.sum_congr rfl
  intro m' _
  have h : (1 - (α / β) * q ^ (m' + 1))⁻¹ = β * (β - α * q ^ (m' + 1))⁻¹ := by
    rw [show (1 - (α / β) * q ^ (m' + 1) : ℝ) = (β - α * q ^ (m' + 1)) / β from by
      field_simp, inv_div, div_eq_mul_inv]
  rw [h]; ring

/-- `1 − q^k ≠ 0` for `k ≥ 1` and `q > 1` (then `q^k > 1`). -/
lemma one_sub_qpowG_ne (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) : (1 - q ^ k : ℝ) ≠ 0 := by
  have hgt : (1 : ℝ) < q ^ k := by
    calc (1 : ℝ) < q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := pow_le_pow_right₀ (le_of_lt hq) hk
  linarith

/-- `1 − q^k ≠ 0` for `1 < |q|`, `k ≥ 1`: `|q^k| = |q|^k > 1`, so `q^k ≠ 1` (both signs of `q`). -/
lemma one_sub_qpowG_ne_abs (hq : 1 < |q|) {k : ℕ} (hk : 1 ≤ k) : (1 - q ^ k : ℝ) ≠ 0 := by
  intro h
  have hqk : q ^ k = 1 := by linarith
  have hgt : (1 : ℝ) < |q| ^ k := by
    calc (1 : ℝ) < |q| := hq
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ k := pow_le_pow_right₀ (le_of_lt hq) hk
  rw [← abs_pow, hqk, abs_one] at hgt
  exact lt_irrefl 1 hgt

/-- **`Wₙ ≠ 0`** for `q > 1`, non-degenerate `C`, `n ≥ 1`: a nonzero factorial times two products of
nonzero factors. (The `b_n ≠ 0` ingredient for the final approximant assembly.) -/
lemma WtermG_ne_zero (hq : 1 < q) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    WtermG q C n ≠ 0 := by
  rw [WtermG]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    obtain ⟨h', hh'⟩ : ∃ h', k = h' + 1 := ⟨k - 1, by omega⟩
    rw [hh']
    exact one_sub_ne hCn h'
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_qpowG_ne hq (by omega)

/-- **`Wₙ ≠ 0`, both signs of base** (`1 < |q|`). The negative-base analog of `WtermG_ne_zero`. -/
lemma WtermG_ne_zero_abs (hq : 1 < |q|) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    WtermG q C n ≠ 0 := by
  rw [WtermG]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    obtain ⟨h', hh'⟩ : ∃ h', k = h' + 1 := ⟨k - 1, by omega⟩
    rw [hh']
    exact one_sub_ne hCn h'
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_qpowG_ne_abs hq (by omega)

/-- **`RratG` denominators clear to an integer**: for integer `q ≥ 2` and `C = α/β`,
`β^i·(∏_{l=1}^i (q^l−1))·R_i(α/β,q) ∈ ℤ`. The `C`-powers clear under `β^i`; the `(q^l−1)`
denominators clear because each summand keeps the complementary product `∏_{l'≠l}(q^{l'}−1)`. A
clearing brick toward the general Lemma-3 numerator integrality (`AcorrG`'s `RratG`-part). -/
lemma RratG_int (q α β : ℤ) (hq : 2 ≤ q) (hβ : β ≠ 0) (i : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (β : ℝ) ^ i * (∏ l ∈ Finset.Icc 1 i, ((q : ℝ) ^ l - 1))
        * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) i := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by rw [abs_of_pos (by linarith : (0 : ℝ) < (q : ℝ))]; exact hq1
  have hβr : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  refine ⟨∑ l ∈ Finset.Icc 1 i,
      β ^ l * α ^ (i - l) * ∏ l' ∈ (Finset.Icc 1 i).erase l, (q ^ l' - 1), ?_⟩
  rw [RratG_closed hq1abs, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  have hql : (q : ℝ) ^ l - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < (q : ℝ) ^ l := by
      calc (1 : ℝ) < (q : ℝ) := hq1
        _ = (q : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℝ) ^ l := pow_le_pow_right₀ (le_of_lt hq1) hl.1
    linarith
  have hβsplit : (β : ℝ) ^ i = (β : ℝ) ^ l * (β : ℝ) ^ (i - l) := by
    rw [← pow_add]; congr 1; omega
  push_cast
  rw [← Finset.mul_prod_erase (Finset.Icc 1 i) (fun l' => ((q : ℝ) ^ l' - 1))
      (Finset.mem_Icc.mpr hl), div_pow, hβsplit]
  field_simp

end LeanGallery.NumberTheory.Erdos1050
