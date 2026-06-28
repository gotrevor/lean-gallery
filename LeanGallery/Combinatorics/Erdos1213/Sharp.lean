/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Main

/-!
# Sharp constant for Hegyvári Theorem 3 (Erdős #1213)

The headline `hegyvari_thm3` proves `f(a,K) < (a₁+K/2)e^{K+1} + K·e^{2K+2}` (leading constant
`e²·K·e^{2K} ≈ 7.389·K·e^{2K}`).  This file sharpens the **constant** to `C = ½·e^{1−2γ} ≈ 0.428451`,
a `2·e^{1+2γ} ≈ 17.25×` improvement at the same exponent `2K`, where `γ` is the Euler–Mascheroni
constant.  The win comes from two changes to the elementary count:

* cut the length sum off at the count-positivity wall `j ≤ √(2D/K)` (Hegyvári summed to `j ≈ e^{K+1}`,
  paying a parasitic `e^{2K+2}/4` for the dead tail);
* keep the `+γ` in the harmonic sum `H_J ≥ log J + γ` — mathlib's
  `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'` — instead of `H_J ≥ log J` only.

Paper writeup: `notes/CONSTANT-LEMMA.md`.  This is a separate, *sharper* upper bound on the same `f`;
it does not replace the headline (which is already complete and axiom-clean).
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

/-- **The Euler–Mascheroni harmonic lower bound.**  `log n + γ < H_n` for `n ≥ 1`, the load-bearing
input for the sharp constant.  Direct from mathlib's `eulerMascheroniSeq' n = H_n − log n` (for
`n ≥ 1`) and `γ < eulerMascheroniSeq' n`. -/
theorem log_add_gamma_lt_harmonic (n : ℕ) (hn : 1 ≤ n) :
    Real.log n + Real.eulerMascheroniConstant < (harmonic n : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq', if_neg (by omega : n ≠ 0)] at h
  linarith

/-! ## Threshold definitions -/

/-- Sharp small error term `η_K = 4·(a₁/K + 1)·e^{γ−1/2−K}` (exponentially small in `K`). -/
noncomputable def sharpEta (a1 K : ℝ) : ℝ :=
  4 * (a1 / K + 1) * Real.exp (Real.eulerMascheroniConstant - 1 / 2 - K)

/-- Sharp threshold `(K/2)·exp(2K + 1 − 2γ + η_K)`.  Leading term `½·e^{1−2γ}·K·e^{2K}`. -/
noncomputable def sharpBound (a1 K : ℝ) : ℝ :=
  (K / 2) * Real.exp (2 * K + 1 - 2 * Real.eulerMascheroniConstant + sharpEta a1 K)

/-! ## Existence: counted blocks fit inside `[1,s]`

The `√(2D/K)` cutoff gives `K·j ≤ 2D`, which is *exactly* the fact the original `block_fits` derives
internally (it actually only uses `Kj ≤ 2D`, despite proving the stronger `Kj ≤ D`).  So the existence
proof is the same verified arithmetic, fed a cleaner hypothesis. -/

/-- From `j ≤ √(2D/K)` and `j ≥ 1`: `K·j ≤ 2D` (since `K·j ≤ K·j² ≤ 2D`). -/
theorem Kj_le_two_D_of_le_sqrt (K : ℕ) (D : ℝ) (hK : 1 ≤ K) (hD : 0 ≤ D)
    (j : ℕ) (hj : 1 ≤ j) (hjA : (j : ℝ) ≤ Real.sqrt (2 * D / K)) :
    (K : ℝ) * j ≤ 2 * D := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hjsq : (j : ℝ) ^ 2 ≤ 2 * D / K := by
    have h2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (j : ℝ)) hjA 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hKjsq : (K : ℝ) * (j : ℝ) ^ 2 ≤ 2 * D := by
    have h := mul_le_mul_of_nonneg_left hjsq hKpos.le
    have e : (K : ℝ) * (2 * D / K) = 2 * D := by field_simp
    rwa [e] at h
  have hjj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith [show (1 : ℝ) ≤ j from by exact_mod_cast hj]
  have hmono : (K : ℝ) * j ≤ (K : ℝ) * (j : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hjj hKpos.le
  linarith

/-- **Existence (sharp cutoff).**  For `1 ≤ j` with `K·j ≤ 2·(a s)` and an offset `i` below the real
threshold `lb j`, the block `(i+1, i+j)` lies inside `[1,s]`.  Same arithmetic as the original
`block_fits`. -/
theorem block_fits_sharp (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (j : ℕ) (hj : 1 ≤ j) (hKj2D : (K : ℝ) * j ≤ 2 * (a s : ℝ))
    (i : ℕ) (hi : (i : ℝ) < lb (a 1 : ℝ) (K : ℝ) (a s : ℝ) j) :
    i + j ≤ s := by
  simp only [lb] at hi
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hKjpos : (0 : ℝ) < (K : ℝ) * j := mul_pos hKpos hjpos
  have hpb : a s ≤ a 1 + (s - 1) * K := by
    have h := pointwise_bound hgap (s - 1) (by omega)
    simpa [Nat.sub_add_cancel hs] using h
  have hpb_real : (a s : ℝ) ≤ (a 1 : ℝ) + ((s : ℝ) - 1) * K := by
    have h : (a s : ℝ) ≤ (a 1 : ℝ) + ((s - 1 : ℕ) : ℝ) * K := by exact_mod_cast hpb
    rw [Nat.cast_sub hs] at h; push_cast at h; linarith
  have hmul : (i : ℝ) * (2 * (K : ℝ) * j) < 2 * (a s : ℝ) - 2 * (a 1 : ℝ) * j
      - (K : ℝ) * j * ((j : ℝ) - 1) :=
    calc (i : ℝ) * (2 * (K : ℝ) * j)
        < ((a s : ℝ) / ((K : ℝ) * j) - (a 1 : ℝ) / (K : ℝ) - ((j : ℝ) - 1) / 2)
            * (2 * (K : ℝ) * j) := mul_lt_mul_of_pos_right hi (by linarith)
      _ = 2 * (a s : ℝ) - 2 * (a 1 : ℝ) * j - (K : ℝ) * j * ((j : ℝ) - 1) := by field_simp
  have hprod : ((j : ℝ) - 1) * ((K : ℝ) * j - 2 * (a s : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by linarith [show (1 : ℝ) ≤ j from by exact_mod_cast hj]) (by linarith)
  have hprod2 : ((j : ℝ) - 1) * ((a s : ℝ) - (a 1 : ℝ) - ((s : ℝ) - 1) * K) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by linarith [show (1 : ℝ) ≤ j from by exact_mod_cast hj]) (by linarith)
  have hlt : (i : ℝ) + j < s := by
    have ha1_nn : (0 : ℝ) ≤ a 1 := Nat.cast_nonneg _
    have hi_nn : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    nlinarith [mul_pos hKjpos (show (0 : ℝ) < s by exact_mod_cast show 0 < s by omega)]
  have hlt_nat : i + j < s := by exact_mod_cast hlt
  omega

/-! ## Analytic threshold

The heart of the sharp constant.  With `s := √(2D/K)` and cutoff `A := ⌊s⌋₊`:
`Σ_{j=1}^A lb j ≥ (D/2K)(2·log s + 2γ − 1) − s·(1 + a/K) ≥ D` once `D ≥ sharpBound`.
Factored into a pure-algebra core, the threshold facts about `s`, and the counting chain. -/

/-- **Pure-algebra core.**  Given `s² = 2D/K`, the harmonic-sum lower bound `2 log s ≥ 2K+1−2γ+η`,
and `s·η ≥ 4(1+a/K)`, the lower-bound expression dominates `D`.  Here `η` is abstract (the
exp-products are opaque atoms that cancel via `hsη`). -/
private lemma final_algebra (K a : ℕ) (hK : 1 ≤ K) (D s gam : ℝ)
    (hspos : 0 < s) (hs2 : s ^ 2 = 2 * D / K)
    (eta : ℝ)
    (hlogs : 2 * (K : ℝ) + 1 - 2 * gam + eta ≤ 2 * Real.log s)
    (hsη : 4 * ((a : ℝ) / K + 1) ≤ s * eta) :
    D ≤ (D / (2 * K)) * (2 * Real.log s + 2 * gam - 1)
        - s * (1 + (a : ℝ) / K) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hD : D = K * s ^ 2 / 2 := by field_simp at hs2; linarith [hs2]
  have hDK : D / (2 * K) = s ^ 2 / 4 := by rw [hD]; field_simp; ring
  -- (s²/4)·(2K+1−2γ+η) ≤ (s²/4)·(2 log s)
  have hp1 : (s ^ 2 / 4) * (2 * (K : ℝ) + 1 - 2 * gam + eta)
      ≤ (s ^ 2 / 4) * (2 * Real.log s) :=
    mul_le_mul_of_nonneg_left hlogs (by positivity)
  -- (s/4)·4(1+a/K) ≤ (s/4)·(s·η)
  have hp2 : (s / 4) * (4 * ((a : ℝ) / K + 1)) ≤ (s / 4) * (s * eta) :=
    mul_le_mul_of_nonneg_left hsη (by positivity)
  rw [hDK]
  nlinarith [hp1, hp2, hspos]

/-- `√(exp X) = exp(X/2)`. -/
private lemma sqrt_exp (X : ℝ) : Real.sqrt (Real.exp X) = Real.exp (X / 2) := by
  rw [show Real.exp X = (Real.exp (X / 2)) ^ 2 from by rw [sq, ← Real.exp_add, add_halves]]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- **Counting chain (P2).**  The per-length lower bounds, summed over `j ≤ ⌊s⌋₊` with `s := √(2D/K)`,
dominate `(D/2K)(2 log s + 2γ − 1) − s(1 + a/K)`.  Uses the closed form `sum_lb_eq`, the
Euler–Mascheroni harmonic bound `H_A ≥ log A + γ`, and `log A ≥ log s − 1/(s−1)`.  Proven by clearing
the `1/K` denominators to a polynomial inequality. -/
private lemma counting_chain (K a : ℕ) (hK : 1 ≤ K) (D s : ℝ)
    (hspos : 0 < s) (hs2 : s ^ 2 = 2 * D / K) (hs_ge2 : 2 ≤ s) :
    (D / (2 * K)) * (2 * Real.log s + 2 * Real.eulerMascheroniConstant - 1)
        - s * (1 + (a : ℝ) / K)
      ≤ ∑ j ∈ Finset.Icc 1 ⌊s⌋₊, lb (a : ℝ) (K : ℝ) D j := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hs1pos : (0 : ℝ) < s - 1 := by linarith
  have hDval : D = K * s ^ 2 / 2 := by
    have h := hs2; field_simp at h; linarith [h]
  have hDpos : 0 < D := by nlinarith [hDval, mul_pos hKR (pow_pos hspos 2)]
  set A := ⌊s⌋₊ with hAdef
  rw [sum_lb_eq (a : ℝ) (K : ℝ) D hKne A]
  -- floor facts
  have hA2 : 2 ≤ A := Nat.le_floor (by exact_mod_cast hs_ge2)
  have hA1 : 1 ≤ A := by omega
  have hAR_le : (A : ℝ) ≤ s := Nat.floor_le hspos.le
  have hAR_lt : s - 1 < (A : ℝ) := by
    have := Nat.lt_floor_add_one s; linarith
  have hAR_pos : (0 : ℝ) < (A : ℝ) := by
    have h1A : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
    linarith
  -- harmonic: H_A ≥ log A + γ
  have hharm : Real.log (A : ℝ) + Real.eulerMascheroniConstant ≤ (harmonic A : ℝ) :=
    le_of_lt (log_add_gamma_lt_harmonic A hA1)
  -- log A ≥ log s − 1/(s−1)
  have hlogstep : Real.log s - 1 / (s - 1) ≤ Real.log (A : ℝ) := by
    have h1 : Real.log (s - 1) ≤ Real.log (A : ℝ) :=
      (Real.log_le_log_iff hs1pos hAR_pos).mpr (le_of_lt hAR_lt)
    have hd : Real.log (s / (s - 1)) ≤ s / (s - 1) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hspos) (ne_of_gt hs1pos)] at hd
    have he : s / (s - 1) - 1 = 1 / (s - 1) := by field_simp; ring
    linarith [hd, he, h1]
  -- error: D/(s−1) ≤ K·s
  have herr : D / (s - 1) ≤ (K : ℝ) * s := by
    rw [div_le_iff₀ hs1pos]; rw [hDval]; nlinarith [hs_ge2, hKR, hspos]
  -- cleared bound facts (×4D / ×4 / etc.)
  have h4Dnn : (0 : ℝ) ≤ 4 * D := by linarith
  have h_HA : 4 * D * (Real.log (A : ℝ) + Real.eulerMascheroniConstant) ≤ 4 * D * (harmonic A : ℝ) :=
    mul_le_mul_of_nonneg_left hharm h4Dnn
  have h_DlogA : 4 * D * Real.log s - 4 * (K : ℝ) * s ≤ 4 * D * Real.log (A : ℝ) := by
    have hstep : 4 * D * (Real.log s - 1 / (s - 1)) ≤ 4 * D * Real.log (A : ℝ) :=
      mul_le_mul_of_nonneg_left hlogstep h4Dnn
    have hD_over : 4 * D * (1 / (s - 1)) ≤ 4 * (K : ℝ) * s := by
      rw [mul_one_div]; rw [div_le_iff₀ hs1pos] at herr ⊢; nlinarith [herr]
    nlinarith [hstep, hD_over]
  have hAA : (K : ℝ) * ((A : ℝ) * ((A : ℝ) - 1)) ≤ 2 * D := by
    have hAsq : (A : ℝ) * ((A : ℝ) - 1) ≤ s ^ 2 := by nlinarith [hAR_le, hAR_pos, hAR_lt]
    nlinarith [hAsq, hs2, hKR, mul_le_mul_of_nonneg_left hAsq hKR.le]
  have hAs : 0 ≤ 4 * (a : ℝ) * (s - (A : ℝ)) := by
    apply mul_nonneg (by positivity); linarith [hAR_le]
  -- the cleared inequality, then divide back by 4K
  have hcleared : 2 * D * (2 * Real.log s + 2 * Real.eulerMascheroniConstant - 1)
        - 4 * (K : ℝ) * s - 4 * s * a
      ≤ 4 * D * (harmonic A : ℝ) - 4 * (A : ℝ) * a - (K : ℝ) * ((A : ℝ) * ((A : ℝ) - 1)) := by
    nlinarith [h_HA, h_DlogA, hAA, hAs]
  have e1 : 4 * (K : ℝ) * ((D / (2 * K)) * (2 * Real.log s + 2 * Real.eulerMascheroniConstant - 1)
        - s * (1 + (a : ℝ) / K))
      = 2 * D * (2 * Real.log s + 2 * Real.eulerMascheroniConstant - 1)
        - 4 * (K : ℝ) * s - 4 * s * a := by field_simp; ring
  have e2 : 4 * (K : ℝ) * ((D / K) * (harmonic A : ℝ) - (A : ℝ) * a / K
        - (A : ℝ) * ((A : ℝ) - 1) / 4)
      = 4 * D * (harmonic A : ℝ) - 4 * (A : ℝ) * a - (K : ℝ) * ((A : ℝ) * ((A : ℝ) - 1)) := by
    field_simp
  apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 4 * K by positivity)
  rw [e1, e2]; exact hcleared

/-- **Analytic threshold (sharp).**  With cutoff `A = ⌊√(2D/K)⌋₊`, once `D ≥ sharpBound a K` the
per-length lower bounds sum to at least `D`.  Leading constant `½·e^{1−2γ}`. -/
theorem sum_lb_ge_D_sharp (K a : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ a) (D : ℝ)
    (hD : sharpBound (a : ℝ) (K : ℝ) ≤ D) :
    D ≤ ∑ j ∈ Finset.Icc 1 ⌊Real.sqrt (2 * D / (K : ℝ))⌋₊, lb (a : ℝ) (K : ℝ) D j := by
  set g := Real.eulerMascheroniConstant with hg
  set η := sharpEta (a : ℝ) (K : ℝ) with hη_def
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hg23 : g < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hηpos : 0 < η := by rw [hη_def, sharpEta]; positivity
  have hηnn : 0 ≤ η := le_of_lt hηpos
  have hDpos : 0 < D := lt_of_lt_of_le (by rw [sharpBound]; positivity) hD
  have hDKnn : (0 : ℝ) ≤ 2 * D / K := by positivity
  -- s := √(2D/K)
  set s := Real.sqrt (2 * D / (K : ℝ)) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 2 * D / K := Real.sq_sqrt hDKnn
  -- E := exp(2K+1-2g+η) ≤ 2D/K
  have hsb_eq : 2 * sharpBound (a : ℝ) (K : ℝ) / K = Real.exp (2 * K + 1 - 2 * g + η) := by
    rw [sharpBound, ← hg, ← hη_def]; field_simp
  have hE : Real.exp (2 * (K : ℝ) + 1 - 2 * g + η) ≤ 2 * D / K := by
    rw [← hsb_eq]; gcongr
  -- s ≥ exp(K + 1/2 - g + η/2)
  have hs_full : Real.exp ((K : ℝ) + 1 / 2 - g + η / 2) ≤ s := by
    have h1 : Real.sqrt (Real.exp (2 * (K : ℝ) + 1 - 2 * g + η)) ≤ s :=
      Real.sqrt_le_sqrt hE
    rwa [sqrt_exp, show (2 * (K : ℝ) + 1 - 2 * g + η) / 2 = (K : ℝ) + 1 / 2 - g + η / 2 from by ring]
      at h1
  -- hlogs : 2K+1-2g+η ≤ 2 log s
  have hlogs : 2 * (K : ℝ) + 1 - 2 * g + η ≤ 2 * Real.log s := by
    have := (Real.le_log_iff_exp_le hspos).mpr hs_full
    linarith
  -- s ≥ exp(K + 1/2 - g)
  have hs_exp : Real.exp ((K : ℝ) + 1 / 2 - g) ≤ s :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) hs_full
  -- hsη : 4(1 + a/K) ≤ s·η
  have hs_exp_ge1 : 1 ≤ s * Real.exp (g - 1 / 2 - K) := by
    have heq : Real.exp ((K : ℝ) + 1 / 2 - g) * Real.exp (g - 1 / 2 - K) = 1 := by
      rw [← Real.exp_add, show (K : ℝ) + 1 / 2 - g + (g - 1 / 2 - K) = 0 from by ring, Real.exp_zero]
    calc (1 : ℝ) = Real.exp ((K : ℝ) + 1 / 2 - g) * Real.exp (g - 1 / 2 - K) := heq.symm
      _ ≤ s * Real.exp (g - 1 / 2 - K) := by
          apply mul_le_mul_of_nonneg_right hs_exp (Real.exp_pos _).le
  have hsη : 4 * ((a : ℝ) / K + 1) ≤ s * η := by
    have hcoef : (0 : ℝ) ≤ 4 * ((a : ℝ) / K + 1) := by positivity
    have hkey : 4 * ((a : ℝ) / K + 1) * 1
        ≤ 4 * ((a : ℝ) / K + 1) * (s * Real.exp (g - 1 / 2 - K)) :=
      mul_le_mul_of_nonneg_left hs_exp_ge1 hcoef
    have hsη_eq : s * η = 4 * ((a : ℝ) / K + 1) * (s * Real.exp (g - 1 / 2 - K)) := by
      rw [hη_def, sharpEta, ← hg]; ring
    rw [hsη_eq]; linarith
  -- s ≥ 2  (for the counting chain)
  have hs_ge2 : 2 ≤ s := by
    have hlog2 : Real.log 2 < (K : ℝ) + 1 / 2 - g := by
      have := Real.log_two_lt_d9
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((K : ℝ) + 1 / 2 - g) := Real.exp_le_exp.mpr (le_of_lt hlog2)
      _ ≤ s := hs_exp
  -- The counting chain (P2): Σ lb ≥ (D/2K)(2 log s + 2γ − 1) − s(1 + a/K)
  have hchain : (D / (2 * K)) * (2 * Real.log s + 2 * g - 1) - s * (1 + (a : ℝ) / K)
      ≤ ∑ j ∈ Finset.Icc 1 ⌊s⌋₊, lb (a : ℝ) (K : ℝ) D j :=
    counting_chain K a hK D s hspos hs2 hs_ge2
  -- Assemble via final_algebra
  have hfinal := final_algebra K a hK D s g hspos hs2 η hlogs hsη
  exact le_trans hfinal hchain

/-! ## Assembly: the sharp headline -/

/-- **Counting lower bound (sharp).**  With cutoff `A = ⌊√(2·a_s/K)⌋₊` and `a s ≥ sharpBound`, the
small-c-sum block count is at least `a s`.  Mirrors `smallBlocks_card_ge_of_le`, fed by
`sum_lb_ge_D_sharp` and `block_fits_sharp`. -/
theorem smallBlocks_card_ge_of_le_sharp (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hbig : sharpBound (a 1 : ℝ) (K : ℝ) ≤ (a s : ℝ)) :
    a s ≤ ∑ j ∈ Finset.Icc 1 ⌊Real.sqrt (2 * (a s : ℝ) / K)⌋₊, (offsetSet a s (a s) j).card := by
  set A := ⌊Real.sqrt (2 * (a s : ℝ) / K)⌋₊ with hAdef
  have hpre : (∑ j ∈ Finset.Icc 1 A, lb (a 1 : ℝ) (K : ℝ) (a s : ℝ) j)
      ≤ ((∑ j ∈ Finset.Icc 1 A, (offsetSet a s (a s) j).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjsqrt : (j : ℝ) ≤ Real.sqrt (2 * (a s : ℝ) / K) := by
      calc (j : ℝ) ≤ (A : ℝ) := by exact_mod_cast hj.2
        _ ≤ Real.sqrt (2 * (a s : ℝ) / K) := Nat.floor_le (Real.sqrt_nonneg _)
    have hKj2D : (K : ℝ) * j ≤ 2 * (a s : ℝ) :=
      Kj_le_two_D_of_le_sqrt K (a s : ℝ) hK (by positivity) j hj.1 hjsqrt
    exact offsetSet_card_real_ge hgap hK (a s) j hj.1
      (fun i hi => block_fits_sharp a s K hK hs hgap j hj.1 hKj2D i hi)
  have hge := sum_lb_ge_D_sharp K (a 1) hK ha1 (a s : ℝ) hbig
  have : (a s : ℝ) ≤ ((∑ j ∈ Finset.Icc 1 A, (offsetSet a s (a s) j).card : ℕ) : ℝ) :=
    le_trans hge hpre
  exact_mod_cast this

/-- **SHARP HEADLINE.**  A strictly increasing sequence on `[1,s]` with gaps `≤ K` and all
consecutive-block sums distinct has last term below `sharpBound = (K/2)·exp(2K+1−2γ+η_K)`, leading
constant `½·e^{1−2γ} ≈ 0.4285` — a `≈17.25×` improvement over `hegyvari_thm3`. -/
theorem hegyvari_thm3_sharp (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hdist : AllCSumsDistinct a s) :
    (a s : ℝ) < sharpBound (a 1 : ℝ) (K : ℝ) := by
  by_contra hcon
  push Not at hcon
  set D := a s with hD
  have hD1 : 1 ≤ D := le_trans ha1 (a_one_le hmono s hs (le_refl s))
  have hlower : D ≤ ∑ j ∈ Finset.Icc 1 ⌊Real.sqrt (2 * (D : ℝ) / K)⌋₊, (offsetSet a s D j).card :=
    smallBlocks_card_ge_of_le_sharp a s K hK hs ha1 hgap hcon
  have hmid : (∑ j ∈ Finset.Icc 1 ⌊Real.sqrt (2 * (D : ℝ) / K)⌋₊, (offsetSet a s D j).card)
      ≤ (smallBlocks a s D).card := sum_offsetSet_card_le a s D _
  have hupper : (smallBlocks a s D).card ≤ D - 1 := smallBlocks_card_le a s D ha1 hmono hdist
  omega

/-- Every achievable last term lies strictly below `sharpBound`. -/
theorem validLastTerms_lt_sharpBound (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init)
    {n : ℕ} (hn : n ∈ validLastTerms init K) :
    (n : ℝ) < sharpBound (init : ℝ) (K : ℝ) := by
  obtain ⟨s, seq, hseq1, hs, hseqn, hmono, hgap, hdist⟩ := hn
  have ha1 : 1 ≤ seq 1 := hseq1 ▸ ha
  have hlt := hegyvari_thm3_sharp seq s K hK hs ha1 hmono hgap hdist
  rw [hseq1] at hlt
  have hns : (n : ℝ) = (seq s : ℝ) := by exact_mod_cast hseqn.symm
  linarith [hlt, hns]

/-- **`f(a,K) ≤ sharpBound`** — the sharp constant in supremum form.  `f(a,K) ≤ ½·e^{1−2γ}·K·e^{2K}·
e^{η_K}`, `η_K → 0`. -/
theorem hegyvariF_le_sharpBound (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init) :
    (hegyvariF init K : ℝ) ≤ sharpBound (init : ℝ) (K : ℝ) := by
  unfold hegyvariF
  have hne : (validLastTerms init K).Nonempty :=
    ⟨init, 1, fun _ => init, rfl, le_refl 1, rfl,
      fun _ h1 h2 => by omega, fun _ h1 h2 => by omega,
      fun _ _ _ _ hu1 _ hv1s _ _ hv2s _ => ⟨by omega, by omega⟩⟩
  have hLpos : (0 : ℝ) ≤ sharpBound (init : ℝ) (K : ℝ) := by rw [sharpBound]; positivity
  have hle : sSup (validLastTerms init K) ≤ ⌊sharpBound (init : ℝ) (K : ℝ)⌋₊ :=
    csSup_le hne fun n hn => by
      have hlt := validLastTerms_lt_sharpBound init K hK ha hn
      have h1 : n = ⌊(n : ℝ)⌋₊ := (Nat.floor_natCast n).symm
      exact h1 ▸ Nat.floor_mono (le_of_lt hlt)
  exact le_trans (by exact_mod_cast hle) (Nat.floor_le hLpos)

end LeanGallery.Combinatorics.Erdos1213
