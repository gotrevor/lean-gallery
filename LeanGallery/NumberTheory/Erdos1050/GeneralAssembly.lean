/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.GeneralLemma3
import LeanGallery.NumberTheory.Erdos1050.GeneralError
import LeanGallery.NumberTheory.Erdos1050.Criterion

/-!
# Borwein Theorem 1 — full assembly for the `C > 2` regime (no cited axiom)

With all five Borwein lemmas now general and machine-checked —
* Lemma 1 (residue identity) `EtermG_eq_pValG`,
* Lemma 2 (denominator integrality) `BdenG_cast`,
* Lemma 3 (numerator integrality) `AcorrG_int`, assembled with 1+2 into `borwein_integralityG`,
* Lemma 4 (error → 0) `cleared_error_tendstoG`,
* Lemma 5 (non-vanishing) `EtermG_ne_zero` —
the integer-approximant existence `borwein_approximants` is now a **THEOREM** (not a cited axiom) for
integer `q ≥ 2` and `C = α/β > 2` (Borwein's shifted magnitude regime). Hence the reduced q-harmonic
value `z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹` is **unconditionally irrational** for every such `(q, C)` — no
appeal to `borwein_approximants`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Filter Topology

/-- **Borwein's integer approximants — a THEOREM for `|C| = |α/β| > 2`** (general analog of the
discharged `q=2` chain, with no cited axiom). For integer `q ≥ 2` and `α, β` with `|α/β| > 2`, there are
integer sequences `aₙ, bₙ` with `bₙ·z − aₙ ≠ 0` and `bₙ·z − aₙ → 0`, where
`z = ∑_{j≥0}(1 − (α/β)·q^{j+1})⁻¹`. Exactly the conclusion of the `borwein_approximants` axiom for the
`(q, α/β)` instances with `|α/β| > 2` (both signs — non-vanishing by Lemma 5's positive/negative
regimes; error → 0 by the sign-independent Lemma 4). -/
theorem borwein_approximantsG {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    ∃ a b : ℕ → ℤ,
      (∀ n, (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n ≠ 0) ∧
      Tendsto (fun n => (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n) atTop (𝓝 0) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  -- `|C| > 2` makes every `|C·q^{h+1}| ≥ |C| > 2 > 1`, so the non-degeneracy hypothesis is automatic.
  have hCn : ∀ h : ℕ, ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1) ≠ 1 := by
    intro h hcontra
    have hqp : (1 : ℝ) ≤ (q : ℝ) ^ (h + 1) := one_le_pow₀ (by linarith)
    have habs : |((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1)| = 1 := by rw [hcontra]; norm_num
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ (h + 1))] at habs
    nlinarith [hC2, hqp, habs]
  -- non-vanishing of the error term, by the sign regime of `C`.
  have hEne : ∀ k, 1 ≤ k → EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) k ≠ 0 := by
    intro k hk
    rcases lt_abs.mp hC2 with hCp | hCm
    · exact EtermG_ne_zero hq2 hCp hk
    · exact EtermG_ne_zero_neg hq2 (by linarith : (α : ℝ) / (β : ℝ) < -2) hk
  have hqabs : 2 ≤ |q| := by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ q)]; exact hq
  obtain ⟨a, b, hab⟩ := borwein_integralityG hqabs hα hβ hCn
  -- Shift the index by 1 to land in `n ≥ 1`, where the identity and Lemmas 4/5 apply.
  refine ⟨fun n => a (n + 1), fun n => b (n + 1), ?_, ?_⟩
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (WtermG_ne_zero hq1 hCn (by omega)))
      (hEne (n + 1) (by omega))
    exact pow_ne_zero _ hβ0
  · have hshift : Tendsto (fun n => (β : ℝ) ^ (2 * (n + 1))
        * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)
        * EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)) atTop (𝓝 0) :=
      (cleared_error_tendstoG hq2 hC2 hβ0).comp (tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- **Borwein Theorem 1, reduced q-harmonic value, UNCONDITIONAL for `|C| = |α/β| > 2`.** The value
`z = ∑_{j≥0}(1 − (α/β)·q^{j+1})⁻¹` is irrational for integer `q ≥ 2` and `|α/β| > 2` (both signs), with
**no cited axiom** — every Borwein lemma is machine-checked. -/
theorem zG_irrational_of_abs_gt_two {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  obtain ⟨a, b, hne, hlim⟩ := borwein_approximantsG hq hα hβ hC2
  exact irrational_of_intApprox _ a b hne hlim

/-! ## The magnitude shift `C → C·qᵐ` — extending to all `C = α/β > 0`

`z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹` and `z' = ∑_{j≥0}(1 − (C·qᵐ)·q^{j+1})⁻¹` differ by the finite rational
head `∑_{j<m}(1 − C·q^{j+1})⁻¹` (`z = head + z'`). For `C > 0` the shifted parameter `C·qᵐ → ∞`, so some
`m` lands in the `> 2` regime; then `z'` is irrational by `zG_irrational_of_gt_two`, hence so is `z`.
This is Borwein's reduction remark (`c → c·qᵐ` to reach `|c| > 2`), in the reduced parametrisation. -/

/-- **Shift decomposition**: `z(C) = (finite head) + z(C·qᵐ)`, for `2 ≤ |q|`, `C ≠ 0`. The tail of the
`z(C)` series is exactly the `z(C·qᵐ)` series (reindex `j ↦ j+m`). -/
lemma zG_shift {q C : ℝ} (hq : 2 ≤ |q|) (hC : C ≠ 0) (m : ℕ) :
    zG q C = (∑ j ∈ Finset.range m, (1 - C * q ^ (j + 1))⁻¹) + zG q (C * q ^ m) := by
  have hsum := qharmonic_summable q C hq hC
  unfold zG
  rw [← Summable.sum_add_tsum_nat_add m hsum]
  congr 1
  apply tsum_congr
  intro i
  rw [show (i + m) + 1 = (i + 1) + m from by ring, pow_add]
  ring

/-- **Borwein Theorem 1, UNCONDITIONAL for `C = α/β > 0`** (no cited axiom). For integer `q ≥ 2` and
`α, β` with `α/β > 0`, the value `z = ∑_{j≥0}(1 − (α/β)·q^{j+1})⁻¹` is irrational. Proof: shift
`C → C·qᵐ` with `m` large enough that `C·qᵐ > 2`; `z = (rational head) + z(C·qᵐ)`, and `z(C·qᵐ)` is
irrational by `zG_irrational_of_gt_two`. Extends the `> 2` family to the entire positive half-line. -/
theorem zG_irrational_of_pos {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hCpos : 0 < (α : ℝ) / (β : ℝ)) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [abs_of_pos (by linarith)]; exact hq2
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hC0 : ((α : ℝ) / (β : ℝ)) ≠ 0 := ne_of_gt hCpos
  -- pick `m` with `C·qᵐ > 2` (since `C > 0` and `qᵐ → ∞`)
  have htend : Tendsto (fun m : ℕ => ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m) atTop atTop :=
    Tendsto.const_mul_atTop hCpos (tendsto_pow_atTop_atTop_of_one_lt hq1)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop 2).exists
  -- the shifted value is irrational (`> 2` regime), via the integer numerator `α·qᵐ`
  have hαqm : (α * q ^ m : ℤ) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ (by omega : (q : ℤ) ≠ 0))
  have hCqm_eq : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) = ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m := by
    push_cast; ring
  have hC2 : 2 < ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) := by rw [hCqm_eq]; exact hm
  have hC2abs : 2 < |((α * q ^ m : ℤ) : ℝ) / (β : ℝ)| := by rw [abs_of_pos (by linarith)]; exact hC2
  have h_tail : Irrational (zG (q : ℝ) (((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m)) := by
    have := zG_irrational_of_abs_gt_two hq hαqm hβ hC2abs
    rwa [hCqm_eq] at this
  -- decompose and transfer irrationality across the rational head
  rw [zG_shift hqabs hC0 m]
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = ∑ j ∈ Finset.range m, (1 - (α : ℝ) / (β : ℝ) * (q : ℝ) ^ (j + 1))⁻¹ := by
    refine ⟨∑ j ∈ Finset.range m, (1 - (α : ℚ) / (β : ℚ) * (q : ℚ) ^ (j + 1))⁻¹, ?_⟩
    push_cast
    rfl
  rw [← hr]
  exact irrational_ratCast_add_iff.mpr h_tail

/-- **Borwein Theorem 1, UNCONDITIONAL for `C = α/β < 0`** (no cited axiom). Mirror of
`zG_irrational_of_pos`: for `C < 0`, `C·qᵐ → −∞`, so some `m` lands `C·qᵐ < −2` (`|·| > 2` regime);
`z = (rational head) + z(C·qᵐ)` then transfers irrationality. -/
theorem zG_irrational_of_neg {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hCneg : (α : ℝ) / (β : ℝ) < 0) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [abs_of_pos (by linarith)]; exact hq2
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hC0 : ((α : ℝ) / (β : ℝ)) ≠ 0 := ne_of_lt hCneg
  -- pick `m` with `C·qᵐ < −2` (since `−C > 0` and `qᵐ → ∞`)
  have htend : Tendsto (fun m : ℕ => (-((α : ℝ) / (β : ℝ))) * (q : ℝ) ^ m) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < -((α : ℝ) / (β : ℝ)))
      (tendsto_pow_atTop_atTop_of_one_lt hq1)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop 2).exists
  have hαqm : (α * q ^ m : ℤ) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ (by omega : (q : ℤ) ≠ 0))
  have hCqm_eq : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) = ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m := by
    push_cast; ring
  have hCqm_neg : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) < -2 := by rw [hCqm_eq]; nlinarith [hm]
  have hC2abs : 2 < |((α * q ^ m : ℤ) : ℝ) / (β : ℝ)| := by
    rw [abs_of_neg (by linarith)]; linarith
  have h_tail : Irrational (zG (q : ℝ) (((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m)) := by
    have := zG_irrational_of_abs_gt_two hq hαqm hβ hC2abs
    rwa [hCqm_eq] at this
  rw [zG_shift hqabs hC0 m]
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = ∑ j ∈ Finset.range m, (1 - (α : ℝ) / (β : ℝ) * (q : ℝ) ^ (j + 1))⁻¹ := by
    refine ⟨∑ j ∈ Finset.range m, (1 - (α : ℚ) / (β : ℚ) * (q : ℚ) ^ (j + 1))⁻¹, ?_⟩
    push_cast
    rfl
  rw [← hr]
  exact irrational_ratCast_add_iff.mpr h_tail

/-- **Borwein Theorem 1, reduced value, UNCONDITIONAL for every nonzero `C = α/β`** (`q ≥ 2`), no cited
axiom. Combines the positive (`zG_irrational_of_pos`) and negative (`zG_irrational_of_neg`) regimes. -/
theorem zG_irrational {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC0 : (α : ℝ) / (β : ℝ) ≠ 0) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  rcases lt_or_gt_of_ne hC0 with h | h
  · exact zG_irrational_of_neg hq hα hβ h
  · exact zG_irrational_of_pos hq hα hβ h

/-! ## NEGATIVE base `q ≤ −2`: the full axiom-free chain for `2 ≤ |q|` (both signs of base)

Mirrors the positive-base assembly, routing non-vanishing through `EtermG_ne_zero_negbase`
(the sign dichotomy) for `q ≤ −2`. The magnitude shift uses `|C·qᵐ| = |C|·|q|ᵐ → ∞`, which lands
some `m` in the `|·| > 2` regime regardless of the alternating sign of `qᵐ`. -/

/-- **Borwein approximants, both signs of integer base** (`2 ≤ |q|`, `|α/β| > 2`), no cited axiom. -/
theorem borwein_approximantsG_abs {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    ∃ a b : ℕ → ℤ,
      (∀ n, (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n ≠ 0) ∧
      Tendsto (fun n => (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n) atTop (𝓝 0) := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by linarith
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hCn : ∀ h : ℕ, ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1) ≠ 1 := by
    intro h hcontra
    have hqp : (1 : ℝ) ≤ |(q : ℝ)| ^ (h + 1) := one_le_pow₀ (by linarith)
    have habs : |((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1)| = 1 := by rw [hcontra]; norm_num
    rw [abs_mul, abs_pow] at habs
    nlinarith [hC2, hqp, habs, abs_nonneg ((α : ℝ) / (β : ℝ)),
      mul_le_mul (le_of_lt hC2) hqp zero_le_one (abs_nonneg ((α : ℝ) / (β : ℝ)))]
  have hEne : ∀ k, 1 ≤ k → EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) k ≠ 0 := by
    intro k hk
    by_cases hq0 : 0 ≤ q
    · have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
        rwa [abs_of_nonneg (by exact_mod_cast hq0 : (0 : ℝ) ≤ (q : ℝ))] at hqabs
      rcases lt_abs.mp hC2 with hCp | hCm
      · exact EtermG_ne_zero hq2 hCp hk
      · exact EtermG_ne_zero_neg hq2 (by linarith) hk
    · push Not at hq0
      have hqn2 : (q : ℝ) ≤ -2 := by
        rw [abs_of_neg (by exact_mod_cast hq0 : (q : ℝ) < 0)] at hqabs; linarith
      exact EtermG_ne_zero_negbase hqn2 hC2 hk
  obtain ⟨a, b, hab⟩ := borwein_integralityG hq hα hβ hCn
  refine ⟨fun n => a (n + 1), fun n => b (n + 1), ?_, ?_⟩
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (WtermG_ne_zero_abs hq1abs hCn (by omega)))
      (hEne (n + 1) (by omega))
    exact pow_ne_zero _ hβ0
  · have hshift : Tendsto (fun n => (β : ℝ) ^ (2 * (n + 1))
        * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)
        * EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)) atTop (𝓝 0) :=
      (cleared_error_tendstoG_abs hqabs hC2 hβ0).comp (tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- Reduced value irrational for `2 ≤ |q|`, `|α/β| > 2`. -/
theorem zG_irrational_of_abs_gt_two_abs {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  obtain ⟨a, b, hne, hlim⟩ := borwein_approximantsG_abs hq hα hβ hC2
  exact irrational_of_intApprox _ a b hne hlim

/-- **Reduced value irrational, every nonzero `C`, both signs of base** (`2 ≤ |q|`), no cited axiom.
The magnitude shift `C → C·qᵐ` reaches `|C·qᵐ| = |C|·|q|ᵐ > 2` for large `m` (works for `q < 0` too,
since only the magnitude matters); `z = (rational head) + z(C·qᵐ)` then transfers irrationality. -/
theorem zG_irrational_abs {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC0 : (α : ℝ) / (β : ℝ) ≠ 0) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by linarith
  have hqZ : (q : ℤ) ≠ 0 := by rintro rfl; norm_num at hq
  have htend : Tendsto (fun m : ℕ => |(α : ℝ) / (β : ℝ)| * |(q : ℝ)| ^ m) atTop atTop :=
    Tendsto.const_mul_atTop (abs_pos.mpr hC0) (tendsto_pow_atTop_atTop_of_one_lt hq1abs)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop 2).exists
  have hαqm : (α * q ^ m : ℤ) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ hqZ)
  have hCqm_eq : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) = ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m := by
    push_cast; ring
  have hC2abs : 2 < |((α * q ^ m : ℤ) : ℝ) / (β : ℝ)| := by rw [hCqm_eq, abs_mul, abs_pow]; exact hm
  have h_tail : Irrational (zG (q : ℝ) (((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m)) := by
    have := zG_irrational_of_abs_gt_two_abs hq hαqm hβ hC2abs
    rwa [hCqm_eq] at this
  rw [zG_shift hqabs hC0 m]
  obtain ⟨r, hr⟩ : ∃ r : ℚ,
      (r : ℝ) = ∑ j ∈ Finset.range m, (1 - (α : ℝ) / (β : ℝ) * (q : ℝ) ^ (j + 1))⁻¹ := by
    refine ⟨∑ j ∈ Finset.range m, (1 - (α : ℚ) / (β : ℚ) * (q : ℚ) ^ (j + 1))⁻¹, ?_⟩
    push_cast; rfl
  rw [← hr]
  exact irrational_ratCast_add_iff.mpr h_tail

/-! ## Axiom-free headline corollaries (all nonzero `C`, all `c`; `q ≥ 2`) -/

/-- **Borwein Theorem 1, reduced form, AXIOM-FREE for `C > 0`.** The reduced q-harmonic value
`∑_{n≥0}(1 − C·q^{n+1})⁻¹` is irrational for every integer `q ≥ 2` and rational `C` with `(C:ℝ) > 0`.
This is the axiom-free analog of `qharmonic_irrational` (which routes through `borwein_approximants`),
covering both `C`-signs. -/
theorem qharmonic_irrational' (q : ℤ) (hq : 2 ≤ q) (C : ℚ) (hCne : C ≠ 0) :
    Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) := by
  have hαne : C.num ≠ 0 := Rat.num_ne_zero.mpr hCne
  have hβne : (C.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr C.den_nz
  have hcast : ((C.num : ℝ) / ((C.den : ℤ) : ℝ)) = (C : ℝ) := by
    push_cast; exact (Rat.cast_def C).symm
  have hC0 : (C.num : ℝ) / ((C.den : ℤ) : ℝ) ≠ 0 := by rw [hcast]; exact Rat.cast_ne_zero.mpr hCne
  have h := zG_irrational hq hαne hβne hC0
  rw [hcast] at h
  exact h

/-- **Borwein Theorem 1, FULLY AXIOM-FREE for every nonzero `c`** (and `q ≥ 2`). The series
`∑_{n≥1} 1/(qⁿ + c)` is irrational for integer `q ≥ 2` and any nonzero rational `c` with `qⁿ⁺¹ + c ≠ 0`.
**No appeal to `borwein_approximants`** — every one of Borwein's five lemmas is machine-checked, and the
magnitude shift `c → c·qᵐ` covers all `c`. (The original `borwein_thm1` allows `q ≤ −2` too but cites
the axiom; this is the axiom-free version for positive base `q ≥ 2`.) -/
theorem borwein_thm1' (q : ℤ) (hq : 2 ≤ q) (c : ℚ) (hc0 : c ≠ 0)
    (hcn : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := by
  set C : ℚ := -1 / c with hCdef
  have hCne : C ≠ 0 := by
    rw [hCdef]; intro h; rw [div_eq_zero_iff] at h
    rcases h with h | h
    · norm_num at h
    · exact hc0 h
  -- Affine identity (unconditional): `c · ∑ 1/(qⁿ+c) = ∑ (1 − C·qⁿ)⁻¹` (as in `borwein_thm1`).
  have key : (c : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ)))
      = ∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hden : (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0 := hcn n
    rw [hCdef]
    push_cast
    generalize hx : (q : ℝ) ^ (n + 1) = x at hden ⊢
    field_simp
    rw [eq_div_iff (show (c : ℝ) - -x ≠ 0 by rw [sub_neg_eq_add, add_comm]; exact hden)]
    ring
  have hirr : Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) :=
    qharmonic_irrational' q hq C hCne
  rw [← key] at hirr
  exact (irrational_ratCast_mul_iff.mp hirr).2

/-! ## Axiom-free headlines for `2 ≤ |q|` (both signs of base) — the discharge of `borwein_approximants` -/

/-- **Borwein Theorem 1, reduced form, AXIOM-FREE for `2 ≤ |q|`** (both signs of base). -/
theorem qharmonic_irrational_abs (q : ℤ) (hq : 2 ≤ |q|) (C : ℚ) (hCne : C ≠ 0) :
    Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) := by
  have hαne : C.num ≠ 0 := Rat.num_ne_zero.mpr hCne
  have hβne : (C.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr C.den_nz
  have hcast : ((C.num : ℝ) / ((C.den : ℤ) : ℝ)) = (C : ℝ) := by
    push_cast; exact (Rat.cast_def C).symm
  have hC0 : (C.num : ℝ) / ((C.den : ℤ) : ℝ) ≠ 0 := by rw [hcast]; exact Rat.cast_ne_zero.mpr hCne
  have h := zG_irrational_abs hq hαne hβne hC0
  rw [hcast] at h
  exact h

/-- **Borwein's Theorem 1, FULLY AXIOM-FREE for `2 ≤ |q|`** (integer base of either sign, every nonzero
rational `c`). The series `∑_{n≥1} 1/(qⁿ + c)` is irrational. **No appeal to `borwein_approximants`** —
all five Borwein lemmas (incl. Lemma 5 non-vanishing for negative base via the sign dichotomy) are
machine-checked. This discharges the `borwein_approximants` axiom entirely. -/
theorem borwein_thm1_abs (q : ℤ) (hq : 2 ≤ |q|) (c : ℚ) (hc0 : c ≠ 0)
    (hcn : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := by
  set C : ℚ := -1 / c with hCdef
  have hCne : C ≠ 0 := by
    rw [hCdef]; intro h; rw [div_eq_zero_iff] at h
    rcases h with h | h
    · norm_num at h
    · exact hc0 h
  have key : (c : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ)))
      = ∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hden : (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0 := hcn n
    rw [hCdef]
    push_cast
    generalize hx : (q : ℝ) ^ (n + 1) = x at hden ⊢
    field_simp
    rw [eq_div_iff (show (c : ℝ) - -x ≠ 0 by rw [sub_neg_eq_add, add_comm]; exact hden)]
    ring
  have hirr : Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) :=
    qharmonic_irrational_abs q hq C hCne
  rw [← key] at hirr
  exact (irrational_ratCast_mul_iff.mp hirr).2

/-- The reduced Erdős–Borwein-type series `∑_{n≥1} 1/(2ⁿ − 1)`, now axiom-free (`q = 2`). -/
theorem irrational_sum_two_pow_sub_one_abs :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) := by
  have h := borwein_thm1_abs 2 (by norm_num) (-1) (by norm_num) (by
    intro n
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    intro hc; push_cast at hc; linarith)
  have hcongr : (fun n : ℕ => (1 : ℝ) / (((2 : ℤ) : ℝ) ^ (n + 1) + ((-1 : ℚ) : ℝ)))
      = fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) := by
    funext n; push_cast; ring_nf
  rwa [hcongr] at h

end LeanGallery.NumberTheory.Erdos1050
