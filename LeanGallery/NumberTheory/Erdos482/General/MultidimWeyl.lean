/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Pi
import LeanGallery.NumberTheory.Erdos482.General.Equidistribution

/-!
# Multidimensional Weyl criterion (toward step (c): the `T³` lift of the cubic frontier)

`PENDING_WORK.md ★★` step (c) lifts the a.e. doubling equidistribution to the torus
`UnitAddTorus d = d → ℝ/ℤ`.  mathlib's `Mathlib.Analysis.Fourier.AddCircleMulti` already provides the
torus Fourier characters `mFourier` and torus Stone–Weierstrass (`span_mFourier_closure_eq_top`), so the
multidimensional Weyl criterion is a near-mirror of the 1-D `Equidistribution.weyl_criterion`.

This file builds the genuinely-new crux first: **the torus Fourier integral**
`∫ mFourier n = δ_{n,0}` (`integral_mFourier_eq`), via Fubini over the product measure
(`integral_fintype_prod_volume_eq_prod`) and the 1-D `integral_fourier_eq`.
-/

open Filter Finset MeasureTheory UnitAddTorus AddCircle
open scoped Topology

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- **Integral of a torus Fourier monomial** (product Haar): `∫ mFourier n = 1` if `n = 0` and `0`
otherwise.  By Fubini `∫_{Tᵈ} ∏ᵢ fourier(nᵢ) = ∏ᵢ ∫ fourier(nᵢ) = ∏ᵢ δ_{nᵢ,0} = δ_{n,0}`. -/
theorem integral_mFourier_eq {d : Type*} [Fintype d] (n : d → ℤ) :
    (∫ x : (d → AddCircle (1:ℝ)), mFourier n x ∂volume) = if n = 0 then 1 else 0 := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  have hvh : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have hfac : ∀ k : ℤ, (∫ y : AddCircle (1:ℝ), fourier k y ∂volume) = if k = 0 then 1 else 0 := by
    intro k; rw [hvh]; exact integral_fourier_eq k
  have hprod : ∀ x : (d → AddCircle (1:ℝ)), mFourier n x = ∏ i, fourier (n i) (x i) := fun _ => rfl
  simp_rw [hprod]
  rw [show (∫ x : (d → AddCircle (1:ℝ)), ∏ i, fourier (n i) (x i) ∂volume)
        = ∏ i, ∫ y : AddCircle (1:ℝ), fourier (n i) y ∂volume from
      integral_fintype_prod_volume_eq_prod (fun i y => fourier (n i) y)]
  simp only [hfac]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A sequence on the torus `Tᵈ = d → ℝ/ℤ` is **equidistributed** when the Cesàro averages of every
continuous test function converge to its integral (product Haar = probability measure). -/
def IsEquidistributedTorus {d : Type*} [Fintype d] (x : ℕ → (d → AddCircle (1:ℝ))) : Prop :=
  ∀ f : C(d → AddCircle (1:ℝ), ℂ),
    Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, f (x n)) atTop (𝓝 (∫ y, f y ∂volume))

/-- **Multidimensional Weyl criterion.**  If every nonzero torus character has vanishing Cesàro mean
(`(1/N)∑_{n<N} mFourier k (xₙ) → 0` for all `k ≠ 0`), then `x` is equidistributed on `Tᵈ`.  Exact
mirror of the 1-D `weyl_criterion`: monomials (`mFourier_zero`/`integral_mFourier_eq`) → Fourier span
(`Submodule.span_induction`) → all continuous `f` by uniform approximation (`span_mFourier_closure_eq_top`
+ `norm_cesaro_le`).  Step (c) piece 2 of the cubic frontier. -/
theorem weyl_criterion_torus {d : Type*} [Fintype d] (x : ℕ → (d → AddCircle (1:ℝ)))
    (h : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (mFourier k) (x n)) atTop (𝓝 0)) :
    IsEquidistributedTorus x := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  have hvh : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by rw [hvh]; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (d → AddCircle (1:ℝ))) := by
    rw [volume_pi]; infer_instance
  have hInt : ∀ f : C(d → AddCircle (1:ℝ), ℂ), Integrable (fun y => f y) volume := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Step 1: every torus monomial.
  have hmono : ∀ k : d → ℤ, Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (mFourier k) (x n)) atTop
      (𝓝 (∫ y : (d → AddCircle (1:ℝ)), (mFourier k) y ∂volume)) := by
    intro k
    rw [integral_mFourier_eq]
    by_cases hk : k = 0
    · subst hk
      simp only [mFourier_zero, ContinuousMap.one_apply]
      refine Tendsto.congr' ?_ (show Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1) from tendsto_const_nhds)
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hNc]
    · rw [if_neg hk]; exact h k hk
  -- Step 2: the Fourier span (linearity).
  have hspan : ∀ f ∈ Submodule.span ℂ (Set.range (mFourier (d := d))),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, f (x n)) atTop (𝓝 (∫ y, f y ∂volume)) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem g hg => obtain ⟨k, rfl⟩ := hg; exact hmono k
    | zero =>
      simp only [ContinuousMap.zero_apply, Finset.sum_const_zero, mul_zero, integral_zero]
      exact tendsto_const_nhds
    | add g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      have hintadd : (∫ y, (g₁ + g₂) y ∂volume)
          = (∫ y, g₁ y ∂volume) + ∫ y, g₂ y ∂volume := by
        simp only [ContinuousMap.add_apply]; exact integral_add (hInt g₁) (hInt g₂)
      have havg : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (g₁ + g₂) (x n))
          = fun N : ℕ => ((N:ℂ)⁻¹ * ∑ n ∈ range N, g₁ (x n))
              + ((N:ℂ)⁻¹ * ∑ n ∈ range N, g₂ (x n)) := by
        funext N; simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
      rw [hintadd, havg]; exact ih₁.add ih₂
    | smul c g hg ih =>
      have hintsmul : (∫ y, (c • g) y ∂volume) = c * ∫ y, g y ∂volume := by
        simp only [ContinuousMap.smul_apply]; rw [integral_smul, smul_eq_mul]
      have havg : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (c • g) (x n))
          = fun N : ℕ => c * ((N:ℂ)⁻¹ * ∑ n ∈ range N, g (x n)) := by
        funext N; simp only [ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]; ring_nf
      rw [hintsmul, havg]; exact ih.const_mul c
  -- Step 3: density.
  have hdense : Dense ((Submodule.span ℂ (Set.range (mFourier (d := d)))) :
      Set C(d → AddCircle (1:ℝ), ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_mFourier_closure_eq_top
  intro f
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hdense f) (ε / 3) (by positivity)
  have hfg_norm : ‖f - g‖ < ε / 3 := by rwa [dist_eq_norm] at hfg
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hspan g hg) (ε / 3) (by positivity)
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hi : dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k)) ((n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k)) ≤ ‖f - g‖ := by
    rw [dist_eq_norm]
    have hd : (n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k) - (n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k)
        = (n:ℂ)⁻¹ * ∑ k ∈ range n, (f - g) (x k) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]; simp only [ContinuousMap.sub_apply]
    rw [hd]; exact norm_cesaro_le x (f - g) hn1
  have hiii : dist (∫ y, g y ∂volume) (∫ y, f y ∂volume) ≤ ‖f - g‖ := by
    rw [dist_eq_norm]
    have hsub : (∫ y, g y ∂volume) - ∫ y, f y ∂volume = ∫ y, (g - f) y ∂volume := by
      rw [← integral_sub (hInt g) (hInt f)]; simp only [ContinuousMap.sub_apply]
    rw [hsub]
    calc ‖∫ y, (g - f) y ∂volume‖
        ≤ ‖g - f‖ * (volume (Set.univ : Set (d → AddCircle (1:ℝ)))).toReal :=
          norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall (fun y => (g - f).norm_coe_le_norm y))
      _ = ‖f - g‖ := by rw [measure_univ, ENNReal.toReal_one, mul_one, norm_sub_rev]
  calc dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k)) (∫ y, f y ∂volume)
      ≤ dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k)) ((n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k))
        + dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k)) (∫ y, g y ∂volume)
        + dist (∫ y, g y ∂volume) (∫ y, f y ∂volume) := dist_triangle4 _ _ _ _
    _ < ε := by have := hN₀ n hn₀; linarith [hi, hiii, hfg_norm]

end LeanGallery.NumberTheory.Erdos482.General
