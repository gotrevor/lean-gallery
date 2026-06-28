/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.DELEngine
import LeanGallery.NumberTheory.Erdos482.General.BaseGWeyl
import LeanGallery.NumberTheory.Erdos482.General.Equidistribution
import LeanGallery.NumberTheory.Erdos482.General.DoublingEquidist

/-!
# a.e. equidistribution of the base-`g` orbit `{gⁿ s}`

The base-`g` (`g ≥ 2`) analogue of `DoublingEquidist`.  For almost every real `s`, the orbit
`n ↦ ↑(gⁿ s)` is equidistributed on `ℝ/ℤ` — the base-`g` Borel normality statement, via the
Davenport–Erdős–LeVeque L² method (`BaseGWeyl.baseG_weyl_L2_normalized` + the DEL engine).

* `ae_baseG_weyl_tendsto` / `ae_baseG_weyl_tendsto_real`: per-frequency a.e. vanishing of the base-`g`
  Weyl average (over `[0,1]` resp. all of `ℝ`).
* `ae_baseG_orbit_equidistributed` / `_real`: a.e. equidistribution of the base-`g` orbit.

The general periodicity bridge `ae_of_ae_restrict_Icc01_of_periodic` and the gap-fill /
Weyl-criterion / DEL pieces are all base-agnostic and reused verbatim.
-/

open Filter Finset MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- **Fourier monomial on the base-`g` orbit = the explicit base-`g` Weyl exponential.**
`fourier k (↑(gⁿ·s)) = e(2πi·(k·gⁿ)·s)` on `ℝ/ℤ`.  Base-`g` analogue of `fourier_doubling_eq`. -/
theorem fourier_baseG_eq (g : ℕ) (k : ℤ) (n : ℕ) (s : ℝ) :
    (fourier k) ((((g:ℝ)) ^ n * s : ℝ) : AddCircle (1:ℝ))
      = Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The normalized base-`g` exponential along the squares, `g_j(s) = (1/j²)∑_{n<j²} e(k·gⁿ·s)`. -/
private def gWeylBaseG (g : ℕ) (k : ℤ) (j : ℕ) (s : ℝ) : ℂ :=
  ((j ^ 2 : ℕ) : ℂ)⁻¹ * ∑ n ∈ range (j ^ 2),
    Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s)

/-- **Per-frequency a.e. vanishing of the base-`g` Weyl average.**  For `k ≠ 0`, almost every
`s ∈ [0,1]` has `(1/N)∑_{n<N} e(k·gⁿ·s) → 0`.  (DEL engine along the squares `j²`, mean square `1/j²`
summable, then the gap-fill to all `N`.) -/
theorem ae_baseG_weyl_tendsto {g : ℕ} (hg : 2 ≤ g) (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
  have hcont : ∀ j, Continuous (gWeylBaseG g k j) := by
    intro j
    unfold gWeylBaseG
    refine continuous_const.mul (continuous_finsetSum _ (fun n _ => ?_))
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hmeas : ∀ j, AEStronglyMeasurable (gWeylBaseG g k j) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    fun j => (hcont j).aestronglyMeasurable
  have hL2 : ∀ j, (∫⁻ x in Set.Icc (0:ℝ) 1, ‖gWeylBaseG g k j x‖₊ ^ 2 ∂volume)
      = ENNReal.ofReal (((j ^ 2 : ℕ) : ℝ)⁻¹) := by
    intro j
    rw [l2_bridge (gWeylBaseG g k j) (hcont j)]
    congr 1
    unfold gWeylBaseG
    exact baseG_weyl_L2_normalized hg k hk (j ^ 2)
  have hsum : (∑' j, ∫⁻ x in Set.Icc (0:ℝ) 1, ‖gWeylBaseG g k j x‖₊ ^ 2 ∂volume) ≠ ⊤ := by
    rw [tsum_congr hL2]; exact tsum_ofReal_inv_sq_ne_top
  filter_upwards [ae_tendsto_zero_of_summable_sq (gWeylBaseG g k) hmeas hsum] with s hs
  simp only [gWeylBaseG] at hs
  set a : ℕ → ℂ :=
    fun n => Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s) with ha
  exact cesaro_fill_of_subseq_sq a (fun n => le_of_eq (norm_baseG_exp g k n s)) hs

/-- **Per-frequency a.e. vanishing over all of `ℝ`.**  For `k ≠ 0`, almost every real `s` has
`(1/N)∑_{n<N} e(k·gⁿ·s) → 0`.  Lifts the `[0,1]` form via the periodicity bridge: the sum is `1`-periodic
in `s` (`k·gⁿ ∈ ℤ`). -/
theorem ae_baseG_weyl_tendsto_real {g : ℕ} (hg : 2 ≤ g) (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ (s : ℝ) ∂(volume : Measure ℝ),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
  refine ae_of_ae_restrict_Icc01_of_periodic (fun s => ?_) (ae_baseG_weyl_tendsto hg k hk)
  have hfun : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * ((s + 1 : ℝ))))
      = (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * (s:ℝ))) := by
    funext N
    refine congrArg _ (Finset.sum_congr rfl (fun n _ => ?_))
    rw [show (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * ((s + 1 : ℝ) : ℂ))
          = (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * (s : ℝ))
            + ((k * (g:ℤ) ^ n : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hfun]

/-- **a.e. equidistribution of the base-`g` orbit (`[0,1]`).**  For almost every `s ∈ [0,1]`, the orbit
`n ↦ ↑(gⁿ·s)` is equidistributed on `ℝ/ℤ`.  Intersect the per-frequency vanishing over `k ≠ 0`, then
`weyl_criterion` through the fourier↔exp seam `fourier_baseG_eq`. -/
theorem ae_baseG_orbit_equidistributed {g : ℕ} (hg : 2 ≤ g) :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      IsEquidistributed (fun n => (((g:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
  have hk : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro k
    by_cases hk0 : k = 0
    · exact ae_of_all _ (fun s h => absurd hk0 h)
    · filter_upwards [ae_baseG_weyl_tendsto hg k hk0] with s hs
      exact fun _ => hs
  filter_upwards [hk] with s hsk
  refine weyl_criterion _ (fun k hk0 => ?_)
  exact (hsk k hk0).congr (fun N => by
    congr 1
    exact Finset.sum_congr rfl (fun n _ => (fourier_baseG_eq g k n s).symm))

/-- **a.e. equidistribution of the base-`g` orbit over all of `ℝ`.**  For almost every real `s`, the
orbit `n ↦ ↑(gⁿ·s)` is equidistributed on `ℝ/ℤ`.  Lifts the `[0,1]` form via the periodicity bridge
(`gⁿ ∈ ℤ` killed mod 1).  This is the base-`g` form `DELEngine.ae_comp_mul_left` consumes for the
`s = ξW` scaling toward a.e.-`W`. -/
theorem ae_baseG_orbit_equidistributed_real {g : ℕ} (hg : 2 ≤ g) :
    ∀ᵐ (s : ℝ) ∂(volume : Measure ℝ),
      IsEquidistributed (fun n => (((g:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
  refine ae_of_ae_restrict_Icc01_of_periodic (fun s => ?_) (ae_baseG_orbit_equidistributed hg)
  have hfun : (fun n => (((g:ℝ) ^ n * (s + 1) : ℝ) : AddCircle (1:ℝ)))
      = (fun n => (((g:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
    funext n
    rw [show (g:ℝ) ^ n * (s + 1) = (g:ℝ) ^ n * s + ((g ^ n : ℕ) : ℝ) by push_cast; ring,
      ← AddCircle.coe_fract ((g:ℝ) ^ n * s + ((g ^ n : ℕ) : ℝ)),
      ← AddCircle.coe_fract ((g:ℝ) ^ n * s)]
    congr 1
    exact Int.fract_add_natCast ((g:ℝ) ^ n * s) (g ^ n)
  rw [hfun]

end LeanGallery.NumberTheory.Erdos482.General
