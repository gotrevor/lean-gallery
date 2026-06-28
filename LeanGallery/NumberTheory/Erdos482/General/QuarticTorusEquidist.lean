/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.DoublingEquidist
import LeanGallery.NumberTheory.Erdos482.General.MultidimWeyl
import LeanGallery.NumberTheory.Erdos482.General.EquidistDense
import LeanGallery.NumberTheory.Erdos482.General.DELEngine
import LeanGallery.NumberTheory.Erdos482.General.QuarticDefect

/-!
# a.e.-`W` equidistribution of the quartic `T⁴` orbit `2ⁿ(W, αW, α²W, α³W)`

Degree-4 analogue of `CubicTorusEquidist`.  For `α = 2^{1/4}` and almost every real `W`, the orbit
`n ↦ (2ⁿW, 2ⁿαW, 2ⁿα²W, 2ⁿα³W) mod 1 ∈ T⁴` is equidistributed, hence dense.  The Weyl reduction is
identical to the cubic: the torus character along the orbit is `e(2πi·2ⁿ·ξW)` with
`ξ = m₀+m₁α+m₂α²+m₃α³`, nonzero for `m ≠ 0` by `quartic_lin_indep_int`; this is the frequency-1 doubling
Weyl sum at `s = ξW`, killed a.e. by the doubling equidistribution backbone scaled via `ae_comp_mul_left`.
-/

open Filter Finset MeasureTheory UnitAddTorus AddCircle
open scoped Topology

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- The frequency scalar `ξ = m₀ + m₁α + m₂α² + m₃α³` of a torus character `m : Fin 4 → ℤ`. -/
def quarticXi (m : Fin 4 → ℤ) : ℝ :=
  (m 0 : ℝ) + (m 1) * qrt2 + (m 2) * qrt2 ^ 2 + (m 3) * qrt2 ^ 3

/-- The quartic `T⁴` orbit at seed `W`: `n ↦ (2ⁿ·W, 2ⁿ·αW, 2ⁿ·α²W, 2ⁿ·α³W) mod 1`. -/
def quarticTorusOrbit (W : ℝ) : ℕ → (Fin 4 → AddCircle (1:ℝ)) :=
  fun n i => (((2:ℝ) ^ n * qrt2 ^ (i:ℕ) * W : ℝ) : AddCircle (1:ℝ))

/-- **The torus character along the orbit is a frequency-1 doubling exponential.** -/
lemma quartic_mFourier_orbit_eq (m : Fin 4 → ℤ) (W : ℝ) (n : ℕ) :
    mFourier m (quarticTorusOrbit W n)
      = Complex.exp (2 * ↑Real.pi * Complex.I * (((1:ℤ) * (2:ℤ) ^ n : ℤ) : ℂ)
          * ((quarticXi m * W : ℝ) : ℂ)) := by
  have hprod : mFourier m (quarticTorusOrbit W n)
      = ∏ i : Fin 4, fourier (m i) (quarticTorusOrbit W n i) := rfl
  rw [hprod]
  simp_rw [quarticTorusOrbit, fourier_coe_apply]
  rw [← Complex.exp_sum, Fin.sum_univ_four]
  congr 1
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [quarticXi, v0, v1, v2, v3, pow_zero, pow_one]
  push_cast
  ring

/-- The frequency scalar is nonzero for any nonzero `m` (ℤ-independence of `{1, α, α², α³}`). -/
lemma quarticXi_ne_zero {m : Fin 4 → ℤ} (hm : m ≠ 0) : quarticXi m ≠ 0 := by
  intro h
  have hlin := quartic_lin_indep_int (m 0) (m 1) (m 2) (m 3) (by rw [quarticXi] at h; exact h)
  exact hm (by funext i; fin_cases i <;> simp [hlin.1, hlin.2.1, hlin.2.2.1, hlin.2.2.2])

/-- **Per-character a.e.-`W` vanishing.** -/
lemma ae_W_quartic_mFourier_orbit_tendsto (m : Fin 4 → ℤ) (hm : m ≠ 0) :
    ∀ᵐ W ∂(volume : Measure ℝ),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (quarticTorusOrbit W n))
        atTop (𝓝 0) := by
  have h := ae_comp_mul_left (quarticXi_ne_zero hm) (ae_doubling_weyl_tendsto_real 1 one_ne_zero)
  filter_upwards [h] with W hW
  refine hW.congr (fun N => ?_)
  refine congrArg _ (Finset.sum_congr rfl (fun n _ => ?_))
  exact (quartic_mFourier_orbit_eq m W n).symm

/-- **Final assembly — a.e.-`W` `T⁴` equidistribution.** -/
theorem ae_W_quartic_torus_orbit_equidistributed :
    ∀ᵐ W ∂(volume : Measure ℝ), IsEquidistributedTorus (quarticTorusOrbit W) := by
  have key : ∀ᵐ W ∂(volume : Measure ℝ), ∀ m : Fin 4 → ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (quarticTorusOrbit W n))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : m = 0
    · exact ae_of_all _ (fun W h => absurd hm h)
    · filter_upwards [ae_W_quartic_mFourier_orbit_tendsto m hm] with W hW
      exact fun _ => hW
  filter_upwards [key] with W hW
  exact weyl_criterion_torus _ hW

/-- **The quartic `T⁴` orbit is dense for a.e. `W`.** -/
theorem ae_W_quartic_torus_orbit_dense :
    ∀ᵐ W ∂(volume : Measure ℝ), Dense (Set.range (quarticTorusOrbit W)) := by
  filter_upwards [ae_W_quartic_torus_orbit_equidistributed] with W hW
  exact isEquidistributedTorus_dense hW

end LeanGallery.NumberTheory.Erdos482.General
