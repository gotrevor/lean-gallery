/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.DoublingEquidist
import LeanGallery.NumberTheory.Erdos482.General.MultidimWeyl
import LeanGallery.NumberTheory.Erdos482.General.EquidistDense
import LeanGallery.NumberTheory.Erdos482.General.DELEngine
import LeanGallery.NumberTheory.Erdos482.General.CubicDefect

/-!
# Final assembly: a.e.-`W` equidistribution of the cubic `T³` orbit `2ⁿ(W, αW, α²W)`

`PENDING_WORK.md ★★` step (c), the assembly that lifts the a.e. doubling equidistribution to the torus.
For `α = 2^{1/3}` and almost every real `W`, the orbit
`n ↦ (2ⁿ·W mod 1, 2ⁿ·αW mod 1, 2ⁿ·α²W mod 1) ∈ T³` is **equidistributed**, hence **dense**.

**The Weyl reduction.**  For a nonzero frequency `m : Fin 3 → ℤ`, the torus character along the orbit is
`mFourier m (orbitₙ) = e(2πi · 2ⁿ · ξ·W)` with `ξ := m₀ + m₁α + m₂α²`.  By `cubic_lin_indep_int`
(`{1,α,α²}` ℤ-independent), `m ≠ 0 ⇒ ξ ≠ 0`, so this is the **frequency-1 doubling Weyl sum** at the
scaled seed `s = ξ·W`.  `ae_doubling_weyl_tendsto_real 1` (a.e.-`ℝ` vanishing) scaled by
`ae_comp_mul_left` (the `s = ξW` substitution, `ξ ≠ 0`) gives per-`m` a.e.-`W` vanishing; intersecting
over the countably many `m ≠ 0` (`ae_all_iff`) and applying `weyl_criterion_torus` yields the a.e.-`W`
`T³` equidistribution.  `isEquidistributedTorus_dense` then gives the dense orbit — the input the
cubic-defect confinement (`CubicDefect.cubic_orbit_defect_confined`, a measure-zero two-plane set) must
contradict for the unconditional a.e.-`W` cubic impossibility.
-/

open Filter Finset MeasureTheory UnitAddTorus AddCircle
open scoped Topology

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- `α = 2^{1/3}` (the cubic multiplier; `α³ = 2`). -/
abbrev cbrt2 : ℝ := (2:ℝ) ^ ((1:ℝ) / 3)

/-- The frequency scalar `ξ = m₀ + m₁α + m₂α²` of a torus character `m : Fin 3 → ℤ`.  Nonzero for
`m ≠ 0` by `cubic_lin_indep_int`. -/
def cubicXi (m : Fin 3 → ℤ) : ℝ := (m 0 : ℝ) + (m 1) * cbrt2 + (m 2) * cbrt2 ^ 2

/-- The cubic `T³` orbit at seed `W`: `n ↦ (2ⁿ·W, 2ⁿ·αW, 2ⁿ·α²W) mod 1`. -/
def cubicTorusOrbit (W : ℝ) : ℕ → (Fin 3 → AddCircle (1:ℝ)) :=
  fun n i => (((2:ℝ) ^ n * cbrt2 ^ (i:ℕ) * W : ℝ) : AddCircle (1:ℝ))

/-- **The torus character along the orbit is a frequency-1 doubling exponential.**
`mFourier m (orbitₙ) = e(2πi · 2ⁿ · (ξ·W))`, `ξ = m₀ + m₁α + m₂α²`.  (`mFourier` is a product of
1-D `fourier` characters; `fourier_coe_apply` turns each into an exponential, and the product collapses
the exponents into `2ⁿ·W·∑ᵢ mᵢαⁱ = 2ⁿ·ξW`.) -/
lemma mFourier_orbit_eq (m : Fin 3 → ℤ) (W : ℝ) (n : ℕ) :
    mFourier m (cubicTorusOrbit W n)
      = Complex.exp (2 * ↑Real.pi * Complex.I * (((1:ℤ) * (2:ℤ) ^ n : ℤ) : ℂ)
          * ((cubicXi m * W : ℝ) : ℂ)) := by
  have hprod : mFourier m (cubicTorusOrbit W n)
      = ∏ i : Fin 3, fourier (m i) (cubicTorusOrbit W n i) := rfl
  rw [hprod]
  simp_rw [cubicTorusOrbit, fourier_coe_apply]
  rw [← Complex.exp_sum, Fin.sum_univ_three]
  congr 1
  simp only [cubicXi, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  push_cast
  ring

/-- The frequency scalar is nonzero for any nonzero `m` (ℤ-independence of `{1, α, α²}`). -/
lemma cubicXi_ne_zero {m : Fin 3 → ℤ} (hm : m ≠ 0) : cubicXi m ≠ 0 := by
  intro h
  have hlin := cubic_lin_indep_int (m 0) (m 1) (m 2) (by rw [cubicXi] at h; exact h)
  exact hm (by funext i; fin_cases i <;> simp [hlin.1, hlin.2.1, hlin.2.2])

/-- **Per-character a.e.-`W` vanishing.**  For `m ≠ 0`, almost every `W` has
`(1/N)∑_{n<N} mFourier m (orbitₙ) → 0`.  (The character is the frequency-1 doubling sum at `s = ξW`;
`ae_doubling_weyl_tendsto_real 1` scaled by `ae_comp_mul_left` with `c = ξ ≠ 0`.) -/
lemma ae_W_mFourier_orbit_tendsto (m : Fin 3 → ℤ) (hm : m ≠ 0) :
    ∀ᵐ W ∂(volume : Measure ℝ),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (cubicTorusOrbit W n))
        atTop (𝓝 0) := by
  have h := ae_comp_mul_left (cubicXi_ne_zero hm) (ae_doubling_weyl_tendsto_real 1 one_ne_zero)
  filter_upwards [h] with W hW
  refine hW.congr (fun N => ?_)
  refine congrArg _ (Finset.sum_congr rfl (fun n _ => ?_))
  exact (mFourier_orbit_eq m W n).symm

/-- **Final assembly — a.e.-`W` `T³` equidistribution.**  For almost every `W`, the cubic torus orbit
`n ↦ (2ⁿW, 2ⁿαW, 2ⁿα²W) mod 1` is equidistributed on `T³`.  Intersect the per-character vanishing
(`ae_W_mFourier_orbit_tendsto`) over the countably many `m ≠ 0` (`ae_all_iff`), then `weyl_criterion_torus`. -/
theorem ae_W_cubic_torus_orbit_equidistributed :
    ∀ᵐ W ∂(volume : Measure ℝ), IsEquidistributedTorus (cubicTorusOrbit W) := by
  have key : ∀ᵐ W ∂(volume : Measure ℝ), ∀ m : Fin 3 → ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (cubicTorusOrbit W n))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : m = 0
    · exact ae_of_all _ (fun W h => absurd hm h)
    · filter_upwards [ae_W_mFourier_orbit_tendsto m hm] with W hW
      exact fun _ => hW
  filter_upwards [key] with W hW
  exact weyl_criterion_torus _ hW

/-- **The cubic `T³` orbit is dense for a.e. `W`.**  Equidistribution ⇒ dense
(`isEquidistributedTorus_dense`).  This is the geometric input that contradicts the measure-zero
two-plane defect confinement of the cubic self-referential map (`CubicDefect`). -/
theorem ae_W_cubic_torus_orbit_dense :
    ∀ᵐ W ∂(volume : Measure ℝ), Dense (Set.range (cubicTorusOrbit W)) := by
  filter_upwards [ae_W_cubic_torus_orbit_equidistributed] with W hW
  exact isEquidistributedTorus_dense hW

end LeanGallery.NumberTheory.Erdos482.General
