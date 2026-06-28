/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.DELEngine
import LeanGallery.NumberTheory.Erdos482.General.WeylDoubling
import LeanGallery.NumberTheory.Erdos482.General.Equidistribution

/-!
# Step (b) assembly: a.e. equidistribution of the doubling orbit `{2ⁿ s}`

`PENDING_WORK.md ★★` step (b).  Combining the bricks of this lap —
* `WeylDoubling.doubling_weyl_L2_normalized` (`∫₀¹‖(1/N)∑_{n<N} e(k2ⁿ·)‖² = 1/N`),
* `DELEngine.l2_bridge` + `DELEngine.ae_tendsto_zero_of_summable_sq` (the DEL L² engine),
* `Equidistribution.tsum_ofReal_inv_sq_ne_top` (p-series finiteness),
* `Equidistribution.cesaro_fill_of_subseq_sq` (gap-fill `j²` → all `N`),
* `Equidistribution.weyl_criterion` + `fourier_doubling_eq` (Weyl criterion + the fourier↔exp seam),

we obtain: **for almost every `s ∈ [0,1]`, the doubling orbit `n ↦ ↑(2ⁿ s)` is equidistributed on
`ℝ/ℤ`** (`ae_doubling_orbit_equidistributed`).  This is the unconditional a.e. input that the cubic
self-referential frontier's path #2 lifts to `T³` (step (c)) to break the two-plane defect confinement.
-/

open Filter Finset MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- The normalized doubling exponential along the squares, `g_j(s) = (1/j²)∑_{n<j²} e(k·2ⁿ·s)`. -/
private def gWeyl (k : ℤ) (j : ℕ) (s : ℝ) : ℂ :=
  ((j ^ 2 : ℕ) : ℂ)⁻¹ * ∑ n ∈ range (j ^ 2),
    Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)

/-- Each doubling exponential `e(k·2ⁿ·s)` has unit modulus. -/
theorem norm_doubling_exp (k : ℤ) (n : ℕ) (s : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)‖ = 1 := by
  rw [show (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * (s:ℂ))
        = ((2 * Real.pi * (k * 2 ^ n) * s : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Per-frequency a.e. vanishing of the doubling Weyl average.**  For `k ≠ 0`, almost every
`s ∈ [0,1]` has `(1/N)∑_{n<N} e(k·2ⁿ·s) → 0`.  (DEL engine along the squares `j²` — mean square `1/j²`
is summable — then the gap-fill to all `N`.) -/
theorem ae_doubling_weyl_tendsto (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
  have hcont : ∀ j, Continuous (gWeyl k j) := by
    intro j
    unfold gWeyl
    refine continuous_const.mul (continuous_finsetSum _ (fun n _ => ?_))
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hmeas : ∀ j, AEStronglyMeasurable (gWeyl k j) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    fun j => (hcont j).aestronglyMeasurable
  have hL2 : ∀ j, (∫⁻ x in Set.Icc (0:ℝ) 1, ‖gWeyl k j x‖₊ ^ 2 ∂volume)
      = ENNReal.ofReal (((j ^ 2 : ℕ) : ℝ)⁻¹) := by
    intro j
    rw [l2_bridge (gWeyl k j) (hcont j)]
    congr 1
    unfold gWeyl
    exact doubling_weyl_L2_normalized k hk (j ^ 2)
  have hsum : (∑' j, ∫⁻ x in Set.Icc (0:ℝ) 1, ‖gWeyl k j x‖₊ ^ 2 ∂volume) ≠ ⊤ := by
    rw [tsum_congr hL2]; exact tsum_ofReal_inv_sq_ne_top
  filter_upwards [ae_tendsto_zero_of_summable_sq (gWeyl k) hmeas hsum] with s hs
  simp only [gWeyl] at hs
  set a : ℕ → ℂ :=
    fun n => Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s) with ha
  exact cesaro_fill_of_subseq_sq a (fun n => le_of_eq (norm_doubling_exp k n s)) hs

/-- **Step (b) — a.e. equidistribution of the doubling orbit.**  For almost every `s ∈ [0,1]`, the
doubling orbit `n ↦ ↑(2ⁿ·s)` is equidistributed on `ℝ/ℤ`.  Intersect the per-frequency a.e. vanishing
(`ae_doubling_weyl_tendsto`) over the countably many `k ≠ 0` (`ae_all_iff`), then apply Weyl's criterion
(`weyl_criterion`) through the fourier↔exp seam (`fourier_doubling_eq`).  This is the unconditional a.e.
input the cubic frontier's path #2 lifts to `T³` (step (c)). -/
theorem ae_doubling_orbit_equidistributed :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      IsEquidistributed (fun n => (((2:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
  have hk : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro k
    by_cases hk0 : k = 0
    · exact ae_of_all _ (fun s h => absurd hk0 h)
    · filter_upwards [ae_doubling_weyl_tendsto k hk0] with s hs
      exact fun _ => hs
  filter_upwards [hk] with s hsk
  refine weyl_criterion _ (fun k hk0 => ?_)
  exact (hsk k hk0).congr (fun N => by
    congr 1
    exact Finset.sum_congr rfl (fun n _ => (fourier_doubling_eq k n s).symm))

/-- **Periodicity bridge: a.e.-`[0,1]` ⟹ a.e.-`ℝ` for a unit-periodic predicate.**  If `P` is invariant
under the unit shift (`P (s+1) ↔ P s`) and holds for a.e. `s ∈ [0,1]`, then it holds for a.e. `s ∈ ℝ`
(full Lebesgue `volume`).  The bad set `{¬P}` is `ℤ`-invariant, hence a countable union of integer
translates of `{¬P} ∩ [0,1]`, each null by translation-invariance of `volume` (`measure_preimage_add_right`).
This lifts the `[0,1]`-restricted a.e. doubling equidistribution to all of `ℝ`, as `DELEngine.ae_comp_mul_left`
(the scaling transfer `s = ξW`) requires the unrestricted `volume`. -/
theorem ae_of_ae_restrict_Icc01_of_periodic {P : ℝ → Prop}
    (hper : ∀ s : ℝ, P (s + 1) ↔ P s)
    (h : ∀ᵐ s ∂(volume.restrict (Set.Icc (0:ℝ) 1)), P s) :
    ∀ᵐ s ∂(volume : Measure ℝ), P s := by
  -- `P` is invariant under all natural, hence all integer, shifts.
  have hPn : ∀ (n : ℕ) (s : ℝ), P (s + n) ↔ P s := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => intro s
                   have e : (s + ((m + 1 : ℕ) : ℝ)) = (s + (m:ℝ)) + 1 := by push_cast; ring
                   rw [e, hper, ih]
  have hPnegn : ∀ (n : ℕ) (s : ℝ), P (s - n) ↔ P s := by
    intro n s
    rw [← hPn n (s - n), show (s - (n:ℝ)) + n = s by ring]
  have hinv : ∀ (k : ℤ) (s : ℝ), P (s + (k:ℝ)) ↔ P s := by
    intro k s
    obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
    · rw [Int.cast_natCast]; exact hPn n s
    · rw [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]; exact hPnegn n s
  rw [ae_iff]
  have h0 : volume ({s : ℝ | ¬ P s} ∩ Set.Icc (0:ℝ) 1) = 0 := by
    have := ae_iff.mp h
    rwa [Measure.restrict_apply' measurableSet_Icc] at this
  have cover : {s : ℝ | ¬ P s} ⊆ ⋃ k : ℤ, ({s : ℝ | ¬ P s} ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1)) := by
    intro x hx
    rw [Set.mem_iUnion]
    refine ⟨⌊x⌋, hx, Int.floor_le x, ?_⟩
    have := Int.lt_floor_add_one x; linarith
  have hpiece : ∀ k : ℤ,
      volume ({s : ℝ | ¬ P s} ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1)) = 0 := by
    intro k
    have hset : ({s : ℝ | ¬ P s} ∩ Set.Icc (k:ℝ) ((k:ℝ) + 1))
        = (fun x => x + (-(k:ℝ))) ⁻¹' ({s : ℝ | ¬ P s} ∩ Set.Icc (0:ℝ) 1) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨hx, hl, hr⟩
        refine ⟨?_, by linarith, by linarith⟩
        rw [show (x + -(k:ℝ)) = x + ((-k : ℤ):ℝ) by push_cast; ring, hinv]; exact hx
      · rintro ⟨hx, hl, hr⟩
        rw [show (x + -(k:ℝ)) = x + ((-k : ℤ):ℝ) by push_cast; ring, hinv] at hx
        exact ⟨hx, by linarith, by linarith⟩
    rw [hset, measure_preimage_add_right]; exact h0
  exact measure_mono_null cover (measure_iUnion_null hpiece)

/-- **Per-frequency a.e. vanishing of the doubling Weyl average over all of `ℝ`.**  For `k ≠ 0`, almost
every real `s` (full Lebesgue `volume`) has `(1/N)∑_{n<N} e(k·2ⁿ·s) → 0`.  Lifts the `[0,1]`-restricted
`ae_doubling_weyl_tendsto` via the periodicity bridge: the doubling Weyl sum is `1`-periodic in `s`
(`e(k·2ⁿ·(s+1)) = e(k·2ⁿ·s)`, as `k·2ⁿ ∈ ℤ`).  This is the form `DELEngine.ae_comp_mul_left` scales to
`s = ξ·W` in the `T³` lift. -/
theorem ae_doubling_weyl_tendsto_real (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ (s : ℝ) ∂(volume : Measure ℝ),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
  refine ae_of_ae_restrict_Icc01_of_periodic (fun s => ?_) (ae_doubling_weyl_tendsto k hk)
  have hfun : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * ((s + 1 : ℝ))))
      = (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * (s:ℝ))) := by
    funext N
    refine congrArg _ (Finset.sum_congr rfl (fun n _ => ?_))
    rw [show (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * ((s + 1 : ℝ) : ℂ))
          = (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * (s : ℝ))
            + ((k * (2:ℤ) ^ n : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hfun]

/-- **Step (b) over all of `ℝ`.**  For almost every real `s` (full Lebesgue `volume`), the doubling orbit
`n ↦ ↑(2ⁿ·s)` is equidistributed on `ℝ/ℤ`.  Lifts `ae_doubling_orbit_equidistributed` (a.e.-`[0,1]`) to
`ℝ` via the periodicity bridge: the orbit `↑(2ⁿ·s)` is `1`-periodic in `s` (`2ⁿ ∈ ℤ` is killed mod 1).
This is the form `DELEngine.ae_comp_mul_left` consumes for the `s = ξW` scaling toward a.e.-`W`. -/
theorem ae_doubling_orbit_equidistributed_real :
    ∀ᵐ (s : ℝ) ∂(volume : Measure ℝ),
      IsEquidistributed (fun n => (((2:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
  refine ae_of_ae_restrict_Icc01_of_periodic (fun s => ?_) ae_doubling_orbit_equidistributed
  have hfun : (fun n => (((2:ℝ) ^ n * (s + 1) : ℝ) : AddCircle (1:ℝ)))
      = (fun n => (((2:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
    funext n
    rw [show (2:ℝ) ^ n * (s + 1) = (2:ℝ) ^ n * s + ((2 ^ n : ℕ) : ℝ) by push_cast; ring,
      ← AddCircle.coe_fract ((2:ℝ) ^ n * s + ((2 ^ n : ℕ) : ℝ)),
      ← AddCircle.coe_fract ((2:ℝ) ^ n * s)]
    congr 1
    exact Int.fract_add_natCast ((2:ℝ) ^ n * s) (2 ^ n)
  rw [hfun]

end LeanGallery.NumberTheory.Erdos482.General
