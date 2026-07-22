/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Bases

/-!
# A.e. density of the doubling-map orbit on `ℝ/ℤ`

The cubic self-referential frontier (`General/CubicDefect.lean`) reduces to a statement about the
**doubling map** `x ↦ 2x` on the circle: the block orbit `uₙ = ⌊W·2ⁿ⌋` makes the first internal-floor
error a doubling-map orbit `≈ {αW·2ⁿ}`, so the residual obstruction is whether that orbit avoids a
constrained set (the two-plane confinement of `cubic_orbit_defect_confined`).  For a *specific* `W` this
is the open "is this number base-2 normal" question; but for **almost every** `W` the orbit cannot avoid
any nonempty open set, which already rules out the measure-zero confinement.

This file proves that unconditional a.e. statement, using only the ergodicity of `×2` on `AddCircle`
(`AddCircle.ergodic_nsmul`, already in mathlib) — **no pointwise Birkhoff theorem is needed**:

* `ae_orbit_mem_of_isOpen`: for any nonempty open `U`, a.e. `x` has its forward doubling-orbit enter
  `U`.  (Heart: the "ever hits `U`" set `A = ⋃ₙ T⁻ⁿU` satisfies `T⁻¹A ⊆ A` and `μ A ≥ μ U > 0`, so
  ergodicity forces `A` conull.)
* `ae_dense_orbit_doubling`: a.e. `x` has a **dense** doubling-orbit (intersect the previous over a
  countable basis).

These are the ergodic core of attack-path #2 (the a.e.-`W` unconditional cubic route) in
`PENDING_WORK.md`.  Density (not full equidistribution) already contradicts the two-plane confinement,
so this is the right tool — the remaining gap to a complete a.e.-`W` cubic theorem is the *skew-product*
step relating the joint internal-floor coordinates `(f₁,f₂,f₃)` to this single doubling orbit.
-/

open MeasureTheory Filter Set TopologicalSpace

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- **For any nonempty open `U`, almost every point's forward doubling-orbit enters `U`.**  `T x = 2•x`
on `ℝ/ℤ` is ergodic, the set `A = {x | ∃ n, Tⁿ x ∈ U}` of points ever hitting `U` satisfies
`T⁻¹A ⊆ A` and `μ A ≥ μ U > 0`, so by `Ergodic.ae_empty_or_univ_of_preimage_ae_le` it is conull. -/
theorem ae_orbit_mem_of_isOpen (U : Set (AddCircle (1:ℝ))) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∀ᵐ x : AddCircle (1:ℝ) ∂volume, ∃ n : ℕ, (fun y : AddCircle (1:ℝ) => (2:ℕ) • y)^[n] x ∈ U := by
  set T : AddCircle (1:ℝ) → AddCircle (1:ℝ) := fun y => (2:ℕ) • y with hT
  have herg : Ergodic T volume := AddCircle.ergodic_nsmul (by norm_num)
  have hcontT : Continuous T := by fun_prop
  set A : Set (AddCircle (1:ℝ)) := {x | ∃ n : ℕ, T^[n] x ∈ U} with hAdef
  have hAeq : A = ⋃ n : ℕ, T^[n] ⁻¹' U := by ext x; simp [hAdef]
  have hA : MeasurableSet A := by
    rw [hAeq]
    exact MeasurableSet.iUnion (fun n => (hcontT.iterate n).measurable hU.measurableSet)
  have hpre : T ⁻¹' A ⊆ A := by
    rintro x ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  have hposU : 0 < volume U := hU.measure_pos volume hUne
  have hUA : U ⊆ A := fun x hx => ⟨0, by simpa using hx⟩
  have hposA : 0 < volume A := lt_of_lt_of_le hposU (measure_mono hUA)
  have hle : T ⁻¹' A ≤ᵐ[volume] A := LE.le.eventuallyLE hpre
  have huniv : A =ᵐ[volume] univ := by
    rcases herg.ae_empty_or_univ_of_preimage_ae_le hA.nullMeasurableSet hle with h | h
    · exact absurd (by rw [measure_congr h]; simp : volume A = 0) (ne_of_gt hposA)
    · exact h
  filter_upwards [huniv] with x hx
  exact hx.mpr (mem_univ x)

/-- **Almost every point has a dense doubling-orbit on `ℝ/ℤ`.**  Intersect `ae_orbit_mem_of_isOpen`
over a countable topological basis: a.e. `x` meets every nonempty basic open, hence has dense orbit.
This is the unconditional a.e. input behind the cubic self-referential frontier's path #2 (it already
contradicts any measure-zero confinement of the orbit), and uses only `×2`-ergodicity — not Birkhoff. -/
theorem ae_dense_orbit_doubling :
    ∀ᵐ x : AddCircle (1:ℝ) ∂volume,
      Dense (Set.range (fun n : ℕ => (fun y : AddCircle (1:ℝ) => (2:ℕ) • y)^[n] x)) := by
  set T : AddCircle (1:ℝ) → AddCircle (1:ℝ) := fun y => (2:ℕ) • y with hT
  have hbasis := isBasis_countableBasis (AddCircle (1:ℝ))
  have hcount := countable_countableBasis (AddCircle (1:ℝ))
  have key : ∀ᵐ x ∂volume, ∀ U ∈ countableBasis (AddCircle (1:ℝ)),
      (U ∩ Set.range (fun n : ℕ => T^[n] x)).Nonempty := by
    rw [ae_ball_iff hcount]
    intro U hU
    have hUne : U.Nonempty :=
      nonempty_iff_ne_empty.mpr (fun h => empty_notMem_countableBasis _ (h ▸ hU))
    have hUopen : IsOpen U := hbasis.isOpen hU
    filter_upwards [ae_orbit_mem_of_isOpen U hUopen hUne] with x hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨T^[n] x, hn, ⟨n, rfl⟩⟩
  filter_upwards [key] with x hx
  exact hbasis.dense_iff.mpr (fun U hU _ => hx U hU)

/-- The projection `π : ℝ → ℝ/ℤ` intertwines the real doubling `t ↦ 2t` with the circle doubling
`y ↦ 2•y`: `π(2ⁿ·t) = (y ↦ 2•y)^[n] (π t)`. -/
theorem doubling_iterate_eq (t : ℝ) (n : ℕ) :
    ((2 ^ n * t : ℝ) : AddCircle (1:ℝ))
      = (fun y : AddCircle (1:ℝ) => (2:ℕ) • y)^[n] ((t : AddCircle (1:ℝ))) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, ← QuotientAddGroup.mk_nsmul]
    congr 1
    simp [nsmul_eq_mul]
    ring

/-- **ℝ-line form: a.e. real `t` has a dense base-2 orbit `{2ⁿ·t mod 1}`.**  Pull
`ae_dense_orbit_doubling` back along the measure-preserving projection `ℝ → ℝ/ℤ` (the bad set is a
countable union of pieces, each a measure-preserving preimage of the null circle-bad set).  This is the
real-line input the cubic frontier's path #2 uses: with `t = αW`, `{2ⁿαW mod 1}` is dense for a.e. `W`.
(Density only — the path #2 *equidistribution* on the measure-zero curve `(W,αW,α²W)` needs the Weyl/DEL
mean square `WeylDoubling.doubling_weyl_L2_mean`, not just this.) -/
theorem ae_fract_dense_real :
    ∀ᵐ t : ℝ ∂volume,
      Dense (Set.range (fun n : ℕ => ((2 ^ n * t : ℝ) : AddCircle (1:ℝ)))) := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  set Nbad : Set (AddCircle (1:ℝ)) :=
    {x | ¬ Dense (Set.range (fun n : ℕ => (fun y : AddCircle (1:ℝ) => (2:ℕ) • y)^[n] x))} with hN
  have hNnull : volume Nbad = 0 := ae_iff.mp ae_dense_orbit_doubling
  have hrange : ∀ t : ℝ,
      (Set.range (fun n : ℕ => ((2 ^ n * t : ℝ) : AddCircle (1:ℝ))))
        = Set.range (fun n : ℕ => (fun y : AddCircle (1:ℝ) => (2:ℕ) • y)^[n] ((t : AddCircle (1:ℝ)))) :=
    fun t => congrArg Set.range (funext fun n => doubling_iterate_eq t n)
  rw [ae_iff]
  have hpre :
      {t : ℝ | ¬ Dense (Set.range (fun n : ℕ => ((2 ^ n * t : ℝ) : AddCircle (1:ℝ))))}
        = ((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' Nbad := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_preimage, hN, hrange t]
  rw [hpre]
  have cover : ((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' Nbad
      ⊆ ⋃ k : ℤ, (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' Nbad ∩ Set.Ioc (k:ℝ) ((k:ℝ) + 1)) := by
    intro x hx
    rw [Set.mem_iUnion]
    refine ⟨⌈x⌉ - 1, hx, ?_⟩
    constructor
    · push_cast; have := Int.ceil_lt_add_one x; linarith
    · push_cast; have := Int.le_ceil x; linarith
  have hpiece : ∀ k : ℤ,
      volume (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' Nbad ∩ Set.Ioc (k:ℝ) ((k:ℝ) + 1)) = 0 := by
    intro k
    have hnull := (AddCircle.measurePreserving_mk (1:ℝ) (k:ℝ)).quasiMeasurePreserving.preimage_null hNnull
    rwa [Measure.restrict_apply' measurableSet_Ioc] at hnull
  exact measure_mono_null cover (measure_iUnion_null hpiece)

end LeanGallery.NumberTheory.Erdos482.General
