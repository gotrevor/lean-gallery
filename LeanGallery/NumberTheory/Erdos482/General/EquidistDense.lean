/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanGallery.NumberTheory.Erdos482.General.MultidimWeyl

/-!
# Equidistribution ⇒ dense orbit (step (c) piece 3 of the cubic frontier)

`PENDING_WORK.md ★★` step (c) piece 3.  The genuinely-new general fact (mathlib-absent): on a compact
Hausdorff Borel space with a finite, open-positive measure `μ`, if the Cesàro averages of every
continuous test function converge to its integral, then the orbit `{xₙ}` is **dense**.

This is the bridge that lets the a.e.-`W` `T³` equidistribution (assembled from the doubling
equidistribution via the Weyl reduction) contradict the **measure-zero two-plane defect confinement**
of the cubic self-referential map (`CubicDefect`).

**Provenance.** The general lemma `isEquidistributed_dense` (and its bump helper) were proved by
Aristotle (job `3e68d32f`), verified here in-kernel + `#print axioms`-clean.  Specialized below to the
torus `Tᵈ` (`isEquidistributedTorus_dense`) — the form the cubic frontier consumes.
-/

open MeasureTheory Filter Topology Finset UnitAddTorus

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- A continuous bump function: on a compact Hausdorff space, for a point `p` in an open set `U`
there is a continuous `f : X → ℝ` with values in `[0,1]`, equal to `1` at `p`, and vanishing
outside `U`.  (Urysohn for the disjoint closed sets `Uᶜ` and `{p}`.) -/
lemma bump_exists {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U) {p : X} (hp : p ∈ U) :
    ∃ f : C(X, ℝ), f p = 1 ∧ (∀ y, f y ∈ Set.Icc (0:ℝ) 1) ∧ (∀ y, y ∉ U → f y = 0) := by
  have := @exists_continuous_zero_one_of_isClosed
  obtain ⟨f, hf⟩ := this (show IsClosed (Uᶜ) by exact hU.isClosed_compl)
    (show IsClosed {p} by exact isClosed_singleton) (by simpa)
  exact ⟨f, hf.2.1 rfl, hf.2.2, fun y hy => hf.1 hy⟩

/-- **Equidistribution ⇒ dense orbit (general).**  On a compact Hausdorff Borel space `X` with a finite,
open-positive measure `μ`, if the Cesàro averages of every continuous `ℂ`-valued test function converge
to its integral, then `Set.range x` is dense.  (Contradiction route: a non-dense range misses a nonempty
open `U`; a bump supported in `U` averages to a constant `0`, but has strictly positive integral.) -/
theorem isEquidistributed_dense {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {x : ℕ → X}
    (hx : ∀ f : C(X, ℂ),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)) atTop (𝓝 (∫ y, f y ∂μ))) :
    Dense (Set.range x) := by
  rw [dense_iff_inter_open]
  by_contra h
  push Not at h
  obtain ⟨U, hUopen, ⟨p, hpU⟩, hUempty⟩ := h
  have hrange : ∀ n, x n ∉ U := by
    intro n hn
    exact (Set.not_nonempty_iff_eq_empty.mpr hUempty) ⟨x n, hn, ⟨n, rfl⟩⟩
  obtain ⟨f, hfp, hfIcc, hf0⟩ := bump_exists hUopen hpU
  set g : C(X, ℂ) := ContinuousMap.comp ⟨Complex.ofReal, Complex.continuous_ofReal⟩ f with hg
  have havg : ∀ N : ℕ, (N:ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (x n) = 0 := by
    intro N
    have : ∀ n ∈ Finset.range N, g (x n) = 0 := by
      intro n _
      simp only [hg, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [hf0 (x n) (hrange n)]; simp
    rw [Finset.sum_eq_zero this, mul_zero]
  have hlim0 : Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (x n)) atTop (𝓝 0) := by
    have hconst : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (x n)) = fun _ => 0 :=
      funext havg
    rw [hconst]; exact tendsto_const_nhds
  have hInt0 : ∫ y, g y ∂μ = 0 := tendsto_nhds_unique (hx g) hlim0
  have hReal : ∫ y, f y ∂μ > 0 := by
    have hcs : HasCompactSupport (f : X → ℝ) := HasCompactSupport.of_compactSpace _
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := μ) (f := (f : X → ℝ)) (x := p) f.continuous hcs
      (fun y => (hfIcc y).1) (by rw [hfp]; norm_num)
  have hcast : ∫ y, g y ∂μ = ((∫ y, f y ∂μ : ℝ) : ℂ) := by
    simp only [hg, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    rw [integral_complex_ofReal]
  rw [hcast] at hInt0
  have : (∫ y, f y ∂μ : ℝ) = 0 := by exact_mod_cast hInt0
  linarith [hReal]

/-- **A continuous function confined on a dense orbit to a closed set is confined everywhere on an open
set.**  If `Set.range x` is dense, `f` is continuous on an open `U`, `S` is closed, and `f (x n) ∈ S`
whenever `x n ∈ U`, then `f y ∈ S` for *all* `y ∈ U`.  (Relative density: `U ∩ range x` is dense in `U`,
and `f` maps its relative closure into the closed `S`.)  The clean contrapositive form of the cubic
finish: a defect that is continuous and exceeds the digit window somewhere on an open box cannot be
confined to that window along the dense orbit.  Provenance: Aristotle `291bb0fb`, verified
in-kernel + axiom-clean. -/
theorem dense_continuousOn_image_subset {X : Type*} [TopologicalSpace X]
    {x : ℕ → X} (hx : Dense (Set.range x))
    {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : ContinuousOn f U)
    {S : Set ℝ} (hS : IsClosed S)
    (hmem : ∀ n, x n ∈ U → f (x n) ∈ S) :
    ∀ y ∈ U, f y ∈ S := by
  intro y hy
  have h_closure : y ∈ closure (U ∩ Set.range x) := by
    rw [mem_closure_iff]
    intro o ho hyo
    rcases hx.inter_nhds_nonempty (IsOpen.mem_nhds (hU.inter ho) ⟨hy, hyo⟩) with ⟨z, hz, hz'⟩
    exact ⟨z, by aesop⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at h_closure
  have h_tendsto : Filter.Tendsto f (nhdsWithin y (U ∩ Set.range x)) (nhds (f y)) :=
    (hf.continuousWithinAt hy).mono_left (nhdsWithin_mono _ Set.inter_subset_left)
  refine hS.mem_of_tendsto h_tendsto (Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => ?_)
  obtain ⟨hzU, m, rfl⟩ := hz
  exact hmem m hzU

/-- **A dense orbit realizes values above any threshold strictly below a continuity-point value.**
If `Set.range x` is dense, `f` is continuous at `p`, and `c < f p`, then some orbit point `x n` has
`c < f (x n)`.  (The superlevel set `{y | c < f y}` is a neighborhood of `p`; density meets it.)  The
threshold tool for the cubic finish: at a continuity point of the defect where the value exceeds the
digit window, the dense orbit realizes a defect outside the window — contradicting confinement. -/
theorem exists_lt_of_dense_continuousAt {X : Type*} [TopologicalSpace X] {x : ℕ → X}
    (hx : Dense (Set.range x)) {f : X → ℝ} {p : X} (hf : ContinuousAt f p) {c : ℝ} (hc : c < f p) :
    ∃ n, c < f (x n) := by
  have hnhd : f ⁻¹' Set.Ioi c ∈ nhds p := hf (Ioi_mem_nhds hc)
  obtain ⟨y, hy_pre, m, rfl⟩ := mem_closure_iff_nhds.mp (hx p) _ hnhd
  exact ⟨m, hy_pre⟩

/-- Symmetric form: a dense orbit realizes values strictly below any threshold above a continuity-point
value.  (`{y | f y < c}` is a neighborhood of `p`.) -/
theorem exists_gt_of_dense_continuousAt {X : Type*} [TopologicalSpace X] {x : ℕ → X}
    (hx : Dense (Set.range x)) {f : X → ℝ} {p : X} (hf : ContinuousAt f p) {c : ℝ} (hc : f p < c) :
    ∃ n, f (x n) < c := by
  have hnhd : f ⁻¹' Set.Iio c ∈ nhds p := hf (Iio_mem_nhds hc)
  obtain ⟨y, hy_pre, m, rfl⟩ := mem_closure_iff_nhds.mp (hx p) _ hnhd
  exact ⟨m, hy_pre⟩

/-- **`IsEquidistributedTorus` ⇒ dense orbit on `Tᵈ`.**  Specializes `isEquidistributed_dense` to the
torus `d → ℝ/ℤ` with the product Haar (`volume`), which is a finite open-positive measure.  Step (c)
piece 3 of the cubic frontier: the a.e.-`W` `T³` equidistribution yields a dense orbit, contradicting
the measure-zero two-plane defect confinement. -/
theorem isEquidistributedTorus_dense {d : Type*} [Fintype d] {x : ℕ → (d → AddCircle (1:ℝ))}
    (hx : IsEquidistributedTorus x) : Dense (Set.range x) := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  haveI : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (d → AddCircle (1:ℝ))) := by
    rw [volume_pi]; infer_instance
  exact isEquidistributed_dense volume hx

end LeanGallery.NumberTheory.Erdos482.General
