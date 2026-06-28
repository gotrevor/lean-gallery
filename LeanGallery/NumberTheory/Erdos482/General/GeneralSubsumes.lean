/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.GeneralTorusFinish
import LeanGallery.NumberTheory.Erdos482.General.GeneralDefectCheck
import LeanGallery.NumberTheory.Erdos482.General.QuarticFinish

/-!
# The general degree-`d` impossibility subsumes the hand-rolled cubic and quartic

`GeneralTorusFinish.ae_no_dStep_schedule_reads_base_two` is the uniform degree-`d` (`d ≥ 3`)
impossibility.  This file machine-checks that it genuinely **subsumes** the two independently-developed
special cases (`CubicFinish.ae_no_cubic_schedule_reads_base_two`, `d = 3`, and
`QuarticFinish.ae_no_quartic_schedule_reads_base_two`, `d = 4`): each is re-derived here purely as the
general theorem instantiated at the appropriate degree, via the map-level bridges `cubicV3_eq_dStepV` /
`quarticV4_eq_dStepV` (`GeneralDefectCheck`).

This is a genuine **cross-development consistency check**, not a re-proof: the cubic/quartic headlines
were proven by hand-rolled engines; the general headline by the degree-agnostic engine.  That the latter
*implies* the former (kernel-checked) is strong evidence both statements are faithful — a subtle error in
the general window/defect would break this derivation.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

open MeasureTheory

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- `cbrt2 = 2^{1/3} = rrt 3`. -/
theorem cbrt2_eq_rrt : cbrt2 = rrt 3 := by norm_num [cbrt2, rrt]

/-- `qrt2 = 2^{1/4} = rrt 4`. -/
theorem qrt2_eq_rrt : qrt2 = rrt 4 := by norm_num [qrt2, rrt]

/-- **The cubic headline, re-derived from the general one (`d = 3`).**  Identical statement to
`CubicFinish.ae_no_cubic_schedule_reads_base_two`, obtained here purely by instantiating
`ae_no_dStep_schedule_reads_base_two` at `d = 3` on the schedule `cubicSched` and translating through the
map bridge `cubicV3_eq_dStepV`. -/
theorem ae_no_cubic_schedule_reads_base_two_via_general :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c0 c1 c2 : ℝ, ∃ n : ℕ,
      ¬ (cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
          ∨ cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1) := by
  filter_upwards [ae_no_dStep_schedule_reads_base_two 3 (by norm_num)] with W hW
  intro c0 c1 c2
  obtain ⟨n, hn⟩ := hW (cubicSched c0 c1 c2)
  refine ⟨n, fun hcontra => hn ?_⟩
  have hbridge : dStepV (rrt 3) (cubicSched c0 c1 c2) ⌊W * 2 ^ n⌋ 3 - 2 * (⌊W * 2 ^ n⌋ : ℝ)
      = ((cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ : ℤ) : ℝ) := by
    rw [cbrt2_eq_rrt, ← cubicV3_eq_dStepV]; push_cast; ring
  rw [hbridge]
  rcases hcontra with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

/-- **The quartic headline, re-derived from the general one (`d = 4`).**  Identical statement to
`QuarticFinish.ae_no_quartic_schedule_reads_base_two`, obtained by instantiating
`ae_no_dStep_schedule_reads_base_two` at `d = 4` on `quarticSched` and translating through
`quarticV4_eq_dStepV`. -/
theorem ae_no_quartic_schedule_reads_base_two_via_general :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c0 c1 c2 c3 : ℝ, ∃ n : ℕ,
      ¬ (quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
          ∨ quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1) := by
  filter_upwards [ae_no_dStep_schedule_reads_base_two 4 (by norm_num)] with W hW
  intro c0 c1 c2 c3
  obtain ⟨n, hn⟩ := hW (quarticSched c0 c1 c2 c3)
  refine ⟨n, fun hcontra => hn ?_⟩
  have hbridge : dStepV (rrt 4) (quarticSched c0 c1 c2 c3) ⌊W * 2 ^ n⌋ 4 - 2 * (⌊W * 2 ^ n⌋ : ℝ)
      = ((quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ : ℤ) : ℝ) := by
    rw [qrt2_eq_rrt, ← quarticV4_eq_dStepV]; push_cast; ring
  rw [hbridge]
  rcases hcontra with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

end LeanGallery.NumberTheory.Erdos482.General
