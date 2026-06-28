/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.QuarticDefectLink
import LeanGallery.NumberTheory.Erdos482.General.QuarticTorusEquidist
import LeanGallery.NumberTheory.Erdos482.General.CubicFinish

/-!
# The quartic geometric crux: the partial defect leaves every digit window

Degree-4 analogue of `CubicFinish.cubicGpd_exceeds_window`.  For any schedule `(c₀,c₁,c₂)` and any
constant `C`, there is an interior non-jump point `(r₁,r₂,r₃,r₄) ∈ (0,1)⁴` where the three-floor partial
defect `quarticGpd = α³fA + α²fB + α·fC` (with `fA,fB,fC ∈ (0,1)`) leaves the width-2 window `(C−2, C]`.
The range `(0, α³+α²+α)` has width `α³+α²+α > 3 > 2` (as `α = 2^{1/4} > 1`), so no window of length 2
contains it.  Realization reuses `CubicFinish.fract_shift_realize`: fix `r₁ = 1/2`, solve `r₂,r₃,r₄` for
the three prescribed fractional parts.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real Filter Topology MeasureTheory UnitAddTorus AddCircle

/-- **The quartic partial defect leaves every window (general `α`).**  For `1 < α`, `α⁴ = 2`, any
schedule `(c₀,c₁,c₂)` and any `C`, there is `(r₁,r₂,r₃,r₄) ∈ (0,1)⁴` with the three inner `fract`
arguments non-integers and `quarticGpd α c0 c1 c2 r1 r2 r3 r4 ∉ (C−2, C]`. -/
theorem quarticGpd_exceeds_window_general (α c0 c1 c2 : ℝ) (hα : 1 < α) (hα4 : α ^ 4 = 2) (C : ℝ) :
    ∃ r1 r2 r3 r4 : ℝ, 0 < r1 ∧ r1 < 1 ∧ 0 < r2 ∧ r2 < 1 ∧ 0 < r3 ∧ r3 < 1 ∧ 0 < r4 ∧ r4 < 1
      ∧ (r2 - α * r1 + α * c0 ≠ (⌊r2 - α * r1 + α * c0⌋ : ℤ))
      ∧ (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1⌋ : ℤ))
      ∧ (r4 - α ^ 3 * r1 - α ^ 2 * Int.fract (r2 - α * r1 + α * c0)
            - α * Int.fract (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0)
                + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2
          ≠ (⌊r4 - α ^ 3 * r1 - α ^ 2 * Int.fract (r2 - α * r1 + α * c0)
                - α * Int.fract (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0)
                    + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2⌋ : ℤ))
      ∧ (quarticGpd α c0 c1 c2 r1 r2 r3 r4 < C - 2 ∨ C < quarticGpd α c0 c1 c2 r1 r2 r3 r4) := by
  have hαpos : 0 < α := by linarith
  have hα2 : 1 < α ^ 2 := by nlinarith
  have hα3 : 1 < α ^ 3 := by nlinarith
  have hsum : 3 < α ^ 3 + α ^ 2 + α := by nlinarith
  have hsumpos : 0 < α ^ 3 + α ^ 2 + α := by linarith
  have fne : ∀ x : ℝ, Int.fract x ≠ 0 → x ≠ ((⌊x⌋ : ℤ) : ℝ) := by
    intro x hx h; apply hx; have hsf := Int.self_sub_floor x; linarith
  set K1 := α * c0 - α * (1 / 2) with hK1
  by_cases hC : C < α ^ 3 + α ^ 2 + α
  · -- value > C; choose fA, fB, fC near 1
    set lo := max 0 (C / (α ^ 3 + α ^ 2 + α)) with hlodef
    have hlo0 : 0 ≤ lo := le_max_left _ _
    have hlolt : lo < 1 := by
      apply max_lt
      · norm_num
      · rw [div_lt_one hsumpos]; exact hC
    have hloge : C / (α ^ 3 + α ^ 2 + α) ≤ lo := le_max_right _ _
    have hmul : C ≤ lo * (α ^ 3 + α ^ 2 + α) := (div_le_iff₀ hsumpos).mp hloge
    obtain ⟨r2, hr2pos, hr2lt, hfAlo, hfAhi⟩ := fract_shift_realize K1 lo 1 hlo0 (le_refl 1) hlolt
    set fA := Int.fract (r2 + K1) with hfA
    set K2 := α ^ 2 * c0 + α * c1 - α ^ 2 * (1 / 2) - α * fA with hK2
    obtain ⟨r3, hr3pos, hr3lt, hfBlo, hfBhi⟩ := fract_shift_realize K2 lo 1 hlo0 (le_refl 1) hlolt
    set fB := Int.fract (r3 + K2) with hfB
    set K3 := α ^ 3 * c0 + α ^ 2 * c1 + α * c2 - α ^ 3 * (1 / 2) - α ^ 2 * fA - α * fB with hK3
    obtain ⟨r4, hr4pos, hr4lt, hfClo, hfChi⟩ := fract_shift_realize K3 lo 1 hlo0 (le_refl 1) hlolt
    set fC := Int.fract (r4 + K3) with hfC
    have e1 : Int.fract (r2 - α * (1 / 2) + α * c0) = fA := by rw [hfA, hK1]; congr 1; ring
    have hval : quarticGpd α c0 c1 c2 (1 / 2) r2 r3 r4 = α ^ 3 * fA + α ^ 2 * fB + α * fC := by
      unfold quarticGpd
      rw [e1, show r3 - α ^ 2 * (1 / 2 : ℝ) - α * fA + α ^ 2 * c0 + α * c1 = r3 + K2 by rw [hK2]; ring,
        ← hfB, show r4 - α ^ 3 * (1 / 2 : ℝ) - α ^ 2 * fA - α * fB + α ^ 3 * c0 + α ^ 2 * c1 + α * c2
          = r4 + K3 by rw [hK3]; ring, ← hfC]
    refine ⟨1 / 2, r2, r3, r4, by norm_num, by norm_num, hr2pos, hr2lt, hr3pos, hr3lt, hr4pos, hr4lt,
      ?_, ?_, ?_, ?_⟩
    · apply fne; rw [e1]; linarith
    · apply fne
      rw [show r3 - α ^ 2 * (1 / 2 : ℝ) - α * Int.fract (r2 - α * (1 / 2) + α * c0) + α ^ 2 * c0
            + α * c1 = r3 + K2 by rw [e1, hK2]; ring, ← hfB]
      linarith
    · apply fne
      rw [e1, show r4 - α ^ 3 * (1 / 2 : ℝ) - α ^ 2 * fA
            - α * Int.fract (r3 - α ^ 2 * (1 / 2) - α * fA + α ^ 2 * c0 + α * c1)
            + α ^ 3 * c0 + α ^ 2 * c1 + α * c2 = r4 + K3 by
          rw [show r3 - α ^ 2 * (1 / 2 : ℝ) - α * fA + α ^ 2 * c0 + α * c1 = r3 + K2 by rw [hK2]; ring,
            ← hfB, hK3]; ring, ← hfC]
      linarith
    · right
      rw [hval]
      nlinarith [mul_pos (show (0:ℝ) < α ^ 3 by positivity) (sub_pos.mpr hfAlo),
        mul_pos (show (0:ℝ) < α ^ 2 by positivity) (sub_pos.mpr hfBlo),
        mul_pos hαpos (sub_pos.mpr hfClo), hmul]
  · -- value < C - 2; choose fA, fB, fC near 0
    push Not at hC
    have hC2 : 0 < C - 2 := by linarith
    set hi := min (1 / 2) ((C - 2) / (α ^ 3 + α ^ 2 + α)) with hidef
    have hipos : 0 < hi := by
      apply lt_min
      · norm_num
      · positivity
    have hile : hi ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
    have hile2 : hi ≤ (C - 2) / (α ^ 3 + α ^ 2 + α) := min_le_right _ _
    have hmul2 : hi * (α ^ 3 + α ^ 2 + α) ≤ C - 2 := (le_div_iff₀ hsumpos).mp hile2
    obtain ⟨r2, hr2pos, hr2lt, hfAlo, hfAhi⟩ := fract_shift_realize K1 0 hi (le_refl 0) hile hipos
    set fA := Int.fract (r2 + K1) with hfA
    set K2 := α ^ 2 * c0 + α * c1 - α ^ 2 * (1 / 2) - α * fA with hK2
    obtain ⟨r3, hr3pos, hr3lt, hfBlo, hfBhi⟩ := fract_shift_realize K2 0 hi (le_refl 0) hile hipos
    set fB := Int.fract (r3 + K2) with hfB
    set K3 := α ^ 3 * c0 + α ^ 2 * c1 + α * c2 - α ^ 3 * (1 / 2) - α ^ 2 * fA - α * fB with hK3
    obtain ⟨r4, hr4pos, hr4lt, hfClo, hfChi⟩ := fract_shift_realize K3 0 hi (le_refl 0) hile hipos
    set fC := Int.fract (r4 + K3) with hfC
    have e1 : Int.fract (r2 - α * (1 / 2) + α * c0) = fA := by rw [hfA, hK1]; congr 1; ring
    have hval : quarticGpd α c0 c1 c2 (1 / 2) r2 r3 r4 = α ^ 3 * fA + α ^ 2 * fB + α * fC := by
      unfold quarticGpd
      rw [e1, show r3 - α ^ 2 * (1 / 2 : ℝ) - α * fA + α ^ 2 * c0 + α * c1 = r3 + K2 by rw [hK2]; ring,
        ← hfB, show r4 - α ^ 3 * (1 / 2 : ℝ) - α ^ 2 * fA - α * fB + α ^ 3 * c0 + α ^ 2 * c1 + α * c2
          = r4 + K3 by rw [hK3]; ring, ← hfC]
    refine ⟨1 / 2, r2, r3, r4, by norm_num, by norm_num, hr2pos, hr2lt, hr3pos, hr3lt, hr4pos, hr4lt,
      ?_, ?_, ?_, ?_⟩
    · apply fne; rw [e1]; linarith
    · apply fne
      rw [show r3 - α ^ 2 * (1 / 2 : ℝ) - α * Int.fract (r2 - α * (1 / 2) + α * c0) + α ^ 2 * c0
            + α * c1 = r3 + K2 by rw [e1, hK2]; ring, ← hfB]
      linarith
    · apply fne
      rw [e1, show r4 - α ^ 3 * (1 / 2 : ℝ) - α ^ 2 * fA
            - α * Int.fract (r3 - α ^ 2 * (1 / 2) - α * fA + α ^ 2 * c0 + α * c1)
            + α ^ 3 * c0 + α ^ 2 * c1 + α * c2 = r4 + K3 by
          rw [show r3 - α ^ 2 * (1 / 2 : ℝ) - α * fA + α ^ 2 * c0 + α * c1 = r3 + K2 by rw [hK2]; ring,
            ← hfB, hK3]; ring, ← hfC]
      linarith
    · left
      rw [hval]
      nlinarith [mul_pos (show (0:ℝ) < α ^ 3 by positivity) (sub_pos.mpr hfAhi),
        mul_pos (show (0:ℝ) < α ^ 2 by positivity) (sub_pos.mpr hfBhi),
        mul_pos hαpos (sub_pos.mpr hfChi), hmul2]

/-- The geometric crux specialized to `α = qrt2` and the quartic window `C = 2c₀+α³c₁+α²c₂+αc₃`. -/
theorem quarticGpd_exceeds_window (c0 c1 c2 c3 : ℝ) :
    ∃ r1 r2 r3 r4 : ℝ, (0 < r1 ∧ r1 < 1) ∧ (0 < r2 ∧ r2 < 1) ∧ (0 < r3 ∧ r3 < 1)
      ∧ (0 < r4 ∧ r4 < 1)
      ∧ (r2 - qrt2 * r1 + qrt2 * c0 ≠ (⌊r2 - qrt2 * r1 + qrt2 * c0⌋ : ℤ))
      ∧ (r3 - qrt2 ^ 2 * r1 - qrt2 * Int.fract (r2 - qrt2 * r1 + qrt2 * c0) + qrt2 ^ 2 * c0 + qrt2 * c1
          ≠ (⌊r3 - qrt2 ^ 2 * r1 - qrt2 * Int.fract (r2 - qrt2 * r1 + qrt2 * c0)
                + qrt2 ^ 2 * c0 + qrt2 * c1⌋ : ℤ))
      ∧ (r4 - qrt2 ^ 3 * r1 - qrt2 ^ 2 * Int.fract (r2 - qrt2 * r1 + qrt2 * c0)
            - qrt2 * Int.fract (r3 - qrt2 ^ 2 * r1 - qrt2 * Int.fract (r2 - qrt2 * r1 + qrt2 * c0)
                + qrt2 ^ 2 * c0 + qrt2 * c1) + qrt2 ^ 3 * c0 + qrt2 ^ 2 * c1 + qrt2 * c2
          ≠ (⌊r4 - qrt2 ^ 3 * r1 - qrt2 ^ 2 * Int.fract (r2 - qrt2 * r1 + qrt2 * c0)
                - qrt2 * Int.fract (r3 - qrt2 ^ 2 * r1 - qrt2 * Int.fract (r2 - qrt2 * r1 + qrt2 * c0)
                    + qrt2 ^ 2 * c0 + qrt2 * c1) + qrt2 ^ 3 * c0 + qrt2 ^ 2 * c1 + qrt2 * c2⌋ : ℤ))
      ∧ ((2 * c0 + qrt2 ^ 3 * c1 + qrt2 ^ 2 * c2 + qrt2 * c3) < quarticGpd qrt2 c0 c1 c2 r1 r2 r3 r4
          ∨ quarticGpd qrt2 c0 c1 c2 r1 r2 r3 r4 < (2 * c0 + qrt2 ^ 3 * c1 + qrt2 ^ 2 * c2 + qrt2 * c3) - 2) := by
  obtain ⟨r1, r2, r3, r4, h1p, h1l, h2p, h2l, h3p, h3l, h4p, h4l, hA, hB, hC, hval⟩ :=
    quarticGpd_exceeds_window_general qrt2 c0 c1 c2 one_lt_qrt2 qrt2_quartic
      (2 * c0 + qrt2 ^ 3 * c1 + qrt2 ^ 2 * c2 + qrt2 * c3)
  exact ⟨r1, r2, r3, r4, ⟨h1p, h1l⟩, ⟨h2p, h2l⟩, ⟨h3p, h3l⟩, ⟨h4p, h4l⟩, hA, hB, hC, hval.symm⟩

/-- The quartic partial defect as a function on `T⁴`. -/
noncomputable def quarticGpdTorus (α c0 c1 c2 : ℝ) (a : Fin 4 → AddCircle (1:ℝ)) : ℝ :=
  quarticGpd α c0 c1 c2 (torusRep (a 0)) (torusRep (a 1)) (torusRep (a 2)) (torusRep (a 3))

/-- `quarticGpdTorus` reads the partial defect along the quartic orbit. -/
theorem quarticGpdTorus_orbit (c0 c1 c2 c3 W : ℝ) (n : ℕ) :
    quarticGpdTorus qrt2 c0 c1 c2 (quarticTorusOrbit W n)
      = quarticPartialDefect qrt2 c0 c1 c2 c3 (⌊W * 2 ^ n⌋) := by
  rw [quarticPartialDefect_eq_Gpd]
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [quarticGpdTorus, quarticTorusOrbit, torusRep_coe, v0, v1, v2, v3,
    pow_zero, pow_one, mul_one]
  congr 1 <;> · congr 1 ; ring

/-- **`quarticGpdTorus` is continuous at any torus point with nonzero coordinates whose three inner
`fract` arguments are non-integers.** -/
theorem continuousAt_quarticGpdTorus (α c0 c1 c2 : ℝ) {p : Fin 4 → AddCircle (1:ℝ)}
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (h2 : p 2 ≠ 0) (h3 : p 3 ≠ 0)
    (hA : torusRep (p 1) - α * torusRep (p 0) + α * c0
            ≠ (⌊torusRep (p 1) - α * torusRep (p 0) + α * c0⌋ : ℤ))
    (hB : torusRep (p 2) - α ^ 2 * torusRep (p 0)
            - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊torusRep (p 2) - α ^ 2 * torusRep (p 0)
                - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0)
                + α ^ 2 * c0 + α * c1⌋ : ℤ))
    (hC : torusRep (p 3) - α ^ 3 * torusRep (p 0)
            - α ^ 2 * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0)
            - α * Int.fract (torusRep (p 2) - α ^ 2 * torusRep (p 0)
                - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0) + α ^ 2 * c0 + α * c1)
            + α ^ 3 * c0 + α ^ 2 * c1 + α * c2
          ≠ (⌊torusRep (p 3) - α ^ 3 * torusRep (p 0)
                - α ^ 2 * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0)
                - α * Int.fract (torusRep (p 2) - α ^ 2 * torusRep (p 0)
                    - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0)
                    + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2⌋ : ℤ)) :
    ContinuousAt (quarticGpdTorus α c0 c1 c2) p := by
  have hΦ : ContinuousAt
      (fun a : Fin 4 → AddCircle (1:ℝ) =>
        (torusRep (a 0), torusRep (a 1), torusRep (a 2), torusRep (a 3))) p := by
    refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_))
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 4 → AddCircle (1:ℝ) => a 0)
        (continuousAt_torusRep h0) (continuous_apply 0).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 4 → AddCircle (1:ℝ) => a 1)
        (continuousAt_torusRep h1) (continuous_apply 1).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 4 → AddCircle (1:ℝ) => a 2)
        (continuousAt_torusRep h2) (continuous_apply 2).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 4 → AddCircle (1:ℝ) => a 3)
        (continuousAt_torusRep h3) (continuous_apply 3).continuousAt
  have hG : ContinuousAt
      (fun q : ℝ × ℝ × ℝ × ℝ => quarticGpd α c0 c1 c2 q.1 q.2.1 q.2.2.1 q.2.2.2)
      (torusRep (p 0), torusRep (p 1), torusRep (p 2), torusRep (p 3)) :=
    continuousAt_quarticGpd α c0 c1 c2
      (torusRep (p 0), torusRep (p 1), torusRep (p 2), torusRep (p 3)) hA hB hC
  exact ContinuousAt.comp
    (g := fun q : ℝ × ℝ × ℝ × ℝ => quarticGpd α c0 c1 c2 q.1 q.2.1 q.2.2.1 q.2.2.2)
    (f := fun a : Fin 4 → AddCircle (1:ℝ) =>
      (torusRep (a 0), torusRep (a 1), torusRep (a 2), torusRep (a 3)))
    hG hΦ

/-- **Unconditional a.e.-`W` quartic impossibility, uniform over all schedules.**  For `α = 2^{1/4}`
and almost every real `W`, **no** 4-periodic offset schedule `(c₀,c₁,c₂,c₃)` makes the four-step quartic
floor map read `W`'s base-2 digits: for every schedule there is a step `n` with
`quarticV4(⌊W·2ⁿ⌋) − 2⌊W·2ⁿ⌋ ∉ {0,1}`.  Degree-4 analogue of `ae_no_cubic_schedule_reads_base_two`,
built on the same schedule-independent `T⁴` orbit-density set. -/
theorem ae_no_quartic_schedule_reads_base_two :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c0 c1 c2 c3 : ℝ, ∃ n : ℕ,
      ¬ (quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
          ∨ quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1) := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  filter_upwards [ae_W_quartic_torus_orbit_dense] with W hdense
  intro c0 c1 c2 c3
  by_contra hcon
  push Not at hcon
  set C : ℝ := 2 * c0 + qrt2 ^ 3 * c1 + qrt2 ^ 2 * c2 + qrt2 * c3 with hC
  have hwin : ∀ n : ℕ, C - 2 < quarticGpdTorus qrt2 c0 c1 c2 (quarticTorusOrbit W n)
      ∧ quarticGpdTorus qrt2 c0 c1 c2 (quarticTorusOrbit W n) ≤ C := by
    intro n
    have hw := quartic_partial_defect_mem_window qrt2 c0 c1 c2 c3 qrt2_quartic ⌊W * 2 ^ n⌋ (hcon n)
    rw [quarticGpdTorus_orbit (c3 := c3)]
    exact hw
  obtain ⟨r1, r2, r3, r4, hr1, hr2, hr3, hr4, hA, hB, hC', hval⟩ := quarticGpd_exceeds_window c0 c1 c2 c3
  set P : Fin 4 → AddCircle (1:ℝ) := ![(r1 : AddCircle (1:ℝ)), (r2 : AddCircle (1:ℝ)), (r3 : AddCircle (1:ℝ)), (r4 : AddCircle (1:ℝ))] with hP
  have hP0 : P 0 = (r1 : AddCircle (1:ℝ)) := rfl
  have hP1 : P 1 = (r2 : AddCircle (1:ℝ)) := rfl
  have hP2 : P 2 = (r3 : AddCircle (1:ℝ)) := rfl
  have hP3 : P 3 = (r4 : AddCircle (1:ℝ)) := rfl
  have hrep0 : torusRep (P 0) = r1 := by rw [hP0, torusRep_coe, Int.fract_eq_self.mpr ⟨hr1.1.le, hr1.2⟩]
  have hrep1 : torusRep (P 1) = r2 := by rw [hP1, torusRep_coe, Int.fract_eq_self.mpr ⟨hr2.1.le, hr2.2⟩]
  have hrep2 : torusRep (P 2) = r3 := by rw [hP2, torusRep_coe, Int.fract_eq_self.mpr ⟨hr3.1.le, hr3.2⟩]
  have hrep3 : torusRep (P 3) = r4 := by rw [hP3, torusRep_coe, Int.fract_eq_self.mpr ⟨hr4.1.le, hr4.2⟩]
  have hne0 : P 0 ≠ 0 := by
    rw [hP0, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr1.1.le, hr1.2⟩]; exact ne_of_gt hr1.1
  have hne1 : P 1 ≠ 0 := by
    rw [hP1, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr2.1.le, hr2.2⟩]; exact ne_of_gt hr2.1
  have hne2 : P 2 ≠ 0 := by
    rw [hP2, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr3.1.le, hr3.2⟩]; exact ne_of_gt hr3.1
  have hne3 : P 3 ≠ 0 := by
    rw [hP3, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr4.1.le, hr4.2⟩]; exact ne_of_gt hr4.1
  have hcont : ContinuousAt (quarticGpdTorus qrt2 c0 c1 c2) P :=
    continuousAt_quarticGpdTorus qrt2 c0 c1 c2 hne0 hne1 hne2 hne3
      (by rw [hrep0, hrep1]; exact hA) (by rw [hrep0, hrep1, hrep2]; exact hB)
      (by rw [hrep0, hrep1, hrep2, hrep3]; exact hC')
  have hPval : quarticGpdTorus qrt2 c0 c1 c2 P = quarticGpd qrt2 c0 c1 c2 r1 r2 r3 r4 := by
    simp only [quarticGpdTorus, hrep0, hrep1, hrep2, hrep3]
  rcases hval with hgt | hlt
  · have hc : C < quarticGpdTorus qrt2 c0 c1 c2 P := by rw [hPval]; exact hgt
    obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont (c := C) hc
    exact absurd (hwin n).2 (not_le.mpr hn)
  · have hc : quarticGpdTorus qrt2 c0 c1 c2 P < C - 2 := by rw [hPval]; exact hlt
    obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont (c := C - 2) hc
    exact absurd (hwin n).1 (not_lt.mpr hn.le)

/-- **`W` is quartic-digit-representable** if some 4-periodic schedule digit-represents it (every
`quarticV4(⌊W·2ⁿ⌋) − 2⌊W·2ⁿ⌋ ∈ {0,1}`). -/
def QuarticDigitRepresentable (W : ℝ) : Prop :=
  ∃ c0 c1 c2 c3 : ℝ, ∀ n : ℕ,
    quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
      ∨ quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1

/-- **Almost no real is quartic-digit-representable.** -/
theorem ae_not_quarticDigitRepresentable :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ QuarticDigitRepresentable W := by
  filter_upwards [ae_no_quartic_schedule_reads_base_two] with W hW
  rintro ⟨c0, c1, c2, c3, hall⟩
  obtain ⟨n, hn⟩ := hW c0 c1 c2 c3
  exact hn (hall n)

/-- **The quartic map correctly reads `W`'s base-2 digits** if some schedule sends each binary block
`⌊W·2ⁿ⌋` to the next, `quarticV4(⌊W·2ⁿ⌋) = ⌊W·2ⁿ⁺¹⌋`. -/
def QuarticReadsBaseTwo (W : ℝ) : Prop :=
  ∃ c0 c1 c2 c3 : ℝ, ∀ n : ℕ, quarticV4 qrt2 c0 c1 c2 c3 ⌊W * 2 ^ n⌋ = ⌊W * 2 ^ (n + 1)⌋

/-- **The quartic four-step map computes no real's base-2 doubling, for almost every `W`.** -/
theorem ae_not_quarticReadsBaseTwo :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ QuarticReadsBaseTwo W := by
  filter_upwards [ae_not_quarticDigitRepresentable] with W hW
  rintro ⟨c0, c1, c2, c3, hread⟩
  refine hW ⟨c0, c1, c2, c3, fun n => ?_⟩
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hdouble : ⌊W * 2 ^ (n + 1)⌋ = ⌊2 * (W * 2 ^ n)⌋ := by rw [hpow]; ring_nf
  rw [hread n, hdouble]
  rcases floor_two_mul_sub_mem (W * 2 ^ n) with h | h
  · left; omega
  · right; omega

end LeanGallery.NumberTheory.Erdos482.General
