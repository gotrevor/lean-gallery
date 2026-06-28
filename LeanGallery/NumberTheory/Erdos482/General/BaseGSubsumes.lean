/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.BaseGFinish

/-!
# Cross-development consistency: the base-`g` story at `g = 2` reproduces the base-2 story

A kernel-checked faithfulness anchor (à la `GeneralSubsumes`).  The base-`g` digit-representability
predicate `DStepDigitRepresentableBaseG 2 d W` — which encodes a valid base-2 digit as the *interval*
`0 ≤ dStepV − 2u ≤ 1` — coincides with the independently-built base-2 predicate
`DStepDigitRepresentable d W`, which encodes it as the *two-point set* `dStepV − 2u ∈ {0,1}`.  They agree
because the extracted digit is an **integer** (`dStepV` at the last step is a floor, `dStepZ`), and
`grt 2 d = rrt d`.  Hence the base-`g` `g = 2` impossibility is the base-2 impossibility.
-/

open MeasureTheory

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- `grt 2 d = rrt d` (the base-`g` multiplier at `g = 2` is the base-2 multiplier). -/
theorem grt_two_eq_rrt (d : ℕ) : grt 2 d = rrt d := by unfold grt rrt; norm_num

/-- **Per-step digit-predicate equivalence at `g = 2`.**  The base-`g` interval condition
`0 ≤ dStepV − 2u ≤ 1` and the base-2 two-point condition `dStepV − 2u ∈ {0,1}` are equivalent, because
the digit `dStepV − 2u` is an integer (`dStepZ_cast`). -/
theorem baseG_two_digit_iff (d : ℕ) (hd : 1 ≤ d) (c : ℕ → ℝ) (W : ℝ) (n : ℕ) :
    (0 ≤ dStepV (grt 2 d) c ⌊W * ((2 : ℕ) : ℝ) ^ n⌋ d
          - ((2 : ℕ) : ℝ) * (⌊W * ((2 : ℕ) : ℝ) ^ n⌋ : ℝ)
        ∧ dStepV (grt 2 d) c ⌊W * ((2 : ℕ) : ℝ) ^ n⌋ d
              - ((2 : ℕ) : ℝ) * (⌊W * ((2 : ℕ) : ℝ) ^ n⌋ : ℝ) ≤ ((2 : ℕ) : ℝ) - 1)
      ↔ (dStepV (rrt d) c ⌊W * 2 ^ n⌋ d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 0
          ∨ dStepV (rrt d) c ⌊W * 2 ^ n⌋ d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 1) := by
  have hpow : ((2 : ℕ) : ℝ) ^ n = (2 : ℝ) ^ n := by norm_num
  rw [grt_two_eq_rrt, hpow]
  have hv : dStepV (rrt d) c ⌊W * (2 : ℝ) ^ n⌋ d
      = ((dStepZ (rrt d) c ⌊W * (2 : ℝ) ^ n⌋ d : ℤ) : ℝ) :=
    (dStepZ_cast (rrt d) c ⌊W * (2 : ℝ) ^ n⌋ d hd).symm
  set z : ℤ := dStepZ (rrt d) c ⌊W * (2 : ℝ) ^ n⌋ d - 2 * ⌊W * (2 : ℝ) ^ n⌋ with hz
  have hexpr : dStepV (rrt d) c ⌊W * (2 : ℝ) ^ n⌋ d - 2 * (⌊W * (2 : ℝ) ^ n⌋ : ℝ) = (z : ℝ) := by
    rw [hv, hz]; push_cast; ring
  have hexpr' : dStepV (rrt d) c ⌊W * (2 : ℝ) ^ n⌋ d
      - ((2 : ℕ) : ℝ) * (⌊W * (2 : ℝ) ^ n⌋ : ℝ) = (z : ℝ) := by
    rw [← hexpr]; norm_num
  rw [hexpr, hexpr']
  constructor
  · rintro ⟨h1, h2⟩
    have hlo : 0 ≤ z := by exact_mod_cast h1
    have hhi : z ≤ 1 := by
      have : (z : ℝ) ≤ 1 := by
        have h2' : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
        rw [h2'] at h2; exact h2
      exact_mod_cast this
    rcases (by omega : z = 0 ∨ z = 1) with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  · rintro (h | h)
    · have hz0 : z = 0 := by exact_mod_cast h
      rw [hz0]; norm_num
    · have hz1 : z = 1 := by exact_mod_cast h
      rw [hz1]; norm_num

/-- **The base-`g` `g = 2` digit-representability predicate is the base-2 one.** -/
theorem DStepDigitRepresentableBaseG_two_iff (d : ℕ) (hd : 1 ≤ d) (W : ℝ) :
    DStepDigitRepresentableBaseG 2 d W ↔ DStepDigitRepresentable d W := by
  unfold DStepDigitRepresentableBaseG DStepDigitRepresentable
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, fun n => (baseG_two_digit_iff d hd c W n).mp (hc n)⟩
  · rintro ⟨c, hc⟩; exact ⟨c, fun n => (baseG_two_digit_iff d hd c W n).mpr (hc n)⟩

/-- **Cross-check headline: base-`g` `g = 2` impossibility ⟺ base-2 impossibility.**  The base-2
`ae_not_dStepDigitRepresentable` (built from the hand-rolled base-2 development) and the base-`g`
`g = 2` form are the same a.e. statement — kernel-checked consistency between the two developments. -/
theorem ae_not_DStepDigitRepresentableBaseG_two_via_base_two (d : ℕ) (hd : 3 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ DStepDigitRepresentableBaseG 2 d W := by
  filter_upwards [ae_not_dStepDigitRepresentable d hd] with W hW
  rw [DStepDigitRepresentableBaseG_two_iff d (by omega) W]
  exact hW

end LeanGallery.NumberTheory.Erdos482.General
