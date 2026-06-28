/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.GeneralOrbit
import LeanGallery.NumberTheory.Erdos482.General.GeneralTorusEquidist
import LeanGallery.NumberTheory.Erdos482.General.CubicFinish
import LeanGallery.NumberTheory.Erdos482.General.RpowWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Cardinality

/-!
# Torus-level plumbing for the general degree-`d` finish

Expresses the partial defect `dStepPartial` along the base-2 orbit as a function `dGpdTorus` on the
torus `Tᵈ = (ℝ/ℤ)ᵈ` (reusing `CubicFinish.torusRep`, the interior chart `ℝ/ℤ → [0,1)`), and proves it
is `ContinuousAt` torus points with nonzero coordinates and non-integer inner arguments.  This is the
glue between the algebraic engine (`GeneralOrbit.dGpd`) and the geometric input
(`GeneralTorusEquidist.ae_W_dTorus_orbit_dense`); the only remaining step to the general headline is the
nonzero-coordinate realization (see `PENDING_WORK.md`).
-/

open Filter MeasureTheory AddCircle
open scoped Topology

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- The `ℕ → ℝ` coordinate vector of a torus point (chart representatives, `0` past index `d`). -/
def coordsOf (d : ℕ) (a : Fin d → AddCircle (1 : ℝ)) : ℕ → ℝ :=
  fun i => if h : i < d then torusRep (a ⟨i, h⟩) else 0

/-- The partial-defect function on `Tᵈ`: `dGpd` evaluated at the chart representatives. -/
def dGpdTorus (d : ℕ) (α : ℝ) (c : ℕ → ℝ) (a : Fin d → AddCircle (1 : ℝ)) : ℝ :=
  dGpd α c (coordsOf d a) (d - 1)

/-- **`dGpdTorus` reads the partial defect along the base-2 orbit**: at seed `W`, step `n`,
`dGpdTorus d α c (dTorusOrbit d W n) = dStepPartial α c (⌊W·2ⁿ⌋) d` (`α = 2^{1/d}`).  General analogue
of `cubicGpdTorus_orbit`. -/
theorem dGpdTorus_orbit (d : ℕ) (hd : 1 ≤ d) (c : ℕ → ℝ) (W : ℝ) (n : ℕ) :
    dGpdTorus d (rrt d) c (dTorusOrbit d W n) = dStepPartial (rrt d) c (⌊W * 2 ^ n⌋) d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [dGpdTorus, Nat.add_sub_cancel,
    dGpd_congr (rrt (e + 1)) c (coordsOf (e + 1) (dTorusOrbit (e + 1) W n))
      (fun i => Int.fract ((rrt (e + 1)) ^ i * (W * 2 ^ n))) e ?_,
    ← dStepPartial_eq_dGpd]
  intro i hi
  have hid : i < e + 1 := by omega
  simp only [coordsOf, dif_pos hid, dTorusOrbit, torusRep_coe]
  congr 1
  ring

/-- **`dGpdTorus` is `ContinuousAt` any torus point with nonzero coordinates and non-integer inner
arguments** — the general analogue of `continuousAt_cubicGpdTorus`. -/
theorem continuousAt_dGpdTorus (d : ℕ) (α : ℝ) (c : ℕ → ℝ) (P : Fin d → AddCircle (1 : ℝ))
    (hne : ∀ i, P i ≠ 0)
    (harg : ∀ k, k < d - 1 →
      orbitArg α c (coordsOf d P) k ≠ ((⌊orbitArg α c (coordsOf d P) k⌋ : ℤ) : ℝ)) :
    ContinuousAt (dGpdTorus d α c) P := by
  have hcoord : ContinuousAt (fun a : Fin d → AddCircle (1 : ℝ) => coordsOf d a) P := by
    refine continuousAt_pi.2 (fun i => ?_)
    by_cases h : i < d
    · simp only [coordsOf, dif_pos h]
      exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin d → AddCircle (1 : ℝ) => a ⟨i, h⟩)
        (continuousAt_torusRep (hne ⟨i, h⟩)) (continuous_apply (⟨i, h⟩ : Fin d)).continuousAt
    · simp only [coordsOf, dif_neg h]
      exact continuousAt_const
  exact ContinuousAt.comp (g := fun r : ℕ → ℝ => dGpd α c r (d - 1))
    (f := fun a : Fin d → AddCircle (1 : ℝ) => coordsOf d a)
    (continuousAt_dGpd α c (coordsOf d P) (d - 1) harg) hcoord

/-- **The general-`d` impossibility, modulo the geometry crux.**  For `α = 2^{1/d}` (`d ≥ 1`), a fixed
schedule `c`, and *any* torus point `P` with nonzero coordinates and non-integer inner arguments whose
partial-defect value `dGpdTorus P` lies **outside** the digit window `(C-2, C]` (`C = dStepC … d`),
almost every `W` has a step `n` where the `d`-step floor map fails to read a base-2 digit
(`dStepV … − 2⌊W·2ⁿ⌋ ∉ {0,1}`).

This is the full assembly — density (`ae_W_dTorus_orbit_dense`) + continuity (`continuousAt_dGpdTorus`)
+ window confinement (`dStep_partial_mem_window`) via the threshold tools — leaving as its single
hypothesis exactly the **nonzero-coordinate realization** (constructible via `exists_scale_outside_window`
+ `orbitF_realizeR` + a countability choice; see `PENDING_WORK.md`).  Discharging that hypothesis turns
this into the unconditional uniform general-`d` headline. -/
theorem ae_dStep_fails_of_exceeding (d : ℕ) (hd : 1 ≤ d) (c : ℕ → ℝ)
    (P : Fin d → AddCircle (1 : ℝ)) (hne : ∀ i, P i ≠ 0)
    (harg : ∀ k, k < d - 1 →
      orbitArg (rrt d) c (coordsOf d P) k ≠ ((⌊orbitArg (rrt d) c (coordsOf d P) k⌋ : ℤ) : ℝ))
    (hexc : dGpdTorus d (rrt d) c P < dStepC (rrt d) c d - 2 ∨
            dStepC (rrt d) c d < dGpdTorus d (rrt d) c P) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∃ n : ℕ,
      ¬ (dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 0
          ∨ dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hα : (rrt (e + 1)) ^ (e + 1) = 2 := rrt_pow_self (e + 1) (by omega)
  have hcont : ContinuousAt (dGpdTorus (e + 1) (rrt (e + 1)) c) P :=
    continuousAt_dGpdTorus (e + 1) (rrt (e + 1)) c P hne harg
  filter_upwards [ae_W_dTorus_orbit_dense (d := e + 1) (by omega)] with W hdense
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hwin : ∀ n : ℕ, dStepC (rrt (e + 1)) c (e + 1) - 2
        < dGpdTorus (e + 1) (rrt (e + 1)) c (dTorusOrbit (e + 1) W n)
      ∧ dGpdTorus (e + 1) (rrt (e + 1)) c (dTorusOrbit (e + 1) W n)
        ≤ dStepC (rrt (e + 1)) c (e + 1) := by
    intro n
    rw [dGpdTorus_orbit (e + 1) (by omega)]
    exact dStep_partial_mem_window (rrt (e + 1)) c (⌊W * 2 ^ n⌋) e hα (hcon n)
  rcases hexc with hlt | hgt
  · obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont hlt
    exact absurd (hwin n).1 (not_lt.mpr hn.le)
  · obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont hgt
    exact absurd (hwin n).2 (not_le.mpr hn)

/-- **The geometry crux, discharged.**  For `α = 2^{1/d}` (`d ≥ 3`) and any schedule `c`, there is a
torus point `P : Tᵈ` with *all coordinates nonzero*, all inner fract-arguments non-integers, and
partial-defect value `dGpdTorus P` strictly outside the digit window `(C-2, C]` (`C = dStepC … d`).

This is the *nonzero-coordinate realization* the handoff flagged as the last gap.  Construction: take the
constant defect target `τ` from `exists_scale_outside_window_strict` (using the width bound `S_d > 2`,
`rrt_window_gt_two`), then build the coordinate vector `realizeR0 α c τ σ` with a free seed `σ` for the
0-th coordinate.  Every `orbitF` is then the constant `τ ∈ (0,1)` (`orbitF_realizeR0`) regardless of
`σ`, so `dGpdTorus = τ·S_d ∉ window` and (since `τ ≠ 0`) every inner arg is a non-integer.  The seed `σ`
is chosen in the *uncountable* `(0,1)` outside the *countable* bad set making any higher coordinate zero
(each bad set is the affine-preimage of `ℤ`, a countable range), so every torus coordinate is nonzero. -/
theorem exists_exceeding_torus_point (d : ℕ) (hd : 3 ≤ d) (c : ℕ → ℝ) :
    ∃ P : Fin d → AddCircle (1 : ℝ), (∀ i, P i ≠ 0)
      ∧ (∀ k, k < d - 1 →
          orbitArg (rrt d) c (coordsOf d P) k
            ≠ ((⌊orbitArg (rrt d) c (coordsOf d P) k⌋ : ℤ) : ℝ))
      ∧ (dGpdTorus d (rrt d) c P < dStepC (rrt d) c d - 2 ∨
          dStepC (rrt d) c d < dGpdTorus d (rrt d) c P) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  set α : ℝ := rrt (e + 1) with hαdef
  have hαpos : 0 < α := rrt_pos (e + 1)
  have hαne : α ^ (e + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hαpos)
  -- window width `S > 2`
  set S : ℝ := ∑ k ∈ Finset.range e, α ^ (e - k) with hSdef
  have hSsum : S = ∑ j ∈ Finset.Ico 1 (e + 1), α ^ j := by
    rw [hSdef, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      ← Finset.sum_range_reflect (fun k => α ^ (1 + k)) e]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk; congr 1; omega
  have hSgt : 2 < S := by rw [hSsum]; exact rrt_window_gt_two (e + 1) (by omega)
  -- the escaping scale `τ`
  obtain ⟨τ, hτ, hτout⟩ := exists_scale_outside_window_strict S (dStepC α c (e + 1)) hSgt
  have hτico : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
  -- the countable bad set and the chosen seed `σ`
  set K : ℕ → ℝ := fun k => (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) + α * c k with hKdef
  set g : ℕ → ℤ → ℝ := fun k m => ((m : ℝ) - τ + K k) / α ^ (k + 1) with hgdef
  set B : Set ℝ := ⋃ k : Fin e, Set.range (g k.val) with hBdef
  have hBcount : B.Countable := Set.countable_iUnion (fun k => Set.countable_range _)
  have huncount : ¬ (Set.Ioo (0 : ℝ) 1).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]; norm_num
  obtain ⟨σ, hσio, hσB⟩ : ∃ σ, σ ∈ Set.Ioo (0 : ℝ) 1 ∧ σ ∉ B := by
    by_contra hcon; push Not at hcon
    exact huncount (hBcount.mono (fun x hx => hcon x hx))
  -- the realizer and its coordinate properties
  set r : ℕ → ℝ := realizeR0 α c τ σ with hrdef
  have hr_ico : ∀ i, r i ∈ Set.Ico (0 : ℝ) 1 := by
    intro i
    rw [hrdef]; cases i with
    | zero => exact ⟨hσio.1.le, hσio.2⟩
    | succ k => exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hr_pos : ∀ i, i ≤ e → 0 < r i := by
    intro i hi
    rw [hrdef]
    cases i with
    | zero => exact hσio.1
    | succ k =>
      have hk : k < e := by omega
      have hval : realizeR0 α c τ σ (k + 1)
          = Int.fract (τ + α ^ (k + 1) * σ
              - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) - α * c k) := rfl
      rw [hval]
      refine lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm ?_)
      rw [Int.fract_ne_zero_iff]
      rintro ⟨m, hm⟩
      apply hσB
      rw [hBdef, Set.mem_iUnion]
      refine ⟨⟨k, hk⟩, m, ?_⟩
      simp only [hgdef, hKdef]
      rw [div_eq_iff (pow_ne_zero (k + 1) (ne_of_gt hαpos))]
      linear_combination hm
  -- the torus point
  set P : Fin (e + 1) → AddCircle (1 : ℝ) := fun i => ((r i.val : ℝ) : AddCircle (1 : ℝ)) with hPdef
  have hcoord : ∀ i, i ≤ e → coordsOf (e + 1) P i = r i := by
    intro i hi
    have hlt : i < e + 1 := by omega
    simp only [coordsOf, dif_pos hlt, hPdef, torusRep_coe]
    exact Int.fract_eq_self.mpr (hr_ico i)
  refine ⟨P, ?_, ?_, ?_⟩
  · -- all coordinates nonzero
    intro i
    have hi : i.val ≤ e := Nat.lt_succ_iff.mp i.isLt
    simp only [hPdef, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico (hr_ico i.val)]
    exact (hr_pos i.val hi).ne'
  · -- inner args non-integer (since `orbitF = τ ≠ 0`)
    intro k hk
    have hF : orbitF α c (coordsOf (e + 1) P) k = τ := by
      rw [orbitF_congr α c (coordsOf (e + 1) P) r k (fun i hi => hcoord i (by omega)), hrdef]
      exact orbitF_realizeR0 α c τ σ hτico k
    intro heq
    have hfr : Int.fract (orbitArg α c (coordsOf (e + 1) P) k) = 0 := by
      rw [heq]; exact Int.fract_intCast _
    rw [← orbitF_eq_fract_arg, hF] at hfr
    exact hτ.1.ne' hfr
  · -- value `= S·τ` strictly outside the window
    have hval : dGpdTorus (e + 1) α c P = S * τ := by
      have hterm : ∀ k ∈ Finset.range e,
          α ^ (e - k) * orbitF α c (realizeR0 α c τ σ) k = α ^ (e - k) * τ := by
        intro k _; rw [orbitF_realizeR0 α c τ σ hτico k]
      rw [dGpdTorus, Nat.add_sub_cancel,
        dGpd_congr α c (coordsOf (e + 1) P) r e (fun i hi => hcoord i hi)]
      unfold dGpd
      rw [hrdef, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hSdef]
    rw [hval]
    rcases hτout with h | h
    · exact Or.inl (by rw [mul_comm S τ]; exact h)
    · exact Or.inr (by rw [mul_comm S τ]; exact h)

/-- **The unconditional uniform general-`d` impossibility** (`d ≥ 3`, `α = 2^{1/d}`).  For *almost
every* real `W`, **no** `d`-periodic offset schedule `c` whatsoever makes the `d`-step floor map read
`W`'s base-2 digits: for every `c` there is a step `n` at which the extracted digit
`dStepV(⌊W·2ⁿ⌋) − 2⌊W·2ⁿ⌋ ∉ {0,1}`.

This is the general-degree analogue of `CubicFinish.ae_no_cubic_schedule_reads_base_two`, now uniform in
the degree.  The single exceptional null set is the schedule-independent orbit-density set
(`ae_W_dTorus_orbit_dense`); for each `W` there and each `c`, the geometry crux
(`exists_exceeding_torus_point`) exhibits a non-jump torus point where the partial defect leaves the
width-2 digit window, and density + continuity realize an out-of-window orbit step — contradicting the
window confinement `dStep_partial_mem_window`. -/
theorem ae_no_dStep_schedule_reads_base_two (d : ℕ) (hd : 3 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c : ℕ → ℝ, ∃ n : ℕ,
      ¬ (dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 0
          ∨ dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hα : (rrt (e + 1)) ^ (e + 1) = 2 := rrt_pow_self (e + 1) (by omega)
  filter_upwards [ae_W_dTorus_orbit_dense (d := e + 1) (by omega)] with W hdense
  intro c
  obtain ⟨P, hne, harg, hexc⟩ := exists_exceeding_torus_point (e + 1) (by omega) c
  have hcont : ContinuousAt (dGpdTorus (e + 1) (rrt (e + 1)) c) P :=
    continuousAt_dGpdTorus (e + 1) (rrt (e + 1)) c P hne harg
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hwin : ∀ n : ℕ, dStepC (rrt (e + 1)) c (e + 1) - 2
        < dGpdTorus (e + 1) (rrt (e + 1)) c (dTorusOrbit (e + 1) W n)
      ∧ dGpdTorus (e + 1) (rrt (e + 1)) c (dTorusOrbit (e + 1) W n)
        ≤ dStepC (rrt (e + 1)) c (e + 1) := by
    intro n
    rw [dGpdTorus_orbit (e + 1) (by omega)]
    exact dStep_partial_mem_window (rrt (e + 1)) c (⌊W * 2 ^ n⌋) e hα (hcon n)
  rcases hexc with hlt | hgt
  · obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont hlt
    exact absurd (hwin n).1 (not_lt.mpr hn.le)
  · obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont hgt
    exact absurd (hwin n).2 (not_le.mpr hn)

/-- **Fixed-schedule form.**  For each `d`-periodic schedule `c` (`d ≥ 3`), almost every `W` has a step
where the `d`-step readout fails to be a base-2 digit.  Immediate from the uniform version. -/
theorem ae_dStep_not_reads_base_two (d : ℕ) (hd : 3 ≤ d) (c : ℕ → ℝ) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∃ n : ℕ,
      ¬ (dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 0
          ∨ dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 1) := by
  filter_upwards [ae_no_dStep_schedule_reads_base_two d hd] with W hW
  exact hW c

/-- **`W` is `d`-step-digit-representable** if some `d`-periodic offset schedule `c` makes the `d`-step
floor map emit a *valid base-2 digit* `dStepV(uₙ) − 2uₙ ∈ {0,1}` at every step of the binary block orbit
`uₙ = ⌊W·2ⁿ⌋`.  General-degree analogue of `CubicFinish.CubicDigitRepresentable`. -/
def DStepDigitRepresentable (d : ℕ) (W : ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ n : ℕ,
    dStepV (rrt d) c ⌊W * 2 ^ n⌋ d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 0
      ∨ dStepV (rrt d) c ⌊W * 2 ^ n⌋ d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 1

/-- **Almost no real is `d`-step-digit-representable** (`d ≥ 3`).  The general headline in its cleanest
form: the set of `W` for which *some* fixed degree-`d` schedule reads all of `W`'s base-2 digits is
Lebesgue-null.  Immediate from `ae_no_dStep_schedule_reads_base_two`. -/
theorem ae_not_dStepDigitRepresentable (d : ℕ) (hd : 3 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ DStepDigitRepresentable d W := by
  filter_upwards [ae_no_dStep_schedule_reads_base_two d hd] with W hW
  rintro ⟨c, hall⟩
  obtain ⟨n, hn⟩ := hW c
  exact hn (hall n)

/-- **The `d`-step map correctly reads `W`'s base-2 doubling** if some schedule `c` makes the `d`-step
floor map send each binary block `uₙ = ⌊W·2ⁿ⌋` to the next, `dStepV(uₙ) = ⌊W·2ⁿ⁺¹⌋` for all `n`.  The
genuine self-referential condition — the map *computes* `W`'s base-2 doubling. -/
def DStepReadsBaseTwo (d : ℕ) (W : ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ n : ℕ, dStepV (rrt d) c ⌊W * 2 ^ n⌋ d = (⌊W * 2 ^ (n + 1)⌋ : ℝ)

/-- **The `d`-step map computes no real's base-2 doubling, for almost every `W`** (`d ≥ 3`).  The
self-referential capstone: the set of `W` whose base-2 doubling some degree-`d` schedule correctly
computes (`dStepV(⌊W·2ⁿ⌋) = ⌊W·2ⁿ⁺¹⌋` ∀n) is Lebesgue-null.  Correct reading forces every emitted digit
`dStepV(uₙ) − 2uₙ = ⌊W·2ⁿ⁺¹⌋ − 2⌊W·2ⁿ⌋ ∈ {0,1}` (`floor_two_mul_sub_mem`), i.e.
`DStepDigitRepresentable d W`, which is a.e. false. -/
theorem ae_not_dStepReadsBaseTwo (d : ℕ) (hd : 3 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ DStepReadsBaseTwo d W := by
  filter_upwards [ae_not_dStepDigitRepresentable d hd] with W hW
  rintro ⟨c, hread⟩
  refine hW ⟨c, fun n => ?_⟩
  have hdouble : ⌊W * 2 ^ (n + 1)⌋ = ⌊2 * (W * 2 ^ n)⌋ := by
    rw [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring]; ring_nf
  rw [hread n, hdouble]
  rcases floor_two_mul_sub_mem (W * 2 ^ n) with h | h
  · left
    have h' : ((⌊2 * (W * 2 ^ n)⌋ - 2 * ⌊W * 2 ^ n⌋ : ℤ) : ℝ) = 0 := by exact_mod_cast h
    push_cast at h'; linarith
  · right
    have h' : ((⌊2 * (W * 2 ^ n)⌋ - 2 * ⌊W * 2 ^ n⌋ : ℤ) : ℝ) = 1 := by exact_mod_cast h
    push_cast at h'; linarith

/-- **`W` is `d`-step-recurrence-representable** if some schedule `c` admits a genuine *self-referential
recurrence* orbit `orbit : ℕ → ℤ` — `orbit(n+1) = dStepZ(orbit n)` — that emits a valid base-2 digit
`dStepZ(orbit n) − 2·orbit n ∈ {0,1}` at every step, is not eventually all-`1`s (excluding the
degenerate dyadic tail), and whose recovered binary value is `W`.  This is the impossibility phrased on
the *actual recurrence* of the `d`-step self-referential map.  General analogue of
`CubicFinish.CubicRecurrenceRepresentable`. -/
def DStepRecurrenceRepresentable (d : ℕ) (W : ℝ) : Prop :=
  ∃ (c : ℕ → ℝ) (orbit : ℕ → ℤ),
    (∀ n, orbit (n + 1) = dStepZ (rrt d) c (orbit n) d) ∧
    (∀ n, dStepZ (rrt d) c (orbit n) d - 2 * orbit n = 0
        ∨ dStepZ (rrt d) c (orbit n) d - 2 * orbit n = 1) ∧
    (∀ N, ∃ k, N ≤ k ∧ dStepZ (rrt d) c (orbit k) d - 2 * orbit k = 0) ∧
    W = (orbit 0 : ℝ) + ∑' k : ℕ,
        ((dStepZ (rrt d) c (orbit k) d - 2 * orbit k : ℤ) : ℝ) * (1 / 2) ^ (k + 1)

/-- **Almost no real is `d`-step-recurrence-representable** (`d ≥ 3`).  The self-referential capstone on
the genuine recurrence: the set of `W` whose base-2 digits some degree-`d` schedule reads along its
*own* orbit (`orbit(n+1) = dStepZ(orbit n)`) is Lebesgue-null.  The `binary_floor_eq` bridge identifies
the recurrence orbit with the floor orbit of its value (`orbit n = ⌊W·2ⁿ⌋`), reducing to
`ae_not_dStepDigitRepresentable`. -/
theorem ae_not_dStepRecurrenceRepresentable (d : ℕ) (hd : 3 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ DStepRecurrenceRepresentable d W := by
  filter_upwards [ae_not_dStepDigitRepresentable d hd] with W hW
  rintro ⟨c, orbit, hstep, hdig, htail, hWval⟩
  set dig : ℕ → ℤ := fun k => dStepZ (rrt d) c (orbit k) d - 2 * orbit k with hdigdef
  have hostep : ∀ n, orbit (n + 1) = 2 * orbit n + dig n := by
    intro n; rw [hdigdef]; simp only; rw [hstep n]; ring
  have hfloor : ∀ n, ⌊W * 2 ^ n⌋ = orbit n :=
    binary_floor_eq (orbit 0) dig orbit hdig rfl hostep htail W hWval
  refine hW ⟨c, fun n => ?_⟩
  have hcast : dStepV (rrt d) c (orbit n) d - 2 * (orbit n : ℝ)
      = ((dStepZ (rrt d) c (orbit n) d - 2 * orbit n : ℤ) : ℝ) := by
    rw [← dStepZ_cast (rrt d) c (orbit n) d (by omega)]; push_cast; ring
  rw [hfloor n, hcast]
  rcases hdig n with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

end LeanGallery.NumberTheory.Erdos482.General
