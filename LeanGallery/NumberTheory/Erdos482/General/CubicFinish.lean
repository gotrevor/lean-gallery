/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.CubicDefectLink
import LeanGallery.NumberTheory.Erdos482.General.CubicTorusEquidist
import LeanGallery.NumberTheory.Erdos482.General.EquidistDense
import LeanGallery.NumberTheory.Erdos482.General.BinaryExpansion

/-!
# Piece 2 of the cubic finish: the partial defect as a *continuous* function on `T³`

`PENDING_WORK.md ★★★` piece 2.  To feed the density tool `EquidistDense.exists_lt_of_dense_continuousAt`
we need a single function `F : T³ → ℝ` (`T = ℝ/ℤ`) with
* `F (cubicTorusOrbit W n) = cubicPartialDefect α c0 c1 c2 (⌊W·2ⁿ⌋)` — it reads the partial defect along
  the orbit, and
* `ContinuousAt F p` at any torus point `p` whose three real representatives `ρ(p i) = {·}` are nonzero
  and whose two inner `fract`-arguments are non-integers.

The representative map `ρ : ℝ/ℤ → ℝ` is the canonical interior chart `ρ x := (AddCircle.equivIco 1 0 x)`,
which satisfies `ρ (↑t) = Int.fract t` (`AddCircle.coe_equivIco_mk_apply`) and is `ContinuousAt` away from
`0` (`AddCircle.continuousAt_equivIco`).  Then `F a := cubicGpd α c0 c1 (ρ (a 0)) (ρ (a 1)) (ρ (a 2))`,
and `ContinuousAt F p` reduces (via `ContinuousAt.comp`) to `continuousAt_cubicGpd`
(`CubicDefectLink`).
-/

open Filter Topology MeasureTheory UnitAddTorus AddCircle

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- The canonical real representative of a torus point: the interior chart `ℝ/ℤ → [0,1) ⊆ ℝ`. -/
def torusRep (x : AddCircle (1:ℝ)) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x : ℝ)

/-- `torusRep (↑t) = {t}`.  The representative of a coerced real is its fractional part. -/
@[simp] theorem torusRep_coe (t : ℝ) : torusRep ((t : AddCircle (1:ℝ))) = Int.fract t := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  simp only [torusRep, AddCircle.coe_equivIco_mk_apply]
  simp

/-- `torusRep` is continuous at every nonzero torus point (the chart is continuous off the cut `0`). -/
theorem continuousAt_torusRep {x : AddCircle (1:ℝ)} (hx : x ≠ 0) : ContinuousAt torusRep x := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  exact ContinuousAt.comp (g := fun y : Set.Ico (0:ℝ) (0+1) => (y : ℝ))
    (f := fun y => AddCircle.equivIco (1:ℝ) 0 y)
    continuousAt_subtype_val (AddCircle.continuousAt_equivIco (1:ℝ) 0 hx)

/-- **The partial defect as a function on `T³`.**  `F a = cubicGpd α c0 c1 (ρ (a 0)) (ρ (a 1)) (ρ (a 2))`
with `ρ = torusRep`. -/
def cubicGpdTorus (α c0 c1 : ℝ) (a : Fin 3 → AddCircle (1:ℝ)) : ℝ :=
  cubicGpd α c0 c1 (torusRep (a 0)) (torusRep (a 1)) (torusRep (a 2))

/-- **`cubicGpdTorus` reads the partial defect along the cubic orbit.**  At seed `W` and step `n`,
`F (cubicTorusOrbit W n) = cubicPartialDefect α c0 c1 c2 (⌊W·2ⁿ⌋)` (when `α = cbrt2`). -/
theorem cubicGpdTorus_orbit (c0 c1 c2 W : ℝ) (n : ℕ) :
    cubicGpdTorus cbrt2 c0 c1 (cubicTorusOrbit W n)
      = cubicPartialDefect cbrt2 c0 c1 c2 (⌊W * 2 ^ n⌋) := by
  rw [cubicPartialDefect_eq_Gpd]
  simp only [cubicGpdTorus, cubicTorusOrbit, torusRep_coe, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
  congr 1 <;> · congr 1 ; ring

/-- **`cubicGpdTorus` is continuous at any torus point with nonzero coordinates whose two inner
`fract`-arguments are non-integers.**  The representative map `torusRep` is continuous at each nonzero
coordinate; `continuousAt_cubicGpd` supplies continuity of the algebraic core; `ContinuousAt.comp`
glues them.  This is the input `F`/`ContinuousAt F p` demanded by
`EquidistDense.exists_lt_of_dense_continuousAt`. -/
theorem continuousAt_cubicGpdTorus (α c0 c1 : ℝ) {p : Fin 3 → AddCircle (1:ℝ)}
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (h2 : p 2 ≠ 0)
    (hA : torusRep (p 1) - α * torusRep (p 0) + α * c0
            ≠ (⌊torusRep (p 1) - α * torusRep (p 0) + α * c0⌋ : ℤ))
    (hB : torusRep (p 2) - α ^ 2 * torusRep (p 0)
            - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊torusRep (p 2) - α ^ 2 * torusRep (p 0)
                - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0)
                + α ^ 2 * c0 + α * c1⌋ : ℤ)) :
    ContinuousAt (cubicGpdTorus α c0 c1) p := by
  have hΦ : ContinuousAt
      (fun a : Fin 3 → AddCircle (1:ℝ) => (torusRep (a 0), torusRep (a 1), torusRep (a 2))) p := by
    refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 3 → AddCircle (1:ℝ) => a 0)
        (continuousAt_torusRep h0) (continuous_apply 0).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 3 → AddCircle (1:ℝ) => a 1)
        (continuousAt_torusRep h1) (continuous_apply 1).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 3 → AddCircle (1:ℝ) => a 2)
        (continuousAt_torusRep h2) (continuous_apply 2).continuousAt
  have hG : ContinuousAt (fun q : ℝ × ℝ × ℝ => cubicGpd α c0 c1 q.1 q.2.1 q.2.2)
      (torusRep (p 0), torusRep (p 1), torusRep (p 2)) :=
    continuousAt_cubicGpd α c0 c1 (torusRep (p 0), torusRep (p 1), torusRep (p 2)) hA hB
  exact ContinuousAt.comp (g := fun q : ℝ × ℝ × ℝ => cubicGpd α c0 c1 q.1 q.2.1 q.2.2)
    (f := fun a : Fin 3 → AddCircle (1:ℝ) => (torusRep (a 0), torusRep (a 1), torusRep (a 2)))
    hG hΦ

/-! ### The cubic multiplier `cbrt2` satisfies `cbrt2 ^ 3 = 2`. -/

/-- `cbrt2 ^ 3 = 2` (`cbrt2 = 2^{1/3}`). -/
theorem cbrt2_cube : cbrt2 ^ 3 = 2 := by
  rw [cbrt2, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `1 < cbrt2` (`cbrt2 = 2^{1/3}`, base `> 1`, exponent `> 0`). -/
theorem one_lt_cbrt2 : 1 < cbrt2 := by
  rw [cbrt2, Real.one_lt_rpow_iff_of_pos (by norm_num)]
  left; constructor <;> norm_num

/-! ### The geometric crux: the partial defect leaves every digit window.

For any schedule `(c₀,c₁,c₂)` there is an interior, non-jump point of the canonical fractional-coordinate
cube `(0,1)³` at which the partial-defect function `cubicGpd` *leaves* the digit window `(C−2, C]`
(`C = 2c₀+α²c₁+αc₂`).  This is the width-`(α²+α) > 2` range argument made constructive: choose `(fA,fB)`
near a corner of `(0,1)²` so that `cubicGpd = α²fA + αfB` exceeds `C` (when `C < α²+α`) or falls below
`C−2` (when `C ≥ α²+α`); realize `(fA,fB)` by solving the two `fract` equations for `(r₁,r₂,r₃)`.

Proof harvested from Aristotle job `7b1ff2ad` ("gpdwin"), verified in our kernel + `#print axioms`-clean.
-/

/-- **`fract`-shift realization.**  For any shift `K` and non-degenerate target window `(lo, hi) ⊆ [0,1]`,
there is `r ∈ (0,1)` whose shifted fractional part `fract (r + K)` lands strictly inside `(lo, hi)`.
Witness `r = fract (f − K)` for a target `f` in the window (so `fract (r+K) = f`); strict positivity of
`r` from two candidate targets `< 1` apart (both giving `r = 0` would force a nonzero integer in `(0,1)`). -/
theorem fract_shift_realize (K lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hlt : lo < hi) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ lo < Int.fract (r + K) ∧ Int.fract (r + K) < hi := by
  have realize : ∀ f : ℝ, 0 ≤ f → f < 1 → Int.fract (Int.fract (f - K) + K) = f := by
    intro f h0 h1
    rw [← Int.self_sub_floor (f - K)]
    rw [show f - K - (⌊f-K⌋:ℝ) + K = f - (⌊f-K⌋:ℝ) by ring]
    rw [Int.fract_sub_intCast]
    exact Int.fract_eq_self.mpr ⟨h0, h1⟩
  set f1 := (lo + hi)/2 with hf1
  set f2 := (lo + f1)/2 with hf2
  have hf1lo : lo < f1 := by rw [hf1]; linarith
  have hf1hi : f1 < hi := by rw [hf1]; linarith
  have hf2lo : lo < f2 := by rw [hf2]; linarith
  have hf2f1 : f2 < f1 := by rw [hf2]; linarith
  have hf10 : 0 ≤ f1 := le_trans hlo (le_of_lt hf1lo)
  have hf11 : f1 < 1 := lt_of_lt_of_le hf1hi hhi
  have hf20 : 0 ≤ f2 := le_trans hlo (le_of_lt hf2lo)
  have hf21 : f2 < 1 := lt_trans hf2f1 hf11
  set r1 := Int.fract (f1 - K) with hr1
  set r2 := Int.fract (f2 - K) with hr2
  have hr1nn : 0 ≤ r1 := Int.fract_nonneg _
  have hr1lt : r1 < 1 := Int.fract_lt_one _
  have hr2nn : 0 ≤ r2 := Int.fract_nonneg _
  have hr2lt : r2 < 1 := Int.fract_lt_one _
  have hval1 : Int.fract (r1 + K) = f1 := realize f1 hf10 hf11
  have hval2 : Int.fract (r2 + K) = f2 := realize f2 hf20 hf21
  rcases eq_or_lt_of_le hr1nn with h1z | h1pos
  · have hr2pos : 0 < r2 := by
      rcases eq_or_lt_of_le hr2nn with h2z | h2pos
      · exfalso
        have e1 : Int.fract (f1 - K) = 0 := by rw [← hr1, ← h1z]
        have e2 : Int.fract (f2 - K) = 0 := by rw [← hr2, ← h2z]
        set x := f1 - K
        set y := f2 - K
        have hxy_pos : 0 < x - y := by simp only [x, y]; linarith
        have hxy_ub : x - y < 1 := by simp only [x, y]; linarith
        have hx' : x = (⌊x⌋:ℝ) := by have := Int.self_sub_floor x; rw [e1] at this; linarith
        have hy' : y = (⌊y⌋:ℝ) := by have := Int.self_sub_floor y; rw [e2] at this; linarith
        have heq : x - y = (((⌊x⌋ - ⌊y⌋ : ℤ)):ℝ) := by push_cast; linarith [hx', hy']
        rw [heq] at hxy_pos hxy_ub
        have hh0 : (0:ℤ) < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast hxy_pos
        have hh1 : (⌊x⌋ - ⌊y⌋ : ℤ) < 1 := by exact_mod_cast hxy_ub
        omega
      · exact h2pos
    exact ⟨r2, hr2pos, hr2lt, by rw [hval2]; exact hf2lo, by rw [hval2]; linarith⟩
  · exact ⟨r1, h1pos, hr1lt, by rw [hval1]; exact hf1lo, by rw [hval1]; exact hf1hi⟩

/-- **The partial defect leaves every window (general `α`).**  For `1 < α`, `α³ = 2`, any schedule
`(c₀,c₁)` and any constant `C`, there is `(r₁,r₂,r₃) ∈ (0,1)³` with the two inner `fract`-arguments
non-integers and `cubicGpd α c0 c1 r1 r2 r3 ∉ (C−2, C]`. -/
theorem cubicGpd_exceeds_window_general (α c0 c1 : ℝ) (hα : 1 < α) (_hα3 : α ^ 3 = 2) (C : ℝ) :
    ∃ r1 r2 r3 : ℝ, 0 < r1 ∧ r1 < 1 ∧ 0 < r2 ∧ r2 < 1 ∧ 0 < r3 ∧ r3 < 1
      ∧ (r2 - α * r1 + α * c0 ≠ (⌊r2 - α * r1 + α * c0⌋ : ℤ))
      ∧ (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1⌋ : ℤ))
      ∧ (cubicGpd α c0 c1 r1 r2 r3 < C - 2 ∨ C < cubicGpd α c0 c1 r1 r2 r3) := by
  have hαpos : 0 < α := by linarith
  have hα2 : 1 < α^2 := by nlinarith
  have hsum : 2 < α^2 + α := by nlinarith
  have hsumpos : 0 < α^2 + α := by linarith
  have fne : ∀ x:ℝ, Int.fract x ≠ 0 → x ≠ ((⌊x⌋:ℤ):ℝ) := by
    intro x hx h; apply hx; have hsf := Int.self_sub_floor x; linarith
  set K1 := α*c0 - α*(1/2) with hK1
  by_cases hC : C < α^2 + α
  · -- value > C; choose fA, fB near 1
    set lo := max 0 (C/(α^2+α)) with hlodef
    have hlo0 : 0 ≤ lo := le_max_left _ _
    have hlolt : lo < 1 := by
      apply max_lt
      · norm_num
      · rw [div_lt_one hsumpos]; exact hC
    have hloge : C/(α^2+α) ≤ lo := le_max_right _ _
    have hmul : C ≤ lo*(α^2+α) := (div_le_iff₀ hsumpos).mp hloge
    obtain ⟨r2, hr2pos, hr2lt, hfAlo, hfAhi⟩ := fract_shift_realize K1 lo 1 hlo0 (le_refl 1) hlolt
    set fA := Int.fract (r2 + K1) with hfA
    set K2 := α^2*c0 + α*c1 - α^2*(1/2) - α*fA with hK2
    obtain ⟨r3, hr3pos, hr3lt, hfBlo, hfBhi⟩ := fract_shift_realize K2 lo 1 hlo0 (le_refl 1) hlolt
    set fB := Int.fract (r3 + K2) with hfB
    have e1 : Int.fract (r2 - α*(1/2) + α*c0) = fA := by rw [hfA, hK1]; congr 1; ring
    have hval : cubicGpd α c0 c1 (1/2) r2 r3 = α^2*fA + α*fB := by
      unfold cubicGpd
      rw [e1, show r3 - α^2*(1/2:ℝ) - α*fA + α^2*c0 + α*c1 = r3 + K2 by rw [hK2]; ring, ← hfB]
    refine ⟨1/2, r2, r3, by norm_num, by norm_num, hr2pos, hr2lt, hr3pos, hr3lt, ?_, ?_, ?_⟩
    · apply fne; rw [e1]; linarith
    · apply fne
      rw [show r3 - α^2*(1/2:ℝ) - α*Int.fract (r2 - α*(1/2)+α*c0) + α^2*c0 + α*c1 = r3 + K2 by
            rw [e1, hK2]; ring, ← hfB]
      linarith
    · right
      rw [hval]
      nlinarith [mul_pos (show (0:ℝ)<α^2 by positivity) (sub_pos.mpr hfAlo),
                 mul_pos hαpos (sub_pos.mpr hfBlo), hmul]
  · -- value < C - 2; choose fA, fB near 0
    push Not at hC
    have hC2 : 0 < C - 2 := by linarith
    set hi := min (1/2) ((C-2)/(α^2+α)) with hidef
    have hipos : 0 < hi := by
      apply lt_min
      · norm_num
      · positivity
    have hile : hi ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
    have hile2 : hi ≤ (C-2)/(α^2+α) := min_le_right _ _
    have hmul2 : hi*(α^2+α) ≤ C-2 := (le_div_iff₀ hsumpos).mp hile2
    obtain ⟨r2, hr2pos, hr2lt, hfAlo, hfAhi⟩ := fract_shift_realize K1 0 hi (le_refl 0) hile hipos
    set fA := Int.fract (r2 + K1) with hfA
    set K2 := α^2*c0 + α*c1 - α^2*(1/2) - α*fA with hK2
    obtain ⟨r3, hr3pos, hr3lt, hfBlo, hfBhi⟩ := fract_shift_realize K2 0 hi (le_refl 0) hile hipos
    set fB := Int.fract (r3 + K2) with hfB
    have e1 : Int.fract (r2 - α*(1/2) + α*c0) = fA := by rw [hfA, hK1]; congr 1; ring
    have hval : cubicGpd α c0 c1 (1/2) r2 r3 = α^2*fA + α*fB := by
      unfold cubicGpd
      rw [e1, show r3 - α^2*(1/2:ℝ) - α*fA + α^2*c0 + α*c1 = r3 + K2 by rw [hK2]; ring, ← hfB]
    refine ⟨1/2, r2, r3, by norm_num, by norm_num, hr2pos, hr2lt, hr3pos, hr3lt, ?_, ?_, ?_⟩
    · apply fne; rw [e1]; linarith
    · apply fne
      rw [show r3 - α^2*(1/2:ℝ) - α*Int.fract (r2 - α*(1/2)+α*c0) + α^2*c0 + α*c1 = r3 + K2 by
            rw [e1, hK2]; ring, ← hfB]
      linarith
    · left
      rw [hval]
      nlinarith [mul_pos (show (0:ℝ)<α^2 by positivity) (sub_pos.mpr hfAhi),
                 mul_pos hαpos (sub_pos.mpr hfBhi), hmul2]

/-- **The geometric crux, specialized to `α = cbrt2` and the cubic window `C = 2c₀+α²c₁+αc₂`.**
Discharges the obligation consumed by `ae_W_cubic_not_reads_base_two`. -/
theorem cubicGpd_exceeds_window (c0 c1 c2 : ℝ) :
    ∃ r1 r2 r3 : ℝ, (0 < r1 ∧ r1 < 1) ∧ (0 < r2 ∧ r2 < 1) ∧ (0 < r3 ∧ r3 < 1) ∧
      (r2 - cbrt2 * r1 + cbrt2 * c0 ≠ (⌊r2 - cbrt2 * r1 + cbrt2 * c0⌋ : ℤ)) ∧
      (r3 - cbrt2 ^ 2 * r1
          - cbrt2 * Int.fract (r2 - cbrt2 * r1 + cbrt2 * c0) + cbrt2 ^ 2 * c0 + cbrt2 * c1
        ≠ (⌊r3 - cbrt2 ^ 2 * r1
              - cbrt2 * Int.fract (r2 - cbrt2 * r1 + cbrt2 * c0) + cbrt2 ^ 2 * c0 + cbrt2 * c1⌋ : ℤ)) ∧
      ((2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2) < cubicGpd cbrt2 c0 c1 r1 r2 r3 ∨
        cubicGpd cbrt2 c0 c1 r1 r2 r3 < (2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2) - 2) := by
  obtain ⟨r1, r2, r3, h1p, h1l, h2p, h2l, h3p, h3l, hA, hB, hval⟩ :=
    cubicGpd_exceeds_window_general cbrt2 c0 c1 one_lt_cbrt2 cbrt2_cube
      (2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2)
  exact ⟨r1, r2, r3, ⟨h1p, h1l⟩, ⟨h2p, h2l⟩, ⟨h3p, h3l⟩, hA, hB, hval.symm⟩

/-- **Unconditional a.e.-`W` cubic impossibility, uniform over *all* schedules.**  For `α = 2^{1/3}`
and *almost every* real `W`, **no** 3-periodic offset schedule `(c₀,c₁,c₂)` whatsoever makes the
three-step cubic floor map read `W`'s base-2 digits: for every schedule there is a step `n` at which the
extracted digit `cubicV3(⌊W·2ⁿ⌋) − 2⌊W·2ⁿ⌋ ∉ {0,1}`.

The strength here — a single a.e. set defeating *every* schedule simultaneously — comes from the fact
that the exceptional set is exactly the orbit-density set `ae_W_cubic_torus_orbit_dense`, which is
**schedule-independent**: density of the doubling orbit `(2ⁿW, 2ⁿαW, 2ⁿα²W)` is a property of `W` alone.
For any such `W` and any schedule, the partial defect along the orbit is the continuous-off-jumps torus
function `cubicGpdTorus`, and `cubicGpd_exceeds_window` (valid for the window of *any* `C`) exhibits an
interior non-jump point where it leaves the window; `exists_lt/gt_of_dense_continuousAt` realizes an
out-of-window step — contradicting `cubic_partial_defect_mem_window`. -/
theorem ae_no_cubic_schedule_reads_base_two :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c0 c1 c2 : ℝ, ∃ n : ℕ,
      ¬ (cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
          ∨ cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1) := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  filter_upwards [ae_W_cubic_torus_orbit_dense] with W hdense
  intro c0 c1 c2
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ n, digitₙ = 0 ∨ digitₙ = 1`.  Window confinement of the partial defect along the orbit.
  set C : ℝ := 2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2 with hC
  have hwin : ∀ n : ℕ, C - 2 < cubicGpdTorus cbrt2 c0 c1 (cubicTorusOrbit W n)
      ∧ cubicGpdTorus cbrt2 c0 c1 (cubicTorusOrbit W n) ≤ C := by
    intro n
    have hw := cubic_partial_defect_mem_window cbrt2 c0 c1 c2 cbrt2_cube ⌊W * 2 ^ n⌋ (hcon n)
    rw [cubicGpdTorus_orbit (c2 := c2)]
    exact hw
  -- The interior non-jump torus point where the partial defect leaves the window.
  obtain ⟨r1, r2, r3, hr1, hr2, hr3, hA, hB, hval⟩ := cubicGpd_exceeds_window c0 c1 c2
  set P : Fin 3 → AddCircle (1:ℝ) := ![(r1 : AddCircle (1:ℝ)), (r2 : AddCircle (1:ℝ)),
    (r3 : AddCircle (1:ℝ))] with hP
  have hP0 : P 0 = (r1 : AddCircle (1:ℝ)) := rfl
  have hP1 : P 1 = (r2 : AddCircle (1:ℝ)) := rfl
  have hP2 : P 2 = (r3 : AddCircle (1:ℝ)) := rfl
  have hrep0 : torusRep (P 0) = r1 := by rw [hP0, torusRep_coe, Int.fract_eq_self.mpr ⟨hr1.1.le, hr1.2⟩]
  have hrep1 : torusRep (P 1) = r2 := by rw [hP1, torusRep_coe, Int.fract_eq_self.mpr ⟨hr2.1.le, hr2.2⟩]
  have hrep2 : torusRep (P 2) = r3 := by rw [hP2, torusRep_coe, Int.fract_eq_self.mpr ⟨hr3.1.le, hr3.2⟩]
  have hne0 : P 0 ≠ 0 := by
    rw [hP0, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr1.1.le, hr1.2⟩]; exact ne_of_gt hr1.1
  have hne1 : P 1 ≠ 0 := by
    rw [hP1, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr2.1.le, hr2.2⟩]; exact ne_of_gt hr2.1
  have hne2 : P 2 ≠ 0 := by
    rw [hP2, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr3.1.le, hr3.2⟩]; exact ne_of_gt hr3.1
  -- Continuity of the partial-defect function at `P`.
  have hcont : ContinuousAt (cubicGpdTorus cbrt2 c0 c1) P :=
    continuousAt_cubicGpdTorus cbrt2 c0 c1 hne0 hne1 hne2
      (by rw [hrep0, hrep1]; exact hA) (by rw [hrep0, hrep1, hrep2]; exact hB)
  -- The function value at `P` matches the real-coordinate `cubicGpd` and leaves the window.
  have hPval : cubicGpdTorus cbrt2 c0 c1 P = cubicGpd cbrt2 c0 c1 r1 r2 r3 := by
    simp only [cubicGpdTorus, hrep0, hrep1, hrep2]
  rcases hval with hgt | hlt
  · -- value `> C`: dense orbit realizes a `g > C`, contradicting `g ≤ C`.
    have hc : C < cubicGpdTorus cbrt2 c0 c1 P := by rw [hPval]; exact hgt
    obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont (c := C) hc
    exact absurd (hwin n).2 (not_le.mpr hn)
  · -- value `< C − 2`: dense orbit realizes a `g < C − 2`, contradicting `C − 2 < g`.
    have hc : cubicGpdTorus cbrt2 c0 c1 P < C - 2 := by rw [hPval]; exact hlt
    obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont (c := C - 2) hc
    exact absurd (hwin n).1 (not_lt.mpr hn.le)

/-- **Fixed-schedule form.**  For each schedule `(c₀,c₁,c₂)`, almost every `W` has a step where the
cubic readout fails to be a base-2 digit.  Immediate specialization of the uniform
`ae_no_cubic_schedule_reads_base_two`. -/
theorem ae_W_cubic_not_reads_base_two (c0 c1 c2 : ℝ) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∃ n : ℕ,
      ¬ (cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
          ∨ cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1) := by
  filter_upwards [ae_no_cubic_schedule_reads_base_two] with W hW
  exact hW c0 c1 c2

/-- **`W` is cubic-digit-representable** if some 3-periodic offset schedule `(c₀,c₁,c₂)` makes the
three-step cubic floor map `⌊α(⌊α(⌊α(u+c₀)⌋+c₁)⌋+c₂)⌋` (`α=2^{1/3}`) emit a *valid base-2 digit*
`cubicV3(uₙ) − 2uₙ ∈ {0,1}` at **every** step of the binary block orbit `uₙ = ⌊W·2ⁿ⌋`. -/
def CubicDigitRepresentable (W : ℝ) : Prop :=
  ∃ c0 c1 c2 : ℝ, ∀ n : ℕ,
    cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
      ∨ cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1

/-- **Almost no real is cubic-digit-representable.**  The headline impossibility in its cleanest form:
the set of `W` for which *some* fixed cubic schedule reads all of `W`'s base-2 digits is Lebesgue-null.
Immediate from the uniform `ae_no_cubic_schedule_reads_base_two`. -/
theorem ae_not_cubicDigitRepresentable :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ CubicDigitRepresentable W := by
  filter_upwards [ae_no_cubic_schedule_reads_base_two] with W hW
  rintro ⟨c0, c1, c2, hall⟩
  obtain ⟨n, hn⟩ := hW c0 c1 c2
  exact hn (hall n)

/-- The doubling-digit `⌊2x⌋ − 2⌊x⌋` of any real is a base-2 digit `∈ {0,1}`. -/
theorem floor_two_mul_sub_mem (x : ℝ) : ⌊2 * x⌋ - 2 * ⌊x⌋ = 0 ∨ ⌊2 * x⌋ - 2 * ⌊x⌋ = 1 := by
  have hlo : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := by
    rw [Int.le_floor]; push_cast; linarith [Int.floor_le x]
  have hhi : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by
    rw [Int.floor_lt]; push_cast; linarith [Int.lt_floor_add_one x]
  omega

/-- **The cubic map correctly reads `W`'s base-2 digits** if some 3-periodic schedule `(c₀,c₁,c₂)`
makes the three-step cubic floor map send each binary block `uₙ = ⌊W·2ⁿ⌋` to the next, `uₙ₊₁ =
⌊W·2ⁿ⁺¹⌋`: i.e. `cubicV3(⌊W·2ⁿ⌋) = ⌊W·2ⁿ⁺¹⌋` for all `n`.  (This is the genuine self-referential
condition — the map *computes* `W`'s base-2 doubling — and is strictly stronger than merely emitting
valid digits.) -/
def CubicReadsBaseTwo (W : ℝ) : Prop :=
  ∃ c0 c1 c2 : ℝ, ∀ n : ℕ, cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ = ⌊W * 2 ^ (n + 1)⌋

/-- **The cubic three-step map computes no real's base-2 doubling, for almost every `W`.**  The
self-referential capstone: the set of `W` whose base-2 digits some fixed cubic schedule correctly reads
(`cubicV3(⌊W·2ⁿ⌋) = ⌊W·2ⁿ⁺¹⌋` ∀n) is Lebesgue-null.  Correct reading forces every emitted digit
`cubicV3(uₙ) − 2uₙ = ⌊W·2ⁿ⁺¹⌋ − 2⌊W·2ⁿ⌋ ∈ {0,1}` (`floor_two_mul_sub_mem`), i.e.
`CubicDigitRepresentable W`, which is a.e. false. -/
theorem ae_not_cubicReadsBaseTwo :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ CubicReadsBaseTwo W := by
  filter_upwards [ae_not_cubicDigitRepresentable] with W hW
  rintro ⟨c0, c1, c2, hread⟩
  refine hW ⟨c0, c1, c2, fun n => ?_⟩
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hdouble : ⌊W * 2 ^ (n + 1)⌋ = ⌊2 * (W * 2 ^ n)⌋ := by rw [hpow]; ring_nf
  rw [hread n, hdouble]
  have := floor_two_mul_sub_mem (W * 2 ^ n)
  rcases this with h | h
  · left; omega
  · right; omega

/-- **`W` is cubic-recurrence-representable** if some schedule `(c₀,c₁,c₂)` admits a genuine
*self-referential recurrence* orbit `orbit : ℕ → ℤ` — `orbit (n+1) = cubicV3(orbit n)` — that emits a
valid base-2 digit `cubicV3(orbit n) − 2·orbit n ∈ {0,1}` at every step, is not eventually all-`1`s
(`htail`, excluding the degenerate dyadic tail), and whose recovered binary value is `W`
(`W = orbit 0 + ∑ₖ dₖ·2^(−(k+1))`).  This is the impossibility phrased on the *actual recurrence* of the
cubic self-referential map, not on the externally-supplied floor orbit. -/
def CubicRecurrenceRepresentable (W : ℝ) : Prop :=
  ∃ (c0 c1 c2 : ℝ) (orbit : ℕ → ℤ),
    (∀ n, orbit (n + 1) = cubicV3 cbrt2 c0 c1 c2 (orbit n)) ∧
    (∀ n, cubicV3 cbrt2 c0 c1 c2 (orbit n) - 2 * orbit n = 0
        ∨ cubicV3 cbrt2 c0 c1 c2 (orbit n) - 2 * orbit n = 1) ∧
    (∀ N, ∃ k, N ≤ k ∧ cubicV3 cbrt2 c0 c1 c2 (orbit k) - 2 * orbit k = 0) ∧
    W = (orbit 0 : ℝ) + ∑' k : ℕ,
        ((cubicV3 cbrt2 c0 c1 c2 (orbit k) - 2 * orbit k : ℤ) : ℝ) * (1 / 2) ^ (k + 1)

/-- **Almost no real is cubic-recurrence-representable.**  The self-referential capstone on the genuine
recurrence: the set of `W` whose base-2 digits some cubic schedule reads along its *own* orbit
(`orbit(n+1)=cubicV3(orbit n)`) is Lebesgue-null.  The `binary_floor_eq` bridge identifies the recurrence
orbit with the floor orbit of its value (`orbit n = ⌊W·2ⁿ⌋`), reducing to `ae_not_cubicDigitRepresentable`. -/
theorem ae_not_cubicRecurrenceRepresentable :
    ∀ᵐ W ∂(volume : Measure ℝ), ¬ CubicRecurrenceRepresentable W := by
  filter_upwards [ae_not_cubicDigitRepresentable] with W hW
  rintro ⟨c0, c1, c2, orbit, hstep, hdig, htail, hWval⟩
  set d : ℕ → ℤ := fun k => cubicV3 cbrt2 c0 c1 c2 (orbit k) - 2 * orbit k with hd
  -- the recurrence orbit is a binary block orbit with digits `d`
  have hostep : ∀ n, orbit (n + 1) = 2 * orbit n + d n := by
    intro n; rw [hd]; simp only; rw [hstep n]; ring
  have hfloor : ∀ n, ⌊W * 2 ^ n⌋ = orbit n :=
    binary_floor_eq (orbit 0) d orbit hdig rfl hostep htail W hWval
  -- hence the floor orbit reads valid digits → cubic-digit-representable, a.e. false
  refine hW ⟨c0, c1, c2, fun n => ?_⟩
  rw [hfloor n]
  exact hdig n

end LeanGallery.NumberTheory.Erdos482.General
