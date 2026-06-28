/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The quartic four-step self-referential floor map (degree-4 generalization, foundations)

Generalizing `CubicDefect` from `α = 2^{1/3}` (3 steps) to `α = 2^{1/4}` (4 steps).  The four-step map
`v₁=⌊α(u+c₀)⌋`, `v₂=⌊α(v₁+c₁)⌋`, `v₃=⌊α(v₂+c₂)⌋`, `v₄=⌊α(v₃+c₃)⌋` reads base-2 digits iff
`v₄ − 2u ∈ {0,1}` for every block `u = ⌊W·2ⁿ⌋` (note `α⁴ = 2`, so four steps multiply by `2`).

This file ports the *algebraic backbone*: the four-step defect identity (`quartic_fourstep_defect`), the
digit bridge (`quarticV4_sub_eq`), and the combined-defect range-width obstruction
(`quartic_combined_defect_range_wide`).  The analytic finish (a.e.-`W` `T⁴` equidistribution + geometry)
reuses the already-general `MultidimWeyl`/`EquidistDense`/`DELEngine` machinery and the
`quartic_lin_indep_int` backbone (in progress); see `PENDING_WORK.md`.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

noncomputable section

/-- `α = 2^{1/4}` (the quartic multiplier; `α⁴ = 2`). -/
abbrev qrt2 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)

/-- `qrt2 ^ 4 = 2`. -/
theorem qrt2_quartic : qrt2 ^ 4 = 2 := by
  rw [qrt2, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `1 < qrt2`. -/
theorem one_lt_qrt2 : 1 < qrt2 := by
  rw [qrt2, Real.one_lt_rpow_iff_of_pos (by norm_num)]
  left; constructor <;> norm_num

/-- **The quartic four-step defect identity.**  For any `α` with `α⁴ = 2`, offsets `c₀ c₁ c₂ c₃` and
start `u`, the four-step floor map satisfies
`v₄ = 2u + (2c₀ + α³c₁ + α²c₂ + αc₃) − (α³·f₁ + α²·f₂ + α·f₃ + f₄)`,
where `fᵢ` are the four internal floor errors.  Pure algebra from `α⁴ = 2`. -/
theorem quartic_fourstep_defect (α u c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) :
    let v1 : ℝ := (⌊α * (u + c0)⌋ : ℤ)
    let v2 : ℝ := (⌊α * (v1 + c1)⌋ : ℤ)
    let v3 : ℝ := (⌊α * (v2 + c2)⌋ : ℤ)
    let v4 : ℝ := (⌊α * (v3 + c3)⌋ : ℤ)
    v4 = 2 * u + (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3)
        - (α ^ 3 * Int.fract (α * (u + c0)) + α ^ 2 * Int.fract (α * (v1 + c1))
            + α * Int.fract (α * (v2 + c2)) + Int.fract (α * (v3 + c3))) := by
  intro v1 v2 v3 v4
  have h1 : v1 = α * (u + c0) - Int.fract (α * (u + c0)) := (Int.self_sub_fract _).symm
  have h2 : v2 = α * (v1 + c1) - Int.fract (α * (v1 + c1)) := (Int.self_sub_fract _).symm
  have h3 : v3 = α * (v2 + c2) - Int.fract (α * (v2 + c2)) := (Int.self_sub_fract _).symm
  have h4 : v4 = α * (v3 + c3) - Int.fract (α * (v3 + c3)) := (Int.self_sub_fract _).symm
  linear_combination h4 + α * h3 + α ^ 2 * h2 + α ^ 3 * h1 + (u + c0) * hα

/-- The four-step quartic orbit value `v₄ = ⌊α(⌊α(⌊α(⌊α(u+c₀)⌋+c₁)⌋+c₂)⌋+c₃)⌋` from integer start `u`. -/
noncomputable def quarticV4 (α c0 c1 c2 c3 : ℝ) (u : ℤ) : ℤ :=
  ⌊α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ) + c3)⌋

/-- The combined internal-floor defect `α³f₁ + α²f₂ + αf₃ + f₄` of the four-step map at start `u`. -/
noncomputable def quarticDefect (α c0 c1 c2 c3 : ℝ) (u : ℤ) : ℝ :=
  α ^ 3 * Int.fract (α * ((u : ℝ) + c0))
    + α ^ 2 * Int.fract (α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
    + α * Int.fract (α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2))
    + Int.fract (α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ) + c3))

/-- **Digit bridge.**  The extracted digit `quarticV4 − 2u` equals the schedule constant minus the
combined defect: `(2c₀ + α³c₁ + α²c₂ + αc₃) − quarticDefect`. -/
theorem quarticV4_sub_eq (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ) :
    ((quarticV4 α c0 c1 c2 c3 u : ℤ) : ℝ) - 2 * (u : ℝ)
      = (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) - quarticDefect α c0 c1 c2 c3 u := by
  have hd := quartic_fourstep_defect α (u : ℝ) c0 c1 c2 c3 hα
  simp only [quarticV4, quarticDefect]
  linarith [hd]

/-- **The combined four-floor defect does not fit any width-2 window** (for any `α > 1`).  As
`(f₁,f₂,f₃,f₄)` ranges over `[0,1)⁴`, the combined defect `α³f₁ + α²f₂ + αf₃ + f₄` cannot be confined to
a closed interval `[C, C+2]` of length 2.  Witnesses `(0,0,0,0) ↦ 0` and `(½,½,½,½) ↦ (α³+α²+α+1)/2`
already differ by more than `2`, since `α³+α²+α+1 > 4` requires only... actually for `α = 2^{1/4} ≈ 1.19`,
`α³+α²+α+1 ≈ 5.28 > 4`.  The clean sufficient bound used here is `1 < α` ⇒ this is the analogue of the
cubic `cubic_combined_defect_range_wide`; a base-2 readout needs the defect in a width-2 window
(`digit ∈ {0,1} ⟺ C−defect ∈ [0,2)`), so a wider range obstructs every fixed schedule. -/
theorem quartic_combined_defect_range_wide (α : ℝ) (hα1 : 1 < α) :
    ¬ ∃ C : ℝ, ∀ f1 f2 f3 f4 : ℝ, 0 ≤ f1 → f1 < 1 → 0 ≤ f2 → f2 < 1 → 0 ≤ f3 → f3 < 1 →
        0 ≤ f4 → f4 < 1 →
      α ^ 3 * f1 + α ^ 2 * f2 + α * f3 + f4 ∈ Set.Icc C (C + 2) := by
  rintro ⟨C, hC⟩
  have h0 := hC 0 0 0 0 le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    (by norm_num)
  have hh := hC (1 / 2) (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Set.mem_Icc] at h0 hh
  -- need α³+α²+α+1 > 4 from α>1; since α>1 ⇒ α³>1, α²>1, α>1, sum+1 > 4
  nlinarith [h0.1, h0.2, hh.1, hh.2, hα1, mul_pos (show (0:ℝ) < α by linarith) (show (0:ℝ) < α by linarith),
    mul_pos (mul_pos (show (0:ℝ) < α by linarith) (show (0:ℝ) < α by linarith))
      (show (0:ℝ) < α by linarith)]

/-- The quartic obstruction is base-`2`, multiplier `2^{1/4}`. -/
theorem quartic_combined_defect_range_wide_qrt2 :
    ¬ ∃ C : ℝ, ∀ f1 f2 f3 f4 : ℝ, 0 ≤ f1 → f1 < 1 → 0 ≤ f2 → f2 < 1 → 0 ≤ f3 → f3 < 1 →
        0 ≤ f4 → f4 < 1 →
      qrt2 ^ 3 * f1 + qrt2 ^ 2 * f2 + qrt2 * f3 + f4 ∈ Set.Icc C (C + 2) :=
  quartic_combined_defect_range_wide qrt2 one_lt_qrt2

/-! ### The defect collapse: the fourth floor error is forced, and the digit is `⌊C − g⌋`.

Mirrors the cubic `g`-collapse (`CubicDefect.cubic_f3_eq` … `cubic_partial_defect_mem_window`).  The
*three*-floor partial defect `g = α³f₁ + α²f₂ + αf₃` (the first three internal errors) governs the whole
quartic readout: the fourth error is forced `f₄ = {C − g}`, the extracted digit is `⌊C − g⌋`, and a
base-2 digit confines `g` to the width-2 window `(C−2, C]`.  Since `g` ranges over `[0, α³+α²+α)` with
width `α³+α²+α ≈ 4.28 > 2`, an orbit exploring that range leaves the window. -/

/-- The **three-floor partial defect** `g = α³f₁ + α²f₂ + αf₃` of the four-step map. -/
noncomputable def quarticPartialDefect (α c0 c1 c2 _c3 : ℝ) (u : ℤ) : ℝ :=
  α ^ 3 * Int.fract (α * ((u : ℝ) + c0))
    + α ^ 2 * Int.fract (α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
    + α * Int.fract (α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2))

/-- **The fourth floor error is forced**: `f₄ = {C − g}`, `C = 2c₀+α³c₁+α²c₂+αc₃`, `g` the partial
defect.  (Because `α(v₃+c₃) = 2u + C − g` with `2u ∈ ℤ`.)  Pure algebra from `α⁴ = 2`. -/
theorem quartic_f4_eq (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ) :
    Int.fract (α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ) + c3))
      = Int.fract ((2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3)
          - quarticPartialDefect α c0 c1 c2 c3 u) := by
  have harg : α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ) + c3)
      = ((2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) - quarticPartialDefect α c0 c1 c2 c3 u)
        + 2 * (u : ℝ) := by
    simp only [quarticPartialDefect]
    have hv1 : ((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ)
        = α * ((u : ℝ) + c0) - Int.fract (α * ((u : ℝ) + c0)) := (Int.self_sub_fract _).symm
    have hv2 : ((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ)
        = α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)
            - Int.fract (α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)) := (Int.self_sub_fract _).symm
    have hv3 : ((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ)
        = α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)
            - Int.fract (α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)) :=
      (Int.self_sub_fract _).symm
    linear_combination α * hv3 + α ^ 2 * hv2 + α ^ 3 * hv1 + (u + c0) * hα
  rw [harg, show (2 * (u : ℝ)) = ((2 * u : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]

/-- **The combined defect collapses to a floor of the partial defect**: `quarticDefect = C − ⌊C − g⌋`. -/
theorem quarticDefect_eq_C_sub_floor (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ) :
    quarticDefect α c0 c1 c2 c3 u
      = (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3)
        - (⌊(2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3)
            - quarticPartialDefect α c0 c1 c2 c3 u⌋ : ℤ) := by
  have hsplit : quarticDefect α c0 c1 c2 c3 u
      = quarticPartialDefect α c0 c1 c2 c3 u
        + Int.fract (α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ)
            + c2)⌋ : ℤ) : ℝ) + c3)) := by
    simp only [quarticDefect, quarticPartialDefect]
  rw [hsplit, quartic_f4_eq α c0 c1 c2 c3 hα u]
  simp only [Int.fract]; ring_nf

/-- **The extracted digit is a floor of the partial defect**: `quarticV4 − 2u = ⌊C − g⌋`. -/
theorem quartic_digit_eq_floor (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ) :
    quarticV4 α c0 c1 c2 c3 u - 2 * u
      = ⌊(2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) - quarticPartialDefect α c0 c1 c2 c3 u⌋ := by
  have h1 := quarticV4_sub_eq α c0 c1 c2 c3 hα u
  rw [quarticDefect_eq_C_sub_floor α c0 c1 c2 c3 hα u] at h1
  have hr : ((quarticV4 α c0 c1 c2 c3 u - 2 * u : ℤ) : ℝ)
      = ((⌊(2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3)
          - quarticPartialDefect α c0 c1 c2 c3 u⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast hr

/-- **A base-2 digit confines the partial defect to a width-2 window**: if `quarticV4 − 2u ∈ {0,1}` then
`g = α³f₁+α²f₂+αf₃ ∈ (C−2, C]`.  Since the partial-defect range `[0, α³+α²+α)` has width `> 2`, an orbit
that explored it would leave this window — the quartic analogue of `cubic_partial_defect_mem_window`. -/
theorem quartic_partial_defect_mem_window (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ)
    (hdig : quarticV4 α c0 c1 c2 c3 u - 2 * u = 0 ∨ quarticV4 α c0 c1 c2 c3 u - 2 * u = 1) :
    (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) - 2 < quarticPartialDefect α c0 c1 c2 c3 u
      ∧ quarticPartialDefect α c0 c1 c2 c3 u ≤ (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) := by
  have hfloor := quartic_digit_eq_floor α c0 c1 c2 c3 hα u
  set C := 2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3 with hC
  rw [hfloor] at hdig
  have hle : ((⌊C - quarticPartialDefect α c0 c1 c2 c3 u⌋ : ℤ) : ℝ)
      ≤ C - quarticPartialDefect α c0 c1 c2 c3 u := Int.floor_le _
  have hlt : C - quarticPartialDefect α c0 c1 c2 c3 u
      < (⌊C - quarticPartialDefect α c0 c1 c2 c3 u⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  rcases hdig with h | h <;> rw [h] at hle hlt <;> push_cast at hle hlt <;> constructor <;> linarith

/-! ### ℤ-linear independence of `{1, 2^{1/4}, 2^{2/4}, 2^{3/4}}` (the quartic algebraic backbone). -/

/-- **Infinite 2-adic descent.**  The only integer solution of the "norm" system
`4be = a²+2c²`, `b²+2e² = 2ac` is the trivial one.  (These are exactly the conditions forced by squaring
an integer relation `α(b+e√2) = −(a+c√2)`; their only solution being trivial is `2^{1/4} ∉ ℚ(√2)`.)
Proof by descent: `(a,b,c,e)` all even, and `(a/2,b/2,c/2,e/2)` satisfy the same system. -/
private theorem quartic_norm_descent : ∀ n : ℕ, ∀ a b c e : ℤ,
    a.natAbs + b.natAbs + c.natAbs + e.natAbs = n →
    4 * b * e = a ^ 2 + 2 * c ^ 2 → b ^ 2 + 2 * e ^ 2 = 2 * a * c →
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c e hn hI hII
    have hEb : Even b := by
      have h2 : Even (b ^ 2) := ⟨a * c - e ^ 2, by linarith [hII]⟩
      exact (Int.even_pow.mp h2).1
    have hEa : Even a := by
      have h2 : Even (a ^ 2) := ⟨2 * b * e - c ^ 2, by linarith [hI]⟩
      exact (Int.even_pow.mp h2).1
    obtain ⟨a1, rfl⟩ := hEa
    obtain ⟨b1, rfl⟩ := hEb
    have hEe : Even e := by
      have h2 : Even (e ^ 2) := ⟨a1 * c - b1 ^ 2, by nlinarith [hII]⟩
      exact (Int.even_pow.mp h2).1
    have hEc : Even c := by
      have h2 : Even (c ^ 2) := ⟨2 * b1 * e - a1 ^ 2, by nlinarith [hI]⟩
      exact (Int.even_pow.mp h2).1
    obtain ⟨e1, rfl⟩ := hEe
    obtain ⟨c1, rfl⟩ := hEc
    have hI1 : 4 * b1 * e1 = a1 ^ 2 + 2 * c1 ^ 2 := by nlinarith [hI]
    have hII1 : b1 ^ 2 + 2 * e1 ^ 2 = 2 * a1 * c1 := by nlinarith [hII]
    -- the halved tuple has half the size; descend
    have hsum : a1.natAbs + b1.natAbs + c1.natAbs + e1.natAbs
        + (a1.natAbs + b1.natAbs + c1.natAbs + e1.natAbs) = n := by
      have e2 : ∀ x : ℤ, (x + x).natAbs = x.natAbs + x.natAbs := by
        intro x; rw [← two_mul, Int.natAbs_mul]; simp [Nat.two_mul]
      rw [e2, e2, e2, e2] at hn; omega
    by_cases hz : a1.natAbs + b1.natAbs + c1.natAbs + e1.natAbs = 0
    · have ha0 : a1 = 0 := Int.natAbs_eq_zero.mp (by omega)
      have hb0 : b1 = 0 := Int.natAbs_eq_zero.mp (by omega)
      have hc0 : c1 = 0 := Int.natAbs_eq_zero.mp (by omega)
      have he0 : e1 = 0 := Int.natAbs_eq_zero.mp (by omega)
      subst ha0; subst hb0; subst hc0; subst he0
      refine ⟨by ring, by ring, by ring, by ring⟩
    · have hlt : a1.natAbs + b1.natAbs + c1.natAbs + e1.natAbs < n := by omega
      obtain ⟨ha, hb, hc, he⟩ := ih _ hlt a1 b1 c1 e1 rfl hI1 hII1
      subst ha; subst hb; subst hc; subst he; refine ⟨by ring, by ring, by ring, by ring⟩

/-- **`{1, α, α², α³}` with `α = 2^{1/4}` are ℤ-linearly independent.**  The only integer relation
`a + b·α + c·α² + e·α³ = 0` is the trivial one — the degree-4 analogue of `cubic_lin_indep_int`, and the
algebraic backbone for the quartic self-referential impossibility.  (Group as `(a+c√2) + α(b+e√2) = 0`;
square and split off `√2` (irrational) to get the norm system `quartic_norm_descent` kills.) -/
theorem quartic_lin_indep_int (a b c e : ℤ)
    (h : (a : ℝ) + (b : ℝ) * qrt2 + (c : ℝ) * qrt2 ^ 2 + (e : ℝ) * qrt2 ^ 3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  -- `t = α² = √2` is irrational and `t² = 2`.
  have ht : qrt2 ^ 2 = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, qrt2, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hirr : Irrational (qrt2 ^ 2) := ht ▸ irrational_sqrt_two
  have e4 : qrt2 ^ 2 * qrt2 ^ 2 = 2 := by rw [← pow_add]; exact_mod_cast qrt2_quartic
  -- regroup `a + b α + c α² + e α³ = 0` as `α (b + e α²) = −(a + c α²)`
  have h3 : qrt2 ^ 3 = qrt2 * qrt2 ^ 2 := by ring
  rw [h3] at h
  have hg : qrt2 * ((b : ℝ) + (e : ℝ) * qrt2 ^ 2) = -((a : ℝ) + (c : ℝ) * qrt2 ^ 2) := by
    linear_combination h
  -- square and use `α⁴ = 2`: `(4be − (a²+2c²)) + (b²+2e² − 2ac)·α² = 0`
  have hsq : qrt2 ^ 2 * ((b : ℝ) + (e : ℝ) * qrt2 ^ 2) ^ 2 = ((a : ℝ) + (c : ℝ) * qrt2 ^ 2) ^ 2 := by
    rw [← mul_pow, hg]; ring
  have hPQ : (((4 * b * e - (a ^ 2 + 2 * c ^ 2) : ℤ)) : ℝ)
      + (((b ^ 2 + 2 * e ^ 2 - 2 * a * c : ℤ)) : ℝ) * qrt2 ^ 2 = 0 := by
    push_cast
    linear_combination hsq + ((c : ℝ) ^ 2 - 2 * (b : ℝ) * (e : ℝ) - (e : ℝ) ^ 2 * qrt2 ^ 2) * e4
  -- `α²` irrational ⇒ the integer coefficient of `α²` vanishes, hence so does the constant
  have hQ : (b ^ 2 + 2 * e ^ 2 - 2 * a * c : ℤ) = 0 := by
    by_contra hQne
    have hIrr2 := hirr.intCast_mul hQne
    have hIrr3 := hIrr2.intCast_add (4 * b * e - (a ^ 2 + 2 * c ^ 2))
    rw [hPQ] at hIrr3
    exact not_irrational_zero hIrr3
  have hP : (4 * b * e - (a ^ 2 + 2 * c ^ 2) : ℤ) = 0 := by
    have hQ0 : (((b ^ 2 + 2 * e ^ 2 - 2 * a * c : ℤ)) : ℝ) = 0 := by exact_mod_cast hQ
    rw [hQ0, zero_mul, add_zero] at hPQ
    exact_mod_cast hPQ
  exact quartic_norm_descent _ a b c e rfl (by linarith [hP]) (by linarith [hQ])

end

end LeanGallery.NumberTheory.Erdos482.General
