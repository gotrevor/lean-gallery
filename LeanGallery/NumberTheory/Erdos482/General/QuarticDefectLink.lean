/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.QuarticDefect
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The quartic partial defect as a function of the base-2 orbit point (degree-4 generalization)

Degree-4 analogue of `CubicDefectLink`.  The four-step block orbit is `uₙ = ⌊W·2ⁿ⌋`; we express the
three internal floor errors `f₁, f₂, f₃` at `uₙ` through the canonical fractional coordinates of the
doubling orbit point `(r₁,r₂,r₃,r₄) = ({W·2ⁿ}, {αW·2ⁿ}, {α²W·2ⁿ}, {α³W·2ⁿ})`:

* `quartic_f1_orbit`:  `f₁ = {r₂ − α·r₁ + α·c₀}`,
* `quartic_f2_orbit`:  `f₂ = {r₃ − α²·r₁ − α·f₁ + α²c₀ + αc₁}`,
* `quartic_f3_orbit`:  `f₃ = {r₄ − α³·r₁ − α²·f₁ − α·f₂ + α³c₀ + α²c₁ + αc₂}`.

Hence the three-floor partial defect `g = α³f₁ + α²f₂ + αf₃` is a fixed function `quarticGpd` of
`(r₁,r₂,r₃,r₄)`, continuous away from the floor-jump surfaces.  As the orbit point ranges densely over
`T⁴` (the `T⁴` equidistribution, parallel to the cubic), `g` ranges over `[0, α³+α²+α)` (width `> 2`),
leaving the window of `QuarticDefect.quartic_partial_defect_mem_window` — the unconditional a.e.-`W`
quartic contradiction.  This file builds the algebraic half (the orbit-coordinate identities + `quarticGpd`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **First floor error as a function of the orbit coordinates.**  `f₁ = {α(u+c₀)} = {r₂ − α·r₁ + αc₀}`. -/
theorem quartic_f1_orbit (α c0 W : ℝ) (n : ℕ) :
    Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0))
      = Int.fract (Int.fract (α * (W * 2 ^ n)) - α * Int.fract (W * 2 ^ n) + α * c0) := by
  have e : α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)
      = (Int.fract (α * (W * 2 ^ n)) - α * Int.fract (W * 2 ^ n) + α * c0)
        + ((⌊α * (W * 2 ^ n)⌋ : ℤ) : ℝ) := by
    have h1 : ((⌊W * 2 ^ n⌋ : ℤ) : ℝ) = W * 2 ^ n - Int.fract (W * 2 ^ n) :=
      (Int.self_sub_fract _).symm
    have h2 : Int.fract (α * (W * 2 ^ n)) + ((⌊α * (W * 2 ^ n)⌋ : ℤ) : ℝ) = α * (W * 2 ^ n) :=
      Int.fract_add_floor _
    linear_combination α * h1 - h2
  rw [e, Int.fract_add_intCast]

/-- **Second floor error as a function of the orbit coordinates.**
`f₂ = {α(v₁+c₁)} = {r₃ − α²·r₁ − α·f₁ + α²c₀ + αc₁}`. -/
theorem quartic_f2_orbit (α c0 c1 W : ℝ) (n : ℕ) :
    Int.fract (α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
      = Int.fract (Int.fract (α ^ 2 * (W * 2 ^ n)) - α ^ 2 * Int.fract (W * 2 ^ n)
          - α * Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)) + α ^ 2 * c0 + α * c1) := by
  have e : α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)
      = (Int.fract (α ^ 2 * (W * 2 ^ n)) - α ^ 2 * Int.fract (W * 2 ^ n)
          - α * Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)) + α ^ 2 * c0 + α * c1)
        + ((⌊α ^ 2 * (W * 2 ^ n)⌋ : ℤ) : ℝ) := by
    have hu : ((⌊W * 2 ^ n⌋ : ℤ) : ℝ) = W * 2 ^ n - Int.fract (W * 2 ^ n) :=
      (Int.self_sub_fract _).symm
    have hv1 : ((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ)
        = α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0) - Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)) :=
      (Int.self_sub_fract _).symm
    have h3 : Int.fract (α ^ 2 * (W * 2 ^ n)) + ((⌊α ^ 2 * (W * 2 ^ n)⌋ : ℤ) : ℝ)
        = α ^ 2 * (W * 2 ^ n) := Int.fract_add_floor _
    linear_combination α * hv1 + α ^ 2 * hu - h3
  rw [e, Int.fract_add_intCast]

/-- **Third floor error as a function of the orbit coordinates.**
`f₃ = {α(v₂+c₂)} = {r₄ − α³·r₁ − α²·f₁ − α·f₂ + α³c₀ + α²c₁ + αc₂}`. -/
theorem quartic_f3_orbit (α c0 c1 c2 W : ℝ) (n : ℕ) :
    Int.fract (α * (((⌊α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2))
      = Int.fract (Int.fract (α ^ 3 * (W * 2 ^ n)) - α ^ 3 * Int.fract (W * 2 ^ n)
          - α ^ 2 * Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0))
          - α * Int.fract (α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
          + α ^ 3 * c0 + α ^ 2 * c1 + α * c2) := by
  have e : α * (((⌊α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)
      = (Int.fract (α ^ 3 * (W * 2 ^ n)) - α ^ 3 * Int.fract (W * 2 ^ n)
          - α ^ 2 * Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0))
          - α * Int.fract (α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
          + α ^ 3 * c0 + α ^ 2 * c1 + α * c2)
        + ((⌊α ^ 3 * (W * 2 ^ n)⌋ : ℤ) : ℝ) := by
    have hu : ((⌊W * 2 ^ n⌋ : ℤ) : ℝ) = W * 2 ^ n - Int.fract (W * 2 ^ n) :=
      (Int.self_sub_fract _).symm
    have hv1 : ((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ)
        = α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0) - Int.fract (α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)) :=
      (Int.self_sub_fract _).symm
    have hv2 : ((⌊α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ)
        = α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)
            - Int.fract (α * (((⌊α * (((⌊W * 2 ^ n⌋ : ℤ) : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)) :=
      (Int.self_sub_fract _).symm
    have h4 : Int.fract (α ^ 3 * (W * 2 ^ n)) + ((⌊α ^ 3 * (W * 2 ^ n)⌋ : ℤ) : ℝ)
        = α ^ 3 * (W * 2 ^ n) := Int.fract_add_floor _
    linear_combination α * hv2 + α ^ 2 * hv1 + α ^ 3 * hu - h4
  rw [e, Int.fract_add_intCast]

/-- The partial defect `g` along the base-2 orbit, as a function of the four orbit coordinates. -/
noncomputable def quarticGpd (α c0 c1 c2 r1 r2 r3 r4 : ℝ) : ℝ :=
  α ^ 3 * Int.fract (r2 - α * r1 + α * c0)
    + α ^ 2 * Int.fract (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1)
    + α * Int.fract (r4 - α ^ 3 * r1 - α ^ 2 * Int.fract (r2 - α * r1 + α * c0)
        - α * Int.fract (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1)
        + α ^ 3 * c0 + α ^ 2 * c1 + α * c2)

/-- **`quarticGpd` at the canonical orbit coordinates IS the partial defect at `⌊W·2ⁿ⌋`.** -/
theorem quarticPartialDefect_eq_Gpd (α c0 c1 c2 c3 W : ℝ) (n : ℕ) :
    quarticPartialDefect α c0 c1 c2 c3 (⌊W * 2 ^ n⌋)
      = quarticGpd α c0 c1 c2 (Int.fract (W * 2 ^ n)) (Int.fract (α * (W * 2 ^ n)))
          (Int.fract (α ^ 2 * (W * 2 ^ n))) (Int.fract (α ^ 3 * (W * 2 ^ n))) := by
  unfold quarticPartialDefect quarticGpd
  rw [quartic_f1_orbit, quartic_f2_orbit, quartic_f3_orbit, quartic_f1_orbit, quartic_f2_orbit,
    quartic_f1_orbit]

/-- **`quarticGpd` is continuous at any point whose three internal `fract` arguments are non-integers.**
(Affine maps are continuous and `Int.fract` is continuous off `ℤ` — `continuousAt_fract` — so the
3-level composition is continuous at such points.)  Degree-4 analogue of `continuousAt_cubicGpd`. -/
theorem continuousAt_quarticGpd (α c0 c1 c2 : ℝ) (p : ℝ × ℝ × ℝ × ℝ)
    (hA : p.2.1 - α * p.1 + α * c0 ≠ (⌊p.2.1 - α * p.1 + α * c0⌋ : ℤ))
    (hB : p.2.2.1 - α ^ 2 * p.1 - α * Int.fract (p.2.1 - α * p.1 + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊p.2.2.1 - α ^ 2 * p.1 - α * Int.fract (p.2.1 - α * p.1 + α * c0)
                + α ^ 2 * c0 + α * c1⌋ : ℤ))
    (hC : p.2.2.2 - α ^ 3 * p.1 - α ^ 2 * Int.fract (p.2.1 - α * p.1 + α * c0)
            - α * Int.fract (p.2.2.1 - α ^ 2 * p.1 - α * Int.fract (p.2.1 - α * p.1 + α * c0)
                + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2
          ≠ (⌊p.2.2.2 - α ^ 3 * p.1 - α ^ 2 * Int.fract (p.2.1 - α * p.1 + α * c0)
                - α * Int.fract (p.2.2.1 - α ^ 2 * p.1 - α * Int.fract (p.2.1 - α * p.1 + α * c0)
                    + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2⌋ : ℤ)) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => quarticGpd α c0 c1 c2 q.1 q.2.1 q.2.2.1 q.2.2.2) p := by
  have hc1 : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => q.1) p := continuous_fst.continuousAt
  have hc2 : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => q.2.1) p :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hc3 : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1) p :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
  have hc4 : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.2) p :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt
  have hAmap : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => q.2.1 - α * q.1 + α * c0) p := by fun_prop
  have hfractA : ContinuousAt
      (fun q : ℝ × ℝ × ℝ × ℝ => Int.fract (q.2.1 - α * q.1 + α * c0)) p :=
    ContinuousAt.comp (g := Int.fract) (f := fun q : ℝ × ℝ × ℝ × ℝ => q.2.1 - α * q.1 + α * c0)
      (continuousAt_fract hA) hAmap
  have hBmap : ContinuousAt
      (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1 - α ^ 2 * q.1
          - α * Int.fract (q.2.1 - α * q.1 + α * c0) + α ^ 2 * c0 + α * c1) p := by
    refine ((((hc3.sub (hc1.const_mul (α ^ 2))).sub (hfractA.const_mul α)).add
      continuousAt_const).add continuousAt_const)
  have hfractB : ContinuousAt
      (fun q : ℝ × ℝ × ℝ × ℝ => Int.fract (q.2.2.1 - α ^ 2 * q.1
          - α * Int.fract (q.2.1 - α * q.1 + α * c0) + α ^ 2 * c0 + α * c1)) p :=
    ContinuousAt.comp (g := Int.fract)
      (f := fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1 - α ^ 2 * q.1
          - α * Int.fract (q.2.1 - α * q.1 + α * c0) + α ^ 2 * c0 + α * c1)
      (continuousAt_fract hB) hBmap
  have hCmap : ContinuousAt
      (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.2 - α ^ 3 * q.1
          - α ^ 2 * Int.fract (q.2.1 - α * q.1 + α * c0)
          - α * Int.fract (q.2.2.1 - α ^ 2 * q.1 - α * Int.fract (q.2.1 - α * q.1 + α * c0)
              + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2) p := by
    refine (((((hc4.sub (hc1.const_mul (α ^ 3))).sub (hfractA.const_mul (α ^ 2))).sub
      (hfractB.const_mul α)).add continuousAt_const).add continuousAt_const).add continuousAt_const
  have hfractC : ContinuousAt
      (fun q : ℝ × ℝ × ℝ × ℝ => Int.fract (q.2.2.2 - α ^ 3 * q.1
          - α ^ 2 * Int.fract (q.2.1 - α * q.1 + α * c0)
          - α * Int.fract (q.2.2.1 - α ^ 2 * q.1 - α * Int.fract (q.2.1 - α * q.1 + α * c0)
              + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2)) p :=
    ContinuousAt.comp (g := Int.fract)
      (f := fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.2 - α ^ 3 * q.1
          - α ^ 2 * Int.fract (q.2.1 - α * q.1 + α * c0)
          - α * Int.fract (q.2.2.1 - α ^ 2 * q.1 - α * Int.fract (q.2.1 - α * q.1 + α * c0)
              + α ^ 2 * c0 + α * c1) + α ^ 3 * c0 + α ^ 2 * c1 + α * c2)
      (continuousAt_fract hC) hCmap
  exact ((hfractA.const_mul (α ^ 3)).add (hfractB.const_mul (α ^ 2))).add (hfractC.const_mul α)

end LeanGallery.NumberTheory.Erdos482.General
