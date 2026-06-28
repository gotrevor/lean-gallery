/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.CubicDefect
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The cubic defect as a function of the base-2 orbit point (toward the density contradiction)

`PENDING_WORK.md ★★` step (c) piece 4.  The cubic block orbit is `uₙ = ⌊W·2ⁿ⌋` (base-2,
`CubicDefect.cubic_block_orbit_base_two_bounds`).  We express the two internal floor errors `f₁, f₂` at
`uₙ` purely through the **canonical fractional coordinates** of the doubling orbit point
`(r₁, r₂, r₃) = ({W·2ⁿ}, {αW·2ⁿ}, {α²W·2ⁿ})`:

* `cubic_f1_orbit`:  `f₁ = {r₂ − α·r₁ + α·c₀}`,
* `cubic_f2_orbit`:  `f₂ = {r₃ − α²·r₁ − α·f₁ + α²c₀ + αc₁}`.

Hence the **partial defect** `g = α²f₁ + αf₂` (which, by `CubicDefect.cubic_partial_defect_mem_window`,
must lie in the width-2 window `(C−2, C]` for a digit-reading orbit) is a fixed function of
`(r₁, r₂, r₃)` — continuous away from the floor-jump surfaces.  As the orbit point ranges densely over
`T³` (`CubicTorusEquidist.ae_W_cubic_torus_orbit_dense`), `(f₁, f₂)` ranges over `[0,1)²`, so `g` ranges
over `[0, α²+α)` (width `> 2`), leaving the window — the unconditional a.e.-`W` contradiction.  This file
builds the algebraic half (the orbit-coordinate identities); the density/continuity finish remains.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **First floor error as a function of the orbit coordinates.**  For `u = ⌊W·2ⁿ⌋`, the first internal
floor error `f₁ = {α(u+c₀)}` equals `{r₂ − α·r₁ + αc₀}`, where `r₁ = {W·2ⁿ}` and `r₂ = {α·W·2ⁿ}` are the
canonical fractional coordinates of the first two doubling-orbit coordinates.  (Unwind `⌊W·2ⁿ⌋ = W·2ⁿ −
r₁` and drop the integer `⌊α·W·2ⁿ⌋` inside the fractional part.) -/
theorem cubic_f1_orbit (α c0 W : ℝ) (n : ℕ) :
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

/-- **Second floor error as a function of the orbit coordinates.**  For `u = ⌊W·2ⁿ⌋`, `v₁ = ⌊α(u+c₀)⌋`,
the second internal floor error `f₂ = {α(v₁+c₁)}` equals `{r₃ − α²·r₁ − α·f₁ + α²c₀ + αc₁}`, where
`r₃ = {α²·W·2ⁿ}` and `f₁ = {α(u+c₀)}` is the first floor error.  (Unwind `v₁ = α(u+c₀) − f₁` and
`u = W·2ⁿ − r₁`, then drop the integer `⌊α²·W·2ⁿ⌋`.) -/
theorem cubic_f2_orbit (α c0 c1 W : ℝ) (n : ℕ) :
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

/-- **The partial defect `g` along the base-2 orbit is an explicit function of the orbit coordinates.**
At `u = ⌊W·2ⁿ⌋`, `g = α²·{r₂ − αr₁ + αc₀} + α·{r₃ − α²r₁ − α{r₂ − αr₁ + αc₀} + α²c₀ + αc₁}`, where
`(r₁,r₂,r₃) = ({W·2ⁿ}, {αW·2ⁿ}, {α²W·2ⁿ})`.  Away from the floor-jump surfaces (where the inner
fractional parts are smooth) this is a continuous function of the doubling-orbit point; combined with the
density of that orbit (`CubicTorusEquidist.ae_W_cubic_torus_orbit_dense`) it ranges over `[0, α²+α)`
(width `> 2`), leaving the digit window `(C−2, C]` of `CubicDefect.cubic_partial_defect_mem_window`. -/
theorem cubicPartialDefect_orbit_eq (α c0 c1 c2 W : ℝ) (n : ℕ) :
    cubicPartialDefect α c0 c1 c2 (⌊W * 2 ^ n⌋)
      = α ^ 2 * Int.fract (Int.fract (α * (W * 2 ^ n)) - α * Int.fract (W * 2 ^ n) + α * c0)
        + α * Int.fract (Int.fract (α ^ 2 * (W * 2 ^ n)) - α ^ 2 * Int.fract (W * 2 ^ n)
            - α * Int.fract (Int.fract (α * (W * 2 ^ n)) - α * Int.fract (W * 2 ^ n) + α * c0)
            + α ^ 2 * c0 + α * c1) := by
  unfold cubicPartialDefect
  rw [cubic_f1_orbit, cubic_f2_orbit, cubic_f1_orbit]

/-- The partial defect, as a function of the three orbit fractional coordinates `(r₁,r₂,r₃)`. -/
noncomputable def cubicGpd (α c0 c1 r1 r2 r3 : ℝ) : ℝ :=
  α ^ 2 * Int.fract (r2 - α * r1 + α * c0)
    + α * Int.fract (r3 - α ^ 2 * r1 - α * Int.fract (r2 - α * r1 + α * c0) + α ^ 2 * c0 + α * c1)

/-- `cubicGpd` evaluated at the canonical orbit coordinates IS the partial defect at `⌊W·2ⁿ⌋`. -/
theorem cubicPartialDefect_eq_Gpd (α c0 c1 c2 W : ℝ) (n : ℕ) :
    cubicPartialDefect α c0 c1 c2 (⌊W * 2 ^ n⌋)
      = cubicGpd α c0 c1 (Int.fract (W * 2 ^ n)) (Int.fract (α * (W * 2 ^ n)))
          (Int.fract (α ^ 2 * (W * 2 ^ n))) :=
  cubicPartialDefect_orbit_eq α c0 c1 c2 W n

/-- **The partial-defect function `cubicGpd` is continuous at any point whose two internal `fract`
arguments are non-integers.**  (Affine maps are continuous and `Int.fract` is continuous off `ℤ`
— `continuousAt_fract` — so the composition is continuous at such points.)  At such a continuity
point the dense cubic orbit realizes defect values arbitrarily close to `cubicGpd`'s value
(`EquidistDense.exists_lt_of_dense_continuousAt`); choosing the point so the value leaves the digit
window `(C−2, C]` finishes the a.e.-`W` cubic impossibility. -/
theorem continuousAt_cubicGpd (α c0 c1 : ℝ) (p : ℝ × ℝ × ℝ)
    (hA : p.2.1 - α * p.1 + α * c0 ≠ (⌊p.2.1 - α * p.1 + α * c0⌋ : ℤ))
    (hB : p.2.2 - α ^ 2 * p.1
            - α * Int.fract (p.2.1 - α * p.1 + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊p.2.2 - α ^ 2 * p.1
                - α * Int.fract (p.2.1 - α * p.1 + α * c0) + α ^ 2 * c0 + α * c1⌋ : ℤ)) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => cubicGpd α c0 c1 q.1 q.2.1 q.2.2) p := by
  have hcoord : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.1) p := continuous_fst.continuousAt
  have hcoord2 : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.1) p :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hcoord3 : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2) p :=
    (continuous_snd.comp continuous_snd).continuousAt
  have hAmap : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.1 - α * q.1 + α * c0) p := by fun_prop
  have hfractA : ContinuousAt
      (fun q : ℝ × ℝ × ℝ => Int.fract (q.2.1 - α * q.1 + α * c0)) p :=
    ContinuousAt.comp (g := Int.fract) (f := fun q : ℝ × ℝ × ℝ => q.2.1 - α * q.1 + α * c0)
      (continuousAt_fract hA) hAmap
  have hBmap : ContinuousAt
      (fun q : ℝ × ℝ × ℝ => q.2.2 - α ^ 2 * q.1
          - α * Int.fract (q.2.1 - α * q.1 + α * c0) + α ^ 2 * c0 + α * c1) p := by
    apply ContinuousAt.add
    apply ContinuousAt.add
    apply ContinuousAt.sub
    · exact (hcoord3.sub (hcoord.const_mul (α ^ 2)))
    · exact hfractA.const_mul α
    · exact continuousAt_const
    · exact continuousAt_const
  have hfractB : ContinuousAt
      (fun q : ℝ × ℝ × ℝ => Int.fract (q.2.2 - α ^ 2 * q.1
          - α * Int.fract (q.2.1 - α * q.1 + α * c0) + α ^ 2 * c0 + α * c1)) p :=
    ContinuousAt.comp (g := Int.fract)
      (f := fun q : ℝ × ℝ × ℝ => q.2.2 - α ^ 2 * q.1
          - α * Int.fract (q.2.1 - α * q.1 + α * c0) + α ^ 2 * c0 + α * c1)
      (continuousAt_fract hB) hBmap
  exact (hfractA.const_mul (α ^ 2)).add (hfractB.const_mul α)

end LeanGallery.NumberTheory.Erdos482.General
