/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.GeneralDefect
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The general degree-`d` floor errors as functions of the doubling-orbit coordinates

**Context (the general-`d` analytic bridge).**  `GeneralDefect.lean` reduces the `d`-step impossibility
to the partial defect `g = ∑_{k<d-1} α^{d-1-k} fₖ` of the floor errors `fₖ` at the integer start
`u = ⌊W·2ⁿ⌋`.  To run the equidistribution argument we must express each `fₖ` as a function of the
`Tᵈ` doubling-orbit coordinates `rᵢ = {αⁱ·W·2ⁿ}`.

**This file proves that orbit-coordinate form uniformly for every `k`** (`dStepF_orbit`), the
degree-agnostic analogue of `cubic_f1_orbit`/`cubic_f2_orbit`.  The clean route is the affine-recurrence
closed form (`affine_rec_closed`): since
`α(vₖ + cₖ) = α^{k+1}⌊W2ⁿ⌋ + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ`
and `α^{k+1}⌊W2ⁿ⌋ = ⌊α^{k+1}W2ⁿ⌋ + {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ}`, dropping the integer floor gives
`fₖ = { {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ} + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ }`.
No fresh induction is needed — `affine_rec_closed` already did it.

This is the entry point to the remaining analytic `Tᵈ`-assembly (density + the geometry crux
`exists_partial_defect_outside_window`).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Finset

/-- **The `k`-th floor error along the doubling orbit, as a function of the orbit coordinates.**
At the integer start `u = ⌊W·2ⁿ⌋`,
`fₖ = { {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ} + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ }`,
where `{W2ⁿ}` and `{α^{k+1}W2ⁿ}` are doubling-orbit fractional coordinates.  Degree-agnostic analogue of
`cubic_f1_orbit` / `cubic_f2_orbit`. -/
theorem dStepF_orbit (α : ℝ) (c : ℕ → ℝ) (W : ℝ) (n k : ℕ) :
    dStepF α c (⌊W * 2 ^ n⌋) k
      = Int.fract (Int.fract (α ^ (k + 1) * (W * 2 ^ n)) - α ^ (k + 1) * Int.fract (W * 2 ^ n)
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c (⌊W * 2 ^ n⌋) j))
          + α * c k) := by
  set u : ℤ := ⌊W * 2 ^ n⌋ with hu
  have hclosed := affine_rec_closed α (dStepV α c u) (fun j => α * c j - dStepF α c u j)
    (dStepV_succ α c u) k
  have harg : α * (dStepV α c u k + c k)
      = (Int.fract (α ^ (k + 1) * (W * 2 ^ n)) - α ^ (k + 1) * Int.fract (W * 2 ^ n)
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c u j)) + α * c k)
        + ((⌊α ^ (k + 1) * (W * 2 ^ n)⌋ : ℤ) : ℝ) := by
    have hv0 : dStepV α c u 0 = (u : ℝ) := by rw [dStepV]
    have huf : (u : ℝ) = W * 2 ^ n - Int.fract (W * 2 ^ n) := by
      rw [hu]; exact (Int.self_sub_fract _).symm
    have hflr : Int.fract (α ^ (k + 1) * (W * 2 ^ n)) + ((⌊α ^ (k + 1) * (W * 2 ^ n)⌋ : ℤ) : ℝ)
        = α ^ (k + 1) * (W * 2 ^ n) := Int.fract_add_floor _
    have hsum : α * (∑ j ∈ Finset.range k, α ^ (k - 1 - j) * (α * c j - dStepF α c u j))
        = ∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c u j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ]; ring
    rw [hclosed, hv0, huf]
    linear_combination hsum - hflr
  rw [dStepF, harg, Int.fract_add_intCast]

/-- **The floor errors as an explicit recursion in the orbit-coordinate vector `r`.**  `orbitF α c r k`
builds the `k`-th error purely from `r` (where `r i = {αⁱ·W2ⁿ}`) and the earlier errors, matching
`dStepF_orbit`.  Defined by strong recursion (the body references `orbitF … j` for `j < k`). -/
noncomputable def orbitF (α : ℝ) (c r : ℕ → ℝ) (k : ℕ) : ℝ :=
  Nat.strongRecOn k (fun k IH =>
    Int.fract (r (k + 1) - α ^ (k + 1) * r 0
      + (∑ j ∈ (Finset.range k).attach,
          α ^ (k - j.1) * (α * c j.1 - IH j.1 (Finset.mem_range.mp j.2))) + α * c k))

/-- The defining unfolding of `orbitF` (with the plain `Finset.range` sum). -/
theorem orbitF_eq (α : ℝ) (c r : ℕ → ℝ) (k : ℕ) :
    orbitF α c r k = Int.fract (r (k + 1) - α ^ (k + 1) * r 0
      + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - orbitF α c r j)) + α * c k) := by
  rw [orbitF, Nat.strongRecOn_eq,
    ← Finset.sum_attach (Finset.range k) (fun j => α ^ (k - j) * (α * c j - orbitF α c r j))]
  rfl

/-- **The floor error along the orbit IS `orbitF` at the canonical coordinate vector** `r i = {αⁱW2ⁿ}`.
Proved by strong induction via `dStepF_orbit` + `orbitF_eq`. -/
theorem dStepF_eq_orbitF (α : ℝ) (c : ℕ → ℝ) (W : ℝ) (n k : ℕ) :
    dStepF α c (⌊W * 2 ^ n⌋) k
      = orbitF α c (fun i => Int.fract (α ^ i * (W * 2 ^ n))) k := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rw [dStepF_orbit, orbitF_eq]
    have hsum : (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c (⌊W * 2 ^ n⌋) j))
        = ∑ j ∈ Finset.range k,
            α ^ (k - j) * (α * c j - orbitF α c (fun i => Int.fract (α ^ i * (W * 2 ^ n))) j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [IH j (Finset.mem_range.mp hj)]
    rw [hsum]
    simp only [pow_zero, one_mul]

/-- The partial defect as an explicit function `dGpd` of the orbit-coordinate vector `r`. -/
noncomputable def dGpd (α : ℝ) (c r : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ k ∈ Finset.range e, α ^ (e - k) * orbitF α c r k

/-- **The partial defect along the base-2 orbit IS `dGpd` at the canonical orbit coordinates**
`r i = {αⁱ·W2ⁿ}` — the degree-agnostic analogue of `cubicPartialDefect_eq_Gpd`.  This expresses the
defect as an explicit function of the `Tᵈ`-orbit point, the object the equidistribution argument
needs. -/
theorem dStepPartial_eq_dGpd (α : ℝ) (c : ℕ → ℝ) (W : ℝ) (n e : ℕ) :
    dStepPartial α c (⌊W * 2 ^ n⌋) (e + 1)
      = dGpd α c (fun i => Int.fract (α ^ i * (W * 2 ^ n))) e := by
  rw [dStepPartial_eq_sum, dGpd]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [dStepF_eq_orbitF]

/-- **Real-multiplier orbit bridge** (base-agnostic).  `dStepF_orbit` only uses `W·2ⁿ` as a single
real; replacing it with any real `M` gives the same closed form — so the floor errors of `dStepF α c ⌊M⌋`
are `orbitF` at the coordinate vector `r i = {αⁱ·M}`.  At `M = W·2ⁿ` this is `dStepF_eq_orbitF`; at
`M = W·gⁿ` it is the base-`g` bridge. -/
theorem dStepF_orbit_real (α : ℝ) (c : ℕ → ℝ) (M : ℝ) (k : ℕ) :
    dStepF α c (⌊M⌋) k
      = Int.fract (Int.fract (α ^ (k + 1) * M) - α ^ (k + 1) * Int.fract M
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c (⌊M⌋) j))
          + α * c k) := by
  set u : ℤ := ⌊M⌋ with hu
  have hclosed := affine_rec_closed α (dStepV α c u) (fun j => α * c j - dStepF α c u j)
    (dStepV_succ α c u) k
  have harg : α * (dStepV α c u k + c k)
      = (Int.fract (α ^ (k + 1) * M) - α ^ (k + 1) * Int.fract M
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c u j)) + α * c k)
        + ((⌊α ^ (k + 1) * M⌋ : ℤ) : ℝ) := by
    have hv0 : dStepV α c u 0 = (u : ℝ) := by rw [dStepV]
    have huf : (u : ℝ) = M - Int.fract M := by rw [hu]; exact (Int.self_sub_fract _).symm
    have hflr : Int.fract (α ^ (k + 1) * M) + ((⌊α ^ (k + 1) * M⌋ : ℤ) : ℝ)
        = α ^ (k + 1) * M := Int.fract_add_floor _
    have hsum : α * (∑ j ∈ Finset.range k, α ^ (k - 1 - j) * (α * c j - dStepF α c u j))
        = ∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c u j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ]; ring
    rw [hclosed, hv0, huf]
    linear_combination hsum - hflr
  rw [dStepF, harg, Int.fract_add_intCast]

/-- The floor error along the `M`-orbit IS `orbitF` at the canonical coordinates `r i = {αⁱ·M}`. -/
theorem dStepF_eq_orbitF_real (α : ℝ) (c : ℕ → ℝ) (M : ℝ) (k : ℕ) :
    dStepF α c (⌊M⌋) k = orbitF α c (fun i => Int.fract (α ^ i * M)) k := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rw [dStepF_orbit_real, orbitF_eq]
    have hsum : (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c (⌊M⌋) j))
        = ∑ j ∈ Finset.range k,
            α ^ (k - j) * (α * c j - orbitF α c (fun i => Int.fract (α ^ i * M)) j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [IH j (Finset.mem_range.mp hj)]
    rw [hsum]
    simp only [pow_zero, one_mul]

/-- The partial defect along the `M`-orbit IS `dGpd` at the canonical coordinates `r i = {αⁱ·M}`. -/
theorem dStepPartial_eq_dGpd_real (α : ℝ) (c : ℕ → ℝ) (M : ℝ) (e : ℕ) :
    dStepPartial α c (⌊M⌋) (e + 1)
      = dGpd α c (fun i => Int.fract (α ^ i * M)) e := by
  rw [dStepPartial_eq_sum, dGpd]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [dStepF_eq_orbitF_real]

/-- Finite sum of functions continuous at a point is continuous at that point. -/
private theorem continuousAt_finset_sum {ι X : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → X → ℝ) {x : X} (h : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | @insert a s ha IH =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (IH fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The inner argument of `orbitF` at step `k` (`orbitF … k = {orbitArg … k}`). -/
noncomputable def orbitArg (α : ℝ) (c r : ℕ → ℝ) (k : ℕ) : ℝ :=
  r (k + 1) - α ^ (k + 1) * r 0
    + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - orbitF α c r j)) + α * c k

theorem orbitF_eq_fract_arg (α : ℝ) (c r : ℕ → ℝ) (k : ℕ) :
    orbitF α c r k = Int.fract (orbitArg α c r k) := by rw [orbitF_eq, orbitArg]

/-- **`orbitF … k` is continuous in the coordinate vector `r`** at any base point `r₀` whose inner
fract-arguments `orbitArg … m` (`m ≤ k`) are all non-integers.  Strong induction via `continuousAt_fract`
and the product-topology coordinate projections (`continuous_apply`). -/
theorem continuousAt_orbitF (α : ℝ) (c r₀ : ℕ → ℝ) :
    ∀ k, (∀ m, m ≤ k → orbitArg α c r₀ m ≠ ((⌊orbitArg α c r₀ m⌋ : ℤ) : ℝ)) →
      ContinuousAt (fun r => orbitF α c r k) r₀ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro h
    have harg : ContinuousAt (fun r : ℕ → ℝ => orbitArg α c r k) r₀ := by
      unfold orbitArg
      refine ((((continuous_apply (k + 1)).continuousAt).sub
        (((continuous_apply 0).continuousAt).const_mul _)).add ?_).add continuousAt_const
      refine continuousAt_finset_sum _ _ (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      exact (((continuousAt_const).sub (IH j hj (fun m hm => h m (hm.trans hj.le)))).const_mul _)
    have hfun : (fun r : ℕ → ℝ => orbitF α c r k) = (fun r => Int.fract (orbitArg α c r k)) := by
      funext r; rw [orbitF_eq_fract_arg]
    rw [hfun]
    exact ContinuousAt.comp (g := Int.fract) (f := fun r : ℕ → ℝ => orbitArg α c r k)
      (continuousAt_fract (h k le_rfl)) harg

/-- **The partial-defect function `dGpd` is continuous in the coordinate vector** at any point whose
inner fract-arguments are non-integers — the degree-agnostic analogue of `continuousAt_cubicGpd`. -/
theorem continuousAt_dGpd (α : ℝ) (c r₀ : ℕ → ℝ) (e : ℕ)
    (h : ∀ m, m < e → orbitArg α c r₀ m ≠ ((⌊orbitArg α c r₀ m⌋ : ℤ) : ℝ)) :
    ContinuousAt (fun r => dGpd α c r e) r₀ := by
  unfold dGpd
  refine continuousAt_finset_sum _ _ (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  exact (continuousAt_orbitF α c r₀ k (fun m hm => h m (lt_of_le_of_lt hm hk))).const_mul _

/-- An explicit coordinate vector realizing a target floor-error configuration `t`.  `r 0 = 0` and
`r (k+1)` is solved so that `orbitArg = t k` (`orbitF_realizeR`). -/
noncomputable def realizeR (α : ℝ) (c t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => t k - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - t j)) - α * c k

/-- **`orbitF` realizes any interior target configuration.**  For a target `t` with `tₖ ∈ [0,1)`
(`k < e`), the coordinate vector `realizeR` makes every inner arg `orbitArg … k = tₖ` (hence `∉ ℤ` when
`tₖ ≠ 0`) and `orbitF … k = tₖ`.  The general analogue of the cubic's `fract_shift_realize`. -/
theorem orbitArg_realizeR (α : ℝ) (c t : ℕ → ℝ) (e : ℕ)
    (ht : ∀ k, k < e → t k ∈ Set.Ico (0 : ℝ) 1) :
    ∀ k, k < e → orbitArg α c (realizeR α c t) k = t k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk
    have hsum : (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - orbitF α c (realizeR α c t) j))
        = ∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - t j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [orbitF_eq_fract_arg, IH j hj (hj.trans hk), Int.fract_eq_self.mpr (ht j (hj.trans hk))]
    rw [orbitArg, show realizeR α c t 0 = 0 from rfl,
      show realizeR α c t (k + 1)
        = t k - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - t j)) - α * c k from rfl,
      hsum]
    ring

theorem orbitF_realizeR (α : ℝ) (c t : ℕ → ℝ) (e : ℕ)
    (ht : ∀ k, k < e → t k ∈ Set.Ico (0 : ℝ) 1) :
    ∀ k, k < e → orbitF α c (realizeR α c t) k = t k := by
  intro k hk
  rw [orbitF_eq_fract_arg, orbitArg_realizeR α c t e ht k hk]
  exact Int.fract_eq_self.mpr (ht k hk)

/-- **A nonzero-`r 0` realizer producing a constant `orbitF = τ`.**  Like `realizeR` but with a free
seed `σ` for `r 0` and the higher coordinates taken modulo `1` (`Int.fract`), so they too land in
`[0,1)`.  This makes every `orbitF … k = τ` (constant) regardless of `σ`; choosing `σ` outside a
countable bad set keeps every coordinate strictly positive (so the torus point has nonzero coords). -/
noncomputable def realizeR0 (α : ℝ) (c : ℕ → ℝ) (τ σ : ℝ) : ℕ → ℝ
  | 0 => σ
  | (k + 1) => Int.fract (τ + α ^ (k + 1) * σ
      - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) - α * c k)

/-- **`orbitF` at the `realizeR0` seed is the constant `τ`.**  For `τ ∈ [0,1)`, every `orbitF α c
(realizeR0 α c τ σ) k = τ`, *independently of the seed* `σ`.  The inner argument is `τ` shifted by an
integer (`-⌊X⌋`), so its fractional part is `τ`.  Proof by strong induction. -/
theorem orbitF_realizeR0 (α : ℝ) (c : ℕ → ℝ) (τ σ : ℝ) (hτ : τ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ k, orbitF α c (realizeR0 α c τ σ) k = τ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rw [orbitF_eq_fract_arg, orbitArg]
    have hsum : (∑ j ∈ Finset.range k,
          α ^ (k - j) * (α * c j - orbitF α c (realizeR0 α c τ σ) j))
        = ∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj; rw [IH j hj]
    rw [hsum, show realizeR0 α c τ σ 0 = σ from rfl,
      show realizeR0 α c τ σ (k + 1) = Int.fract (τ + α ^ (k + 1) * σ
          - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) - α * c k) from rfl]
    set X : ℝ := τ + α ^ (k + 1) * σ
      - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) - α * c k with hX
    rw [show Int.fract X - α ^ (k + 1) * σ
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) + α * c k
        = ((-⌊X⌋ : ℤ) : ℝ) + τ by
        have hsf : X - Int.fract X = ((⌊X⌋ : ℤ) : ℝ) := Int.self_sub_fract X
        push_cast; rw [hX] at hsf ⊢; linarith]
    rw [Int.fract_intCast_add, Int.fract_eq_self.mpr hτ]

/-- **`orbitF … k` depends only on the coordinates `r 0, …, r (k+1)`.** -/
theorem orbitF_congr (α : ℝ) (c r r' : ℕ → ℝ) (k : ℕ) (h : ∀ i, i ≤ k + 1 → r i = r' i) :
    orbitF α c r k = orbitF α c r' k := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rw [orbitF_eq, orbitF_eq, h 0 (by omega), h (k + 1) le_rfl]
    refine congrArg _ ?_
    refine congrArg (· + α * c k) (congrArg (_ + ·) (Finset.sum_congr rfl (fun j hj => ?_)))
    rw [Finset.mem_range] at hj
    rw [IH j hj (fun i hi => h i (by omega))]

/-- **`dGpd … e` depends only on the coordinates `r 0, …, r e`** (the largest `orbitF (e-1)` reads
`r e`).  So for the `Tᵈ` orbit (`d = e+1`) it depends only on the `d` torus coordinates. -/
theorem dGpd_congr (α : ℝ) (c r r' : ℕ → ℝ) (e : ℕ) (h : ∀ i, i ≤ e → r i = r' i) :
    dGpd α c r e = dGpd α c r' e := by
  unfold dGpd
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [orbitF_congr α c r r' k (fun i hi => h i (by omega))]

end LeanGallery.NumberTheory.Erdos482.General
