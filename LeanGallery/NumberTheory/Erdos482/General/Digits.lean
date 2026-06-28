/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# General base-`g` digit extraction (Stoll [St05], Proposition 2)

The `0902.4168` work in `LeanGallery.NumberTheory.Erdos482.Stoll` is the base-2, `α√2` special case.  Stoll's J. Integer Seq.
**8** (2005) paper [St05] resolves Erdős–Graham #482 in full: for *any* real `w > 0` and *any* integer
base `g ≥ 2`, an explicit floor-recurrence reads off the base-`g` digits of `w`.  This module begins
that track with the foundational digit-extraction formula and its range bound.

`gdigit g t n := ⌊t·gⁿ⌋ − g·⌊t·gⁿ⁻¹⌋` is the `n`-th base-`g` digit of (the mantissa) `t`.  The key
fact — used at *every* induction step of St05's closed-form proofs — is the range bound
`0 ≤ gdigit g t n < g`, which is just `0 ≤ ⌊g·x⌋ − g·⌊x⌋ < g` at `x = t·gⁿ⁻¹`.

Numerically verified (`tools/sandbox/st05_thm13_verify.py`): the closed forms + this digit identity
hold for `w ∈ {√2, √3, π}`, `g ∈ {2,3,10}`, at the ε-interval endpoints, over many `n`.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- The base-`g` digit operator on a real `x` at the integer scale: `⌊g·x⌋ − g·⌊x⌋`.  For `x ≥ 0`
this is the leading base-`g` digit of `g·x`'s fractional carry. -/
noncomputable def digitStep (g : ℕ) (x : ℝ) : ℤ := ⌊(g : ℝ) * x⌋ - g * ⌊x⌋

/-- **The digit-step range bound.**  For `g ≥ 1` and any real `x`, `0 ≤ ⌊g·x⌋ − g·⌊x⌋ < g`.
(Writing `x = ⌊x⌋ + {x}`, the step equals `⌊g·{x}⌋ ∈ {0,…,g−1}`.)  This is the single inequality
behind every St05 induction step. -/
theorem digitStep_mem (g : ℕ) (hg : 1 ≤ g) (x : ℝ) :
    0 ≤ digitStep g x ∧ digitStep g x < (g : ℤ) := by
  have hgr : (0 : ℝ) ≤ (g : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · -- g·⌊x⌋ ≤ ⌊g·x⌋  ⟺  ↑(g·⌊x⌋) ≤ g·x
    rw [digitStep, sub_nonneg, Int.le_floor]
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le x) hgr
  · -- ⌊g·x⌋ < g·⌊x⌋ + g  ⟺  g·x < ↑(g·⌊x⌋ + g)
    rw [digitStep, sub_lt_iff_lt_add, Int.floor_lt]
    push_cast
    have : (g : ℝ) * x < (g : ℝ) * ((⌊x⌋ : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (Int.lt_floor_add_one x) (by exact_mod_cast hg)
    linarith

/-- **Proposition 2 (St05), digit-of-mantissa form.**  `gdigit g t n` is the base-`g` digit
`⌊t·gⁿ⁻¹⌋ − g·⌊t·gⁿ⁻²⌋` written at scale `n`: it equals `digitStep g (t·gⁿ⁻¹)`.  The two are
defeq-after-`ring`; this lemma records the bridge and the range bound in one place. -/
noncomputable def gdigit (g : ℕ) (t : ℝ) (n : ℕ) : ℤ :=
  ⌊t * (g : ℝ) ^ n⌋ - g * ⌊t * (g : ℝ) ^ (n - 1)⌋

/-- `gdigit g t (n+1) = digitStep g (t·gⁿ)` (so the range bound transfers). -/
theorem gdigit_succ_eq (g : ℕ) (t : ℝ) (n : ℕ) :
    gdigit g t (n + 1) = digitStep g (t * (g : ℝ) ^ n) := by
  unfold gdigit digitStep
  rw [show (n + 1) - 1 = n from rfl,
    show t * (g : ℝ) ^ (n + 1) = (g : ℝ) * (t * (g : ℝ) ^ n) by rw [pow_succ]; ring]

/-- **Every base-`g` digit lies in `{0,…,g−1}`** (`g ≥ 1`, any real `t`). -/
theorem gdigit_mem (g : ℕ) (hg : 1 ≤ g) (t : ℝ) (n : ℕ) :
    0 ≤ gdigit g t (n + 1) ∧ gdigit g t (n + 1) < (g : ℤ) := by
  rw [gdigit_succ_eq]; exact digitStep_mem g hg _

/-- **Proposition 2 (St05) — mathlib bridge, general base.**  For `y ≥ 0` and base `g` (`NeZero g`),
mathlib's `i`-th base-`g` digit of `y` is exactly the floor difference `⌊y·g^{i+1}⌋ − g·⌊y·g^i⌋ =
digitStep g (y·g^i)`.  Generalizes the repo's base-2 `LeanGallery.NumberTheory.Erdos482.digits_eq_floor_sub` to any base —
the bridge that identifies St05's recurrence output with the actual base-`g` digits of `w`. -/
theorem realDigits_eq_digitStep (g : ℕ) [NeZero g] (y : ℝ) (hy0 : 0 ≤ y) (i : ℕ) :
    ((Real.digits y g i : ℕ) : ℤ) = digitStep g (y * (g : ℝ) ^ i) := by
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  set N : ℤ := ⌊y * (g : ℝ) ^ (i + 1)⌋ with hN
  set M : ℤ := ⌊y * (g : ℝ) ^ i⌋ with hM
  have hds : digitStep g (y * (g : ℝ) ^ i) = N - g * M := by
    unfold digitStep
    rw [hN, hM, show (g : ℝ) * (y * (g : ℝ) ^ i) = y * (g : ℝ) ^ (i + 1) by ring]
  obtain ⟨hlo, hhi⟩ := digitStep_mem g hg (y * (g : ℝ) ^ i)
  rw [hds] at hlo hhi
  have hdval : ((Real.digits y g i : ℕ) : ℤ) = ((⌊y * (g : ℝ) ^ (i + 1)⌋₊ % g : ℕ) : ℤ) := by
    simp only [Real.digits, Fin.val_ofNat]
  have hpos : (0 : ℝ) ≤ y * (g : ℝ) ^ (i + 1) := mul_nonneg hy0 (by positivity)
  have hfn : (⌊y * (g : ℝ) ^ (i + 1)⌋₊ : ℤ) = N := by rw [Int.natCast_floor_eq_floor hpos]
  -- N % g = N − g·M : the part `g·M` is killed mod g, and `N − g·M ∈ [0,g)`.
  have hmod : N % (g : ℤ) = N - g * M := by
    conv_lhs => rw [show N = (N - g * M) + g * M by ring]
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hlo hhi]
  rw [hds, hdval, Int.natCast_mod, hfn, hmod]

end LeanGallery.NumberTheory.Erdos482.General
