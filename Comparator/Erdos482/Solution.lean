/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.Statement

/-!
# Erdős #482 — comparator SOLUTION

Discharges every `sorry` in `Challenge.lean` by delegating to the real development. The definitions
are repeated **verbatim** from the challenge (comparator requires that every declaration appearing
in a statement be identical in both environments), and each theorem is closed by the corresponding
gallery result.

The four definitions are recursive/noncomputable, so rather than lean on the kernel to unfold two
independently-compiled copies against each other, we bridge them explicitly (`u_eq`, `vv_eq`,
`gu_eq`, `binDigit_eq`) and rewrite the goal into the development's own vocabulary before applying
its theorem. The bridges are pure `rfl`/induction — they add nothing to the trust base.

This file is *not* part of the audit surface — `Challenge.lean` is. Comparator's job is to prove
that whatever happens in here really did establish the challenge's statements.
-/

namespace Erdos482

/-! ## Definitions — verbatim from `Challenge.lean` -/

/-- Verbatim from `Challenge.lean` — comparator checks the two are the same declaration. -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-- Verbatim from `Challenge.lean` — comparator checks the two are the same declaration. -/
noncomputable def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

/-- Verbatim from `Challenge.lean` — comparator checks the two are the same declaration. -/
noncomputable def vv (ε : ℝ) : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((vv ε n : ℝ) + (if Even n then ε else 1 / 2))⌋₊

/-- Verbatim from `Challenge.lean` — comparator checks the two are the same declaration. -/
noncomputable def gu (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((gu g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((gu g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-! ## Bridges to the development's copies of the same definitions -/

theorem u_eq (n : ℕ) : u n = LeanGallery.NumberTheory.Erdos482.u n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [u, LeanGallery.NumberTheory.Erdos482.u, ih]

theorem binDigit_eq (t : ℝ) (n : ℕ) :
    binDigit t n = LeanGallery.NumberTheory.Erdos482.binDigit t n := rfl

theorem vv_eq (ε : ℝ) (n : ℕ) : vv ε n = LeanGallery.NumberTheory.Erdos482.vv ε n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vv, LeanGallery.NumberTheory.Erdos482.vv, ih]

theorem gu_eq (g : ℕ) (a b ε : ℝ) (n : ℕ) :
    gu g a b ε n = LeanGallery.NumberTheory.Erdos482.General.gu g a b ε n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gu, LeanGallery.NumberTheory.Erdos482.General.gu, ih]

/-! ## The headline statements, delegated -/

theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  simp only [u_eq, binDigit_eq]
  exact LeanGallery.NumberTheory.Erdos482.graham_pollak n hn

theorem graham_pollak_digits (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ)
      = ((Real.digits (Int.fract (Real.sqrt 2)) 2 (n - 1) : ℕ) : ℤ) := by
  simp only [u_eq]
  exact LeanGallery.NumberTheory.Erdos482.graham_pollak_digits n hn

theorem cor33_unconditional (m : ℕ) :
    (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) + 1) : ℤ)
        - 2 * (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) - 1) : ℤ)
      = binDigit (759250125 * Real.sqrt 2) (m + 1) := by
  simp only [vv_eq, binDigit_eq]
  exact LeanGallery.NumberTheory.Erdos482.cor33_unconditional m

theorem erdos482_resolution (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 1 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits
              (w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  simp only [gu_eq]
  exact LeanGallery.NumberTheory.Erdos482.General.erdos482_resolution g hg w hw

theorem binDigit_sqrt2_first_six :
    binDigit (Real.sqrt 2) 1 = 0 ∧ binDigit (Real.sqrt 2) 2 = 1 ∧
      binDigit (Real.sqrt 2) 3 = 1 ∧ binDigit (Real.sqrt 2) 4 = 0 ∧
      binDigit (Real.sqrt 2) 5 = 1 ∧ binDigit (Real.sqrt 2) 6 = 0 := by
  simp only [binDigit_eq]
  exact LeanGallery.NumberTheory.Erdos482.binDigit_sqrt2_first_six

end Erdos482
