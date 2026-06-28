/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Digits

/-!
# Stoll [St05] Theorem 1.3 — digit extraction from the closed forms

Theorem 1.3 (g-ary, any base `g ≥ 2`): with `t = w/g^m` the base-`g` mantissa of `w`,
`a = g/((g−1)(t+g))`, `b = g/a`, recurrence `u₁ = 1`, `uₙ₊₁ = ⌊a(uₙ+ε)⌋` (n odd),
`⌊b(uₙ + 1/(g−1))⌋` (n even), one has `u₂ₙ₊₁ − g·u₂ₙ₋₁` = the n-th base-`g` digit of `w`.
The closed forms are `u₂ₖ = (g^{k−1}−1)/(g−1)` and `u₂ₖ₊₁ = g^k + ⌊t·g^{k−1}⌋`.

This module proves the **conclusion modulo the closed-form induction**: *given* the odd-index closed
form, the Graham–Pollak-style difference reads off a base-`g` digit (in `digitStep` form, range
`[0,g)`).  The closed-form induction itself (from the recurrence) is the remaining piece.

Numerically verified end-to-end (`tools/sandbox/st05_thm13_verify.py`).  The odd-index closed form is
written `u(2k+1) = g^k + ⌊t·g^k / g⌋` to avoid a negative exponent at `k = 0` (there it reads
`1 + ⌊t/g⌋ = 1 = u₁`, since `1 ≤ t < g`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **St05 Theorem 1.3 recurrence** (0-indexed, `gu g a b ε n = u_{n+1}`, `u₁ = 1`).  The step from
index `n` uses the `(a, ε)` offset when `n` is even (i.e. original odd index `n+1`) and
`(b, 1/(g−1))` when `n` is odd.  With `a = g/((g−1)(t+g))`, `b = g/a = (g−1)(t+g)`, this is the
recurrence whose closed forms are `gu(2k) = g^k + ⌊t·g^{k−1}⌋`, `(g−1)·gu(2k+1) = g^k − 1` — the
object the Aristotle closed-form induction (`tools/aristotle/thm13closed`, job `e0240fef`) ports onto. -/
noncomputable def gu (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((gu g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((gu g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

@[simp] theorem gu_zero (g : ℕ) (a b ε : ℝ) : gu g a b ε 0 = 1 := rfl

/-- **St05 Theorem 1.3, digit-extraction step (from the odd-index closed form).**  If `u : ℕ → ℤ`
satisfies `u(2k+1) = g^k + ⌊t·g^k/g⌋` for all `k`, then for every `n ≥ 1`,
`u(2n+1) − g·u(2n−1) = digitStep g (t·g^{n−1}/g)`, a base-`g` digit lying in `[0,g)`. -/
theorem thm13_digit_of_oddClosed (g : ℕ) (hg : 1 ≤ g) (t : ℝ) (u : ℕ → ℤ)
    (hodd : ∀ k, u (2 * k + 1) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋)
    (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n + 1) - g * u (2 * n - 1) = digitStep g (t * (g : ℝ) ^ (n - 1) / g) ∧
      0 ≤ u (2 * n + 1) - g * u (2 * n - 1) ∧
      u (2 * n + 1) - g * u (2 * n - 1) < (g : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hgne : (g : ℝ) ≠ 0 := by positivity
  have he : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have hdig : u (2 * (m + 1) + 1) - g * u (2 * (m + 1) - 1)
      = digitStep g (t * (g : ℝ) ^ (m + 1 - 1) / g) := by
    rw [he, hodd (m + 1), hodd m, Nat.add_sub_cancel]
    simp only [digitStep]
    rw [show t * (g : ℝ) ^ (m + 1) / g = (g : ℝ) * (t * (g : ℝ) ^ m / g) by field_simp; ring]
    ring
  refine ⟨hdig, ?_, ?_⟩
  · rw [hdig]; exact (digitStep_mem g hg _).1
  · rw [hdig]; exact (digitStep_mem g hg _).2

/-- **St05 Theorem 1.3 conclusion as a literal mathlib digit.**  Chaining
`thm13_digit_of_oddClosed` with the general Prop-2 bridge `realDigits_eq_digitStep`: under the
odd-index closed form, `u(2n+1) − g·u(2n−1)` is exactly mathlib's leading base-`g` digit
`Real.digits (t·g^{n−1}/g) g 0` (`g ≥ 2`, `t ≥ 0`, `n ≥ 1`).  This identifies St05's recurrence
output with a bona-fide base-`g` digit in mathlib's API. -/
theorem thm13_digit_realDigits (g : ℕ) [NeZero g] (hg : 2 ≤ g) (t : ℝ) (ht : 0 ≤ t) (u : ℕ → ℤ)
    (hodd : ∀ k, u (2 * k + 1) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋)
    (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n + 1) - g * u (2 * n - 1)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hy0 : 0 ≤ t * (g : ℝ) ^ (n - 1) / g := by positivity
  rw [(thm13_digit_of_oddClosed g (by omega) t u hodd n hn).1,
    realDigits_eq_digitStep g (t * (g : ℝ) ^ (n - 1) / g) hy0 0, pow_zero, mul_one]

end LeanGallery.NumberTheory.Erdos482.General
