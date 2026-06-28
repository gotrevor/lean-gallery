/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The integer-approximation irrationality criterion

The single reusable lemma the whole proof feeds: a real `x` is irrational if there are integer
sequences `aₙ, bₙ` with `bₙ·x − aₙ ≠ 0` for all `n` and `bₙ·x − aₙ → 0`. (Hardy–Wright Thm 186 /
Van Assche Lemma 5.1.) The standard one-line argument: if `x = p/q` were rational, then
`bₙ·x − aₙ = (bₙ·p − aₙ·q)/q` is a nonzero rational of absolute value `≥ 1/q`, contradicting `→ 0`.

⚠️ Check whether mathlib already has this (it has `Liouville` machinery in
`Mathlib.NumberTheory.Liouville.*` and `Irrational` API). If a close form exists, delegate to it; this
file is a ~20-line standalone fallback otherwise.
-/

namespace LeanGallery.NumberTheory.Erdos1050
open Filter Topology

/-- Irrationality from integer approximations with nonzero, vanishing error.
If `b n * x - a n ≠ 0` for all `n` and `(fun n => b n * x - a n) → 0`, then `x` is irrational.

Proof: if `x = r` were rational with denominator `d = r.den`, then `d·(bₙ·x − aₙ) =
bₙ·r.num − d·aₙ` is a nonzero integer, hence has absolute value `≥ 1`, so `|bₙ·x − aₙ| ≥ 1/d > 0`
for all `n` — contradicting `bₙ·x − aₙ → 0`. -/
theorem irrational_of_intApprox (x : ℝ) (a b : ℕ → ℤ)
    (hne : ∀ n, (b n : ℝ) * x - a n ≠ 0)
    (hlim : Tendsto (fun n => (b n : ℝ) * x - a n) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast Rat.den_pos r
  have hdne : (r.den : ℝ) ≠ 0 := ne_of_gt hden
  have hrd : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def]; field_simp
  -- Lower bound: `|bₙ·r − aₙ| ≥ 1/r.den` for every `n`.
  have hlb : ∀ n, 1 / (r.den : ℝ) ≤ |(b n : ℝ) * (r : ℝ) - (a n : ℝ)| := by
    intro n
    have hcast : ((b n * r.num - r.den * a n : ℤ) : ℝ)
        = (r.den : ℝ) * ((b n : ℝ) * (r : ℝ) - (a n : ℝ)) := by
      push_cast
      linear_combination (-(b n : ℝ)) * hrd
    have hcne : (b n * r.num - r.den * a n : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hcast
      rcases mul_eq_zero.mp hcast.symm with h | h
      · exact hdne h
      · exact hne n h
    have h1 : (1 : ℝ) ≤ |((b n * r.num - r.den * a n : ℤ) : ℝ)| := by
      have hz : (1 : ℤ) ≤ |b n * r.num - r.den * a n| := Int.one_le_abs hcne
      calc (1 : ℝ) ≤ ((|b n * r.num - r.den * a n| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |((b n * r.num - r.den * a n : ℤ) : ℝ)| := by rw [Int.cast_abs]
    rw [hcast, abs_mul, abs_of_pos hden] at h1
    rw [div_le_iff₀ hden]
    nlinarith [h1]
  -- The error tends to `0` in absolute value, contradicting the constant lower bound.
  have habs : Tendsto (fun n => |(b n : ℝ) * (r : ℝ) - (a n : ℝ)|) atTop (𝓝 0) := by
    simpa using hlim.abs
  have hle : 1 / (r.den : ℝ) ≤ 0 := ge_of_tendsto' habs hlb
  have hpos : (0 : ℝ) < 1 / (r.den : ℝ) := by positivity
  linarith

end LeanGallery.NumberTheory.Erdos1050
