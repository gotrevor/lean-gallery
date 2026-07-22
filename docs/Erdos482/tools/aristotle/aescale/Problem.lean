import Mathlib

open MeasureTheory

/-
GOAL (step-(c) piece 1 of the Erdos #482 / Stoll cubic frontier: change of variables for a.e.
statements under nonzero scaling). On the real line with Lebesgue measure: if a property P holds for
almost every s, then for any nonzero c, the property "P (c * W)" holds for almost every W.

This transfers an a.e.-s equidistribution result to an a.e.-W result after the linear substitution
s = c*W (with c = a + b*alpha + c*alpha^2, the nonzero cubic linear form).

REDUCTION ROUTE (please follow; isolate any hard step as its own sorry'd lemma and still return the
assembled proof):
 - The "bad" set in W is the preimage of the bad set in s under the map m : W |-> c * W, i.e.
   {W | not P (c*W)} = m ⁻¹' {s | not P s}.
 - {s | not P s} is null (from hP : the complement is in `ae volume`).
 - Multiplication by a nonzero constant maps null sets to null sets (Lebesgue scales by |c|): use
   `MeasureTheory.Measure.addHaar_smul` / `Real.volume` scaling, or the quasi-measure-preserving
   structure of `m` (`m` is a measurable equivalence with inverse W |-> c⁻¹ * W). A clean route:
   show `Filter.Tendsto (fun W => c * W) (MeasureTheory.ae volume) (MeasureTheory.ae volume)` (scaling
   preserves the a.e. filter because it preserves null sets), then conclude with
   `Filter.Tendsto.eventually hP`. If a ready `tendsto_smul_ae`-style lemma does not apply to ℝ
   multiplicative scaling, prove the null-preservation directly from `addHaar_smul` and the preimage
   identity `(fun W => c*W) ⁻¹' A = c⁻¹ • A`.

Keep the final statement EXACTLY as below.
-/
theorem ae_comp_mul_left {c : ℝ} (hc : c ≠ 0) {P : ℝ → Prop}
    (hP : ∀ᵐ s ∂(volume : Measure ℝ), P s) :
    ∀ᵐ W ∂(volume : Measure ℝ), P (c * W) := by
  sorry
