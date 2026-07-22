import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

/-
GOAL (a measure-theory bridge for the Davenport-Erdos-LeVeque assembly, Erdos #482 / Stoll cubic
frontier). For a continuous g : R -> C, the lower (ENNReal) integral of the squared norm over the
closed unit interval equals ENNReal.ofReal of the Bochner interval integral of the squared norm:

    integral^- over Icc 0 1 of (norm (g x))^2  =  ENNReal.ofReal ( integral over 0..1 of (norm (g s))^2 ).

This lets us turn the explicit real Weyl mean square (integral over 0..1 of |.|^2 = 1/N) into the
ENNReal hypothesis the DEL engine needs (sum of integral^- of norms^2 finite).

REDUCTION ROUTE (please follow; if a step is hard, isolate it as its own sorry'd lemma and still
return the assembled proof):
 1. Pointwise: ((norm (g x)) : NNReal) coerced to ENNReal, squared, equals ENNReal.ofReal ((norm (g x))^2).
    Use ENNReal.ofReal_pow / the coercion lemmas: (norm a)_nnreal coerced = ENNReal.ofReal (norm a),
    and ofReal is multiplicative on nonnegatives.
 2. integral^- over Icc 0 1 of ENNReal.ofReal ((norm (g x))^2)  =  ENNReal.ofReal (integral over Icc 0 1 of (norm (g x))^2),
    by `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` (needs: (fun x => (norm (g x))^2) is
    Integrable on the restricted measure, and is a.e. nonnegative -- both hold: g continuous on the
    compact Icc 0 1, so norm-squared is continuous hence integrable; nonneg is `sq_nonneg`/positivity).
 3. integral over 0..1 of (norm (g s))^2  =  integral over Icc 0 1 of (norm (g x))^2 :
    intervalIntegral over 0..1 (with 0 <= 1) is the set integral over Ioc 0 1
    (`intervalIntegral.integral_of_le` gives `integral over Ioc 0 1 of f`), and the set integral over
    Ioc 0 1 equals that over Icc 0 1 because they differ by the null set {0}
    (`MeasureTheory.integral_Icc_eq_integral_Ioc` or `setIntegral_congr_set` with `Ioc_ae_eq_Icc`).

Keep the final statement EXACTLY as below (do not change hypotheses/conclusion).
-/
theorem l2_bridge (g : ℝ → ℂ) (hg : Continuous g) :
    (∫⁻ x in Set.Icc (0:ℝ) 1, ‖g x‖₊ ^ 2 ∂volume)
      = ENNReal.ofReal (∫ s in (0:ℝ)..1, ‖g s‖ ^ 2) := by
  sorry
