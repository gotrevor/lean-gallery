import Mathlib
open MeasureTheory Filter Topology

/-
GOAL: The Borel–Cantelli / L² engine of Davenport–Erdős–LeVeque.  On the unit interval [0,1] with
Lebesgue measure, if a sequence of (a.e. strongly) measurable ℂ-valued functions g_j has SUMMABLE
mean squares ∑_j ∫₀¹ ‖g_j‖² < ∞, then g_j → 0 almost everywhere.

This is the abstract step that, applied to g_j(s) = (1/j²)·∑_{n<j²} e^{2πi k 2ⁿ s} (whose ∫₀¹‖g_j‖²
= 1/j² is summable, from the Weyl mean square ∫₀¹|∑_{n<N} e(k2ⁿs)|² = N), gives a.e. base-2
equidistribution of {2ⁿs} on the cubic self-referential frontier (Erdős #482 / Stoll).

RECIPE (Markov + first Borel–Cantelli):
- For ε>0, let A_j = {x ∈ [0,1] | ε ≤ ‖g_j x‖}.  By Chebyshev/Markov
  (`MeasureTheory.meas_ge_le_lintegral_div` or `mul_meas_ge_le_lintegral`), μ(A_j) ≤ (1/ε²)·∫‖g_j‖².
- Hence ∑_j μ(A_j) < ∞, so by Borel–Cantelli (`MeasureTheory.measure_limsup_atTop_eq_zero` /
  `measure_limsup_eq_zero`) μ(limsup A_j) = 0: a.e. x lies in only finitely many A_j, i.e. eventually
  ‖g_j x‖ < ε.
- Run ε over a sequence → 0 (e.g. 1/(k+1)); intersect the countably many conull sets to get a.e. x with
  ‖g_j x‖ → 0, i.e. Tendsto (g_· x) atTop (𝓝 0).
NOTE: if mathlib already has "summable L² ⇒ a.e. tendsto 0" (search `Memℒp`, `ae_tendsto`,
`tendsto_..._ae`), use it directly. Measure here is `volume.restrict (Set.Icc 0 1)` (a probability
measure); keep statement as below.
-/

theorem ae_tendsto_zero_of_summable_sq
    (g : ℕ → ℝ → ℂ)
    (hmeas : ∀ j, AEStronglyMeasurable (g j) (volume.restrict (Set.Icc (0:ℝ) 1)))
    (hsum : Summable (fun j => ∫⁻ x in Set.Icc (0:ℝ) 1, ‖g j x‖₊ ^ 2 ∂volume)) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Tendsto (fun j => g j x) atTop (𝓝 0) := by
  sorry
