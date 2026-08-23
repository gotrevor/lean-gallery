import Mathlib

open MeasureTheory Filter Topology

/-
GOAL (step-(c) piece 3 of the Erdos #482 / Stoll cubic frontier): equidistribution implies a dense
orbit. On a compact space X with a finite, open-positive Borel measure mu, if the Cesaro averages of
every continuous complex test function converge to its integral, then the orbit {x n} is dense.

This lets the a.e. T^3 equidistribution (built in the repo) contradict the measure-zero two-plane
"defect confinement" of the cubic self-referential map.

REDUCTION ROUTE (please follow; isolate any hard sub-step as its own sorry'd lemma and STILL return the
assembled proof):
 - Suppose, for contradiction, the range is not dense: there is a point p and an open set U with p in U
   and U disjoint from the closure of the range (use `dense_iff` / `not_dense_iff` to get a nonempty
   open U missing the range).
 - Build a continuous bump: a continuous function g : X -> R, 0 <= g <= 1, g p = 1, with support inside
   U (X compact Hausdorff is normal/regular; use `exists_continuous_..` / `Urysohn`-style lemmas, or
   `IsCompact`/`exists_continuous_zero_one`). Then view it in C(X, C) via `Complex.ofReal`.
 - The Cesaro average of g along the orbit is 0 for every N, because g vanishes on the range (range
   subset of U^c). Hence the limit is 0.
 - But the integral of g is strictly positive: g is continuous, nonneg, not a.e. zero (it is 1 at p and
   positive on a neighborhood), and mu is open-positive (`IsOpenPosMeasure`), so `integral g > 0`
   (e.g. `Continuous.integral_pos_iff_of_nonneg` / `setIntegral`-positivity).
 - Contradiction: the hypothesis forces the average to converge to integral g > 0, but it is constantly 0.

Keep the statement EXACTLY as below.
-/
theorem isEquidistributed_dense {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {x : ℕ → X}
    (hx : ∀ f : C(X, ℂ),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)) atTop (𝓝 (∫ y, f y ∂μ))) :
    Dense (Set.range x) := by
  sorry
