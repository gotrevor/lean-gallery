import Mathlib
open MeasureTheory Filter Set

/-
GOAL: Transfer "a.e. dense doubling orbit on the circle ℝ/ℤ" to the REAL LINE: for almost every real
t (w.r.t. Lebesgue measure), the set of fractional parts {Int.fract (2^n * t) : n ∈ ℕ} is dense in the
unit interval Icc (0:ℝ) 1.  This is the ℝ-line form of the doubling-orbit density used on the cubic
self-referential frontier (Erdős #482 / Stoll), where the block orbit u_n = ⌊W·2^n⌋ makes the internal
floor errors functions of {2^n · (αW)}.

The circle result is provided as an axiom `ae_dense_orbit_circle` (already proved in our repo,
General/DoublingOrbit.lean, via AddCircle.ergodic_nsmul): a.e. x : AddCircle (1:ℝ) has dense forward
orbit under y ↦ 2•y.

RECIPE: Let π : ℝ → AddCircle (1:ℝ) be the quotient projection `(↑· : ℝ → AddCircle 1)`.  Then π is
measure-preserving from volume on Ioc 0 1 (or the standard fundamental domain) to volume on AddCircle 1
(`AddCircle.measurePreserving_mk` / `QuotientAddGroup` Haar pushforward).  Under π, the doubling map on
ℝ (t ↦ 2t) intertwines with y ↦ 2•y: π (2*t) = 2 • (π t), so π (2^n * t) = (y ↦ 2•y)^[n] (π t).  Pull the
a.e. circle-density back along the measure-preserving π to get a.e. t : ℝ with {π (2^n t)} dense in
AddCircle 1.  Finally transfer density through the section AddCircle 1 → [0,1): density of {π(2^n t)} in
the (compact, connected) circle gives density of the fractional parts {Int.fract (2^n t)} in [0,1] —
for any y ∈ [0,1) and ε>0 there is n with π(2^n t) within ε of π y, i.e. Int.fract (2^n t) within ε of y
modulo the 0~1 seam (handle the seam by also approximating near the endpoints).  Use
`AddCircle.coe_eq_coe_iff`, `Int.fract`, and continuity of π.

NOTE: It is acceptable to instead prove the slightly weaker but equally useful statement that the orbit
{(↑(2^n * t) : AddCircle (1:ℝ)) : n} is dense for a.e. t : ℝ (pure pullback, skipping the fract seam),
if the seam transfer proves long.  Either form discharges the goal-of-record; pick the cleaner one.
-/

axiom ae_dense_orbit_circle :
    ∀ᵐ x : AddCircle (1:ℝ) ∂volume,
      Dense (Set.range (fun n : ℕ => (fun y : AddCircle (1:ℝ) => (2:ℕ) • y)^[n] x))

theorem ae_fract_dense_real :
    ∀ᵐ t : ℝ ∂volume,
      Dense (Set.range (fun n : ℕ => ((2 ^ n * t : ℝ) : AddCircle (1:ℝ)))) := by
  sorry
