import Mathlib
open Real

/-
GOAL: The cubic three-step defect identity.  For any real α with α³ = 2, offsets c0 c1 c2 and start u,
the three nested floors v1 = ⌊α(u+c0)⌋, v2 = ⌊α(v1+c1)⌋, v3 = ⌊α(v2+c2)⌋ (all real casts of ℤ floors)
satisfy
  v3 = 2u + (2c0 + α²c1 + α·c2) − (α²·{α(u+c0)} + α·{α(v1+c1)} + {α(v2+c2)}),
where {·} = Int.fract.  This is the algebraic core localizing the cubic digit obstruction: the
three-step composite is a clean shift-by-2 modulo the combined internal-floor defect α²f1+α·f2+f3.

RECIPE: it is PURE ALGEBRA from α³=2.  Use `Int.self_sub_fract r : r − Int.fract r = ↑⌊r⌋`, so
↑⌊r⌋ = r − Int.fract r.  Introduce the three lets, then with
  h1 : v1 = α(u+c0) − {α(u+c0)}
  h2 : v2 = α(v1+c1) − {α(v1+c1)}
  h3 : v3 = α(v2+c2) − {α(v2+c2)}
(each `(Int.self_sub_fract _).symm`) close the goal by
  `linear_combination h3 + α*h2 + α^2*h1 + (u+c0)*hα`.
(The (u+c0)*hα term converts the α³(u+c0) produced by the substitution chain into 2(u+c0).)
-/

theorem cubic_threestep_defect (α u c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) :
    let v1 : ℝ := (⌊α * (u + c0)⌋ : ℤ)
    let v2 : ℝ := (⌊α * (v1 + c1)⌋ : ℤ)
    let v3 : ℝ := (⌊α * (v2 + c2)⌋ : ℤ)
    v3 = 2 * u + (2 * c0 + α ^ 2 * c1 + α * c2)
        - (α ^ 2 * Int.fract (α * (u + c0)) + α * Int.fract (α * (v1 + c1))
            + Int.fract (α * (v2 + c2))) := by
  sorry
