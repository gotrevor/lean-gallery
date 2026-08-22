import Mathlib
open Real

/- GOAL: St06 Thm 3.4 b-step "lands iff band". Given the value formula (provided as axiom `bvalue`),
prove the floor lands on the digit value 2ms+C iff frac ∈ (−d, 1−d], d=C−2B. Pure Int.floor_eq_iff +
linarith (push_cast the integer bound). -/
axiom bvalue
    (t : ℝ) (s m l k B : ℤ) (a b : ℝ) (ε : ℝ) :
    b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * ε
      = 2 * ((m * s + B : ℤ) : ℝ) + 1
        - (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
            / ((2 * k + 1) * (t + 2 * m) + 2 * l)

theorem bstep_band (t : ℝ) (s m l k B C : ℤ) (a b : ℝ) (ε : ℝ) :
    ⌊b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * ε⌋ = 2 * m * s + C
      ↔ -((C : ℝ) - 2 * B)
            < (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
                / ((2 * k + 1) * (t + 2 * m) + 2 * l)
          ∧ (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
                / ((2 * k + 1) * (t + 2 * m) + 2 * l) ≤ 1 - ((C : ℝ) - 2 * B) := by
  sorry
