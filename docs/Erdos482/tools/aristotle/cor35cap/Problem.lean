import Mathlib
open Real
/- GOAL: St06 Cor 3.5 capstone assembly. Given the two Beatty-case digit theorems and the Beatty
uniqueness (all as axioms), prove that for every n>0 the GP recurrence from n reads digits of r√2.
This exercises the case-split / toNat bookkeeping. -/
axiom su : ℝ → ℝ → ℝ → ℝ → ℤ → ℕ → ℤ
axiom binDigit : ℝ → ℕ → ℤ
axiom beatty_unique_sqrt2 (n : ℤ) (hn : 0 < n) :
    ((∃ k > 0, (⌊(k:ℝ)*(1+Real.sqrt 2)⌋) = n) ∧ ¬ ∃ k > 0, (⌊(k:ℝ)*(1+1/Real.sqrt 2)⌋) = n)
  ∨ (¬ (∃ k > 0, (⌊(k:ℝ)*(1+Real.sqrt 2)⌋) = n) ∧ ∃ k > 0, (⌊(k:ℝ)*(1+1/Real.sqrt 2)⌋) = n)
axiom case1 (r j : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1/2) (1/2) ((r:ℤ) + ⌊Real.sqrt 2 * (r:ℝ)/2⌋) (2*(j+1)+1)
      - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1/2) (1/2) ((r:ℤ) + ⌊Real.sqrt 2 * (r:ℝ)/2⌋) (2*j+1)
      = binDigit ((r:ℝ)*Real.sqrt 2) (j+1)
axiom case2 (r j : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1/2) (1/2) (⌊Real.sqrt 2 * (r:ℝ)⌋ + (r:ℤ)) (2*(j+1)+1)
      - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1/2) (1/2) (⌊Real.sqrt 2 * (r:ℝ)⌋ + (r:ℤ)) (2*j+1)
      = binDigit ((r:ℝ)*Real.sqrt 2) (j+1)
axiom bseq1 (r:ℕ) : (⌊(↑(r:ℤ):ℝ)*(1+1/Real.sqrt 2)⌋) = (r:ℤ) + ⌊Real.sqrt 2 * (r:ℝ)/2⌋
axiom bseq2 (r:ℕ) : (⌊(↑(r:ℤ):ℝ)*(1+Real.sqrt 2)⌋) = ⌊Real.sqrt 2 * (r:ℝ)⌋ + (r:ℤ)

theorem st06_cor35 (n : ℤ) (hn : 0 < n) :
    ∃ r : ℕ, 0 < r ∧ ∀ j : ℕ,
      su (Real.sqrt 2) (Real.sqrt 2) (1/2) (1/2) n (2*(j+1)+1)
        - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1/2) (1/2) n (2*j+1)
      = binDigit ((r:ℝ)*Real.sqrt 2) (j+1) := by
  sorry
