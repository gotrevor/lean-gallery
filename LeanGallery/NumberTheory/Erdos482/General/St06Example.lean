/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm13Closed

/-!
# Stoll [St06] Example 1.1 — the ternary digits of `e` via a `π,e`-recurrence

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Example 1.1.  The showcase instance of St06's 3-parameter family (Thm 3.1):

> `v₁ = 3`,
> `v_{n+1} = ⌊ −3/(e+9) · (vₙ + π) ⌋` if `n` odd,
> `v_{n+1} = ⌊ −(e+9) · (vₙ + 1) ⌋` if `n` even.
> Then `v_{2n+1} − 3·v_{2n−1}` is the `n`-th ternary digit of `e = (2.201101121…)₃`.

This is Thm 3.1 at `g=3, m=3, l=2, k=−1`, with `w = t = e` and `ε = π`: triple `(3,2,−1) ∈ 𝒟₂⁻`,
`a = klg/((g−1)(t+mg)) = −3/(e+9)`, `b = g/a = −(e+9)`, even-step shift `l/(g−1) = 1`.  Unlike St05
(`Cor13e.lean`, which extracts the same digits from the *positive*-coefficient `gu` recurrence), this
uses **negative** coefficients and the transcendental offset `π`, with a leading term `m·gⁿ = 3·3ⁿ`
in the closed form.  Numerically verified to `n = 40` (`tools/sandbox/st06_example11_verify.py`).

The two closed forms (`su` is 0-indexed, `su n = v_{n+1}`):
* `su (2k)   = 3·3^k + ⌊e·3^k/3⌋`   (= `v_{2k+1}`, the `m·gᵏ + ⌊t·gᵏ/g⌋` odd form),
* `su (2k+1) = −(3^k + 1)`           (= `v_{2k+2}`, the `l(k·gᵏ−1)/(g−1)` even form).

Axiom-clean (inherits `[propext, Classical.choice, Quot.sound]`).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **St06 floor recurrence** (general odd-step offset `ε`, even-step shift `s`, start `m`), 0-indexed
so `su a b ε s m n = u_{n+1}`.  At index `n` it applies `(a, ε)` when `n` is even (original odd index)
and `(b, s)` when `n` is odd.  St05's `gu` is the special case `s = 1/(g−1)`, `m = 1`. -/
noncomputable def su (a b ε s : ℝ) (m : ℤ) : ℕ → ℤ
  | 0 => m
  | n + 1 =>
      if Even n then ⌊a * ((su a b ε s m n : ℝ) + ε)⌋
      else ⌊b * ((su a b ε s m n : ℝ) + s)⌋

@[simp] theorem su_zero (a b ε s : ℝ) (m : ℤ) : su a b ε s m 0 = m := rfl

theorem su_succ (a b ε s : ℝ) (m : ℤ) (n : ℕ) :
    su a b ε s m (n + 1)
      = if Even n then ⌊a * ((su a b ε s m n : ℝ) + ε)⌋
        else ⌊b * ((su a b ε s m n : ℝ) + s)⌋ := rfl

/-- **Generalized digit extraction.**  If the even-index closed form of a recurrence carries ANY
integer coefficient `c` on `gᵏ` (St06 allows the leading `m·gᵏ`, vs St05's `gᵏ`), the Graham–Pollak
difference `u(2n) − g·u(2n−2)` still reads off mathlib's leading base-`g` digit — the `c·gᵏ` term
cancels.  This is the `c`-general companion to `thm13_digit_realDigits`. -/
theorem digit_of_evenClosed_coeff (g : ℕ) [NeZero g] (hg : 2 ≤ g) (t : ℝ) (ht : 0 ≤ t) (c : ℤ)
    (u : ℕ → ℤ) (hclosed : ∀ k, u (2 * k) = c * (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋)
    (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n) - g * u (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hgne : (g : ℝ) ≠ 0 := by positivity
  have he : 2 * (j + 1) - 2 = 2 * j := by omega
  rw [he, hclosed (j + 1), hclosed j,
    realDigits_eq_digitStep g (t * (g : ℝ) ^ (j + 1 - 1) / g) (by positivity) 0]
  simp only [digitStep, pow_zero, mul_one, Nat.add_sub_cancel]
  -- align the floor argument `t·g^{j+1}/g` with `g·(t·g^j/g)`
  rw [show t * (g : ℝ) ^ (j + 1) / g = (g : ℝ) * (t * (g : ℝ) ^ j / g) by rw [pow_succ]; field_simp]
  ring

/-! ## The `e`/`π` instance (`g=3, m=3, l=2, k=−1`) -/

/-- Even→odd step (the crux floor inequality).  From the odd closed form value `3·3ᵏ + ⌊e·3ᵏ/3⌋` at
index `2k`, the `(a=−3/(e+9), ε=π)` floor lands on the even closed form `−(3ᵏ+1)`.  The two bounds use
`3 < π < 3.15` and `2 < e < 3` (the `𝒟₂⁻` ε-interval `[1, 10/3)` contains `π`). -/
theorem ex11_step_eo (k : ℕ) :
    ⌊(-3 / (Real.exp 1 + 9)) *
        (((((3 : ℤ) ^ (k + 1) + ⌊Real.exp 1 * (3 : ℝ) ^ k / 3⌋ : ℤ)) : ℝ) + Real.pi)⌋
      = -((3 : ℤ) ^ k + 1) := by
  have he2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi315 : Real.pi < 3.15 := Real.pi_lt_d2
  set e := Real.exp 1 with he
  have hD : (0 : ℝ) < e + 9 := by linarith
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set mk : ℤ := ⌊e * (3 : ℝ) ^ k / 3⌋ with hmk
  -- floor bounds on mk, cleared of the /3
  have h3mk_le : 3 * (mk : ℝ) ≤ e * (3 : ℝ) ^ k := by
    have h := Int.floor_le (e * (3 : ℝ) ^ k / 3); rw [← hmk] at h; linarith
  have h3mk_lt : e * (3 : ℝ) ^ k < 3 * (mk : ℝ) + 3 := by
    have h := Int.lt_floor_add_one (e * (3 : ℝ) ^ k / 3); rw [← hmk] at h; linarith
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · -- lower:  ↑(−(3^k+1)) ≤ (−3/(e+9))·(3^{k+1} + mk + π)
    rw [show (-3 / (e + 9)) *
          ((((3 : ℤ) ^ (k + 1) + mk : ℤ) : ℝ) + Real.pi)
        = (-3 * (((3 : ℤ) ^ (k + 1) + mk : ℤ) : ℝ) - 3 * Real.pi) / (e + 9) by ring,
      le_div_iff₀ hD]
    push_cast
    rw [pow_succ]
    nlinarith [h3mk_le, hpi315, he2]
  · -- upper:  (−3/(e+9))·(…) < ↑(−(3^k+1)) + 1
    rw [show (-3 / (e + 9)) *
          ((((3 : ℤ) ^ (k + 1) + mk : ℤ) : ℝ) + Real.pi)
        = (-3 * (((3 : ℤ) ^ (k + 1) + mk : ℤ) : ℝ) - 3 * Real.pi) / (e + 9) by ring,
      div_lt_iff₀ hD]
    push_cast
    rw [pow_succ]
    nlinarith [h3mk_lt, hpi3, he2]

/-- Odd→even step (exact).  From the even closed form `−(3ᵏ+1)` at index `2k+1`, the
`(b=−(e+9), shift 1)` floor lands exactly on the next odd closed form `3·3^{k+1} + ⌊e·3^{k+1}/3⌋`. -/
theorem ex11_step_oe (k : ℕ) :
    ⌊(-(Real.exp 1 + 9)) * (((-((3 : ℤ) ^ k + 1) : ℤ) : ℝ) + 1)⌋
      = (3 : ℤ) ^ (k + 2) + ⌊Real.exp 1 * (3 : ℝ) ^ (k + 1) / 3⌋ := by
  set e := Real.exp 1 with he
  -- value:  −(e+9)·(−(3^k+1)+1) = (e+9)·3^k = e·3^k + 3^{k+2}
  have hval : (-(e + 9)) * (((-((3 : ℤ) ^ k + 1) : ℤ) : ℝ) + 1)
      = e * (3 : ℝ) ^ k + (((3 : ℤ) ^ (k + 2) : ℤ) : ℝ) := by
    push_cast; ring
  rw [hval, Int.floor_add_intCast]
  -- ⌊e·3^k⌋ = ⌊e·3^{k+1}/3⌋
  rw [show e * (3 : ℝ) ^ (k + 1) / 3 = e * (3 : ℝ) ^ k by rw [pow_succ]; ring]
  ring

/-- **St06 Example 1.1 — the joint closed-form induction.**  For the `e`/`π` recurrence
`su (−3/(e+9)) (−(e+9)) π 1 3` both closed forms hold:
`su(2k) = 3·3ᵏ + ⌊e·3ᵏ/3⌋` and `su(2k+1) = −(3ᵏ+1)`. -/
theorem ex11_closed :
    (∀ k, su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * k)
        = (3 : ℤ) ^ (k + 1) + ⌊Real.exp 1 * (3 : ℝ) ^ k / 3⌋) ∧
      (∀ k, su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * k + 1)
        = -((3 : ℤ) ^ k + 1)) := by
  set e := Real.exp 1 with he
  set a := (-3 / (e + 9)) with ha
  set b := (-(e + 9)) with hb
  -- B_k from A_k (index 2k is even → uses a, ε=π)
  have hBfromA : ∀ k, su a b Real.pi 1 3 (2 * k) = (3 : ℤ) ^ (k + 1) + ⌊e * (3 : ℝ) ^ k / 3⌋ →
      su a b Real.pi 1 3 (2 * k + 1) = -((3 : ℤ) ^ k + 1) := by
    intro k hAk
    have hstep : su a b Real.pi 1 3 (2 * k + 1)
        = ⌊a * ((su a b Real.pi 1 3 (2 * k) : ℝ) + Real.pi)⌋ := by
      rw [su_succ, if_pos ⟨k, two_mul k⟩]
    rw [hstep, hAk, ha]; exact ex11_step_eo k
  -- A_{k+1} from B_k (index 2k+1 is odd → uses b, shift 1)
  have hAfromB : ∀ k, su a b Real.pi 1 3 (2 * k + 1) = -((3 : ℤ) ^ k + 1) →
      su a b Real.pi 1 3 (2 * (k + 1)) = (3 : ℤ) ^ (k + 2) + ⌊e * (3 : ℝ) ^ (k + 1) / 3⌋ := by
    intro k hBk
    have hodd : ¬ Even (2 * k + 1) := by simp [parity_simps]
    have hstep : su a b Real.pi 1 3 (2 * (k + 1))
        = ⌊b * ((su a b Real.pi 1 3 (2 * k + 1) : ℝ) + 1)⌋ := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring, su_succ, if_neg hodd]
    rw [hstep, hBk, hb]; exact ex11_step_oe k
  -- A by induction
  have hA : ∀ k, su a b Real.pi 1 3 (2 * k) = (3 : ℤ) ^ (k + 1) + ⌊e * (3 : ℝ) ^ k / 3⌋ := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.mul_zero, su_zero, pow_zero, mul_one]
      have hfl : ⌊e / 3⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]
        have he2 : (2 : ℝ) < e := Real.exp_one_gt_two
        have he3 : e < 3 := Real.exp_one_lt_three
        constructor <;> [linarith; linarith]
      rw [hfl]; norm_num
    | succ n ih =>
      have := hAfromB n (hBfromA n ih)
      rw [show n + 1 + 1 = n + 2 from rfl]; exact this
  exact ⟨hA, fun k => hBfromA k (hA k)⟩

/-- **St06 Example 1.1 — the ternary digits of `e` (mantissa form).**  For every `n ≥ 1`, the
Graham–Pollak difference of the `e`/`π` recurrence is exactly mathlib's leading base-`3` digit
`Real.digits (e·3^{n−1}/3) 3 0`. -/
theorem st06_example11_ternary_e (n : ℕ) (hn : 1 ≤ n) :
    su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * n)
        - 3 * su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * n - 2)
      = ((Real.digits (Real.exp 1 * (3 : ℝ) ^ (n - 1) / 3) 3 0 : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have hcl : ∀ k, su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * k)
      = (3 : ℤ) * (3 : ℤ) ^ k + ⌊Real.exp 1 * (3 : ℝ) ^ k / 3⌋ := by
    intro k; rw [ex11_closed.1 k, pow_succ]; ring
  exact digit_of_evenClosed_coeff 3 (by norm_num) (Real.exp 1) (le_of_lt (Real.exp_pos 1)) 3 _ hcl n hn

/-- **St06 Example 1.1 — literal-digit form.**  For `n ≥ 2`, the recurrence output is exactly the
`(n−2)`-th mathlib base-`3` digit of `e` itself. -/
theorem st06_example11_ternary_e_literal (n : ℕ) (hn : 2 ≤ n) :
    su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * n)
        - 3 * su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * n - 2)
      = ((Real.digits (Real.exp 1) 3 (n - 2) : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [st06_example11_ternary_e n (by omega)]
  exact digit_recon 3 (Real.exp 1) (le_of_lt (Real.exp_pos 1)) n hn

end LeanGallery.NumberTheory.Erdos482.General
