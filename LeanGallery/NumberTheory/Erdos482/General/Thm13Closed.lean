/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm13

/-!
# Stoll [St05] Theorem 1.3 — the closed-form joint induction (unconditional)

This module discharges the LAST remaining piece of St05 Theorem 1.3: the two closed forms of the
recurrence `gu` (defined in `General/Thm13.lean`) follow from the recurrence by joint induction.
Combined with `thm13_digit_of_oddClosed`/`thm13_digit_realDigits` this yields the **unconditional**
Theorem 1.3 (the g-ary digits of any `w > 0`).

Setup (base `g ≥ 2`, `t` = base-`g` mantissa so `1 ≤ t < g`):
`a = g/((g−1)(t+g))`, `b = (g−1)(t+g)` (so `a·b = g`), `−1/g ≤ ε < (g+1)(g−2)/g`.
Closed forms (`k ≥ 0`):  `gu(2k) = g^k + ⌊t·g^k/g⌋`  and  `(g−1)·gu(2k+1) = g^k − 1`.

The proof rests on two single-step floor identities:
* `step_eo` (even→odd, the crux): `(g−1)·⌊a·(gu(2k)+ε)⌋ = g^k − 1`.  The algebra reduces to
  `(g−1)·a·(g^k + m + ε) = g·(g^k + m + ε)/(t+g)` with `m = ⌊t·g^k/g⌋`; the parameter bounds pin
  the result into `[(g^k−1)/(g−1), (g^k−1)/(g−1)+1)`.
* `step_oe` (odd→even, exact): `b·(gu(2k+1)+1/(g−1)) = g^{k+1} + t·g^k`, so its floor is
  `g^{k+1} + ⌊t·g^k⌋ = g^{k+1} + ⌊t·g^{k+1}/g⌋`.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- `(g−1)·(∑_{i<k} g^i) = g^k − 1` (geometric sum, integer version). -/
theorem geomSumI_mul (g : ℕ) (k : ℕ) :
    ((g : ℤ) - 1) * (∑ i ∈ Finset.range k, (g : ℤ) ^ i) = (g : ℤ) ^ k - 1 := by
  rw [mul_comm]; exact geom_sum_mul (g : ℤ) k

/-- Defining equation of `gu` at a successor index. -/
theorem gu_succ (g : ℕ) (a b ε : ℝ) (n : ℕ) :
    gu g a b ε (n + 1)
      = if Even n then ⌊a * ((gu g a b ε n : ℝ) + ε)⌋
        else ⌊b * ((gu g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋ := rfl

/-- **Even→odd step** (the crux of Thm 1.3's induction).  At an even index, the recurrence value
`g^k + ⌊t·g^k/g⌋` feeds the `(a,ε)` floor and produces the geometric sum `(g^k−1)/(g−1)`, phrased
as `(g−1)·⌊…⌋ = g^k − 1`. -/
theorem step_eo (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) (k : ℕ) :
    ((g : ℤ) - 1) * ⌊a * ((((g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ : ℤ) : ℝ) + ε)⌋
      = (g : ℤ) ^ k - 1 := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have htg : (0 : ℝ) < t + g := by linarith
  set m : ℤ := ⌊t * (g : ℝ) ^ k / g⌋ with hm
  -- fractional-part facts, cleared of the /g
  have hmg_le : (m : ℝ) * (g : ℝ) ≤ t * (g : ℝ) ^ k := by
    have h := Int.floor_le (t * (g : ℝ) ^ k / g); rw [← hm] at h
    rw [le_div_iff₀ hgpos] at h; exact h
  have hmg_lt : t * (g : ℝ) ^ k < ((m : ℝ) + 1) * (g : ℝ) := by
    have h := Int.lt_floor_add_one (t * (g : ℝ) ^ k / g); rw [← hm] at h
    rw [div_lt_iff₀ hgpos] at h; exact h
  -- ε bounds, cleared of the /g
  have hgε0 : (-1 : ℝ) ≤ (g : ℝ) * ε := by
    have h := hε0; rw [div_le_iff₀ hgpos] at h; linarith
  have hgε1 : (g : ℝ) * ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) := by
    have h := hε1; rw [lt_div_iff₀ hgpos] at h; linarith
  -- the geometric-sum integer
  set S : ℤ := ∑ i ∈ Finset.range k, (g : ℤ) ^ i with hSdef
  have hScast : ((g : ℝ) - 1) * (S : ℝ) = (g : ℝ) ^ k - 1 := by
    have h2 : ((((g : ℤ) - 1) * S : ℤ) : ℝ) = (((g : ℤ) ^ k - 1 : ℤ) : ℝ) :=
      congrArg _ (geomSumI_mul g k)
    push_cast at h2; linarith
  set X : ℝ := a * ((((g : ℤ) ^ k + m : ℤ) : ℝ) + ε) with hX
  have hXcast : ((((g : ℤ) ^ k + m : ℤ) : ℝ)) = (g : ℝ) ^ k + (m : ℝ) := by push_cast; ring
  -- key identity: (g-1)·X = g·(g^k + m + ε)/(t+g)
  have hkey : ((g : ℝ) - 1) * X = (g : ℝ) * ((g : ℝ) ^ k + (m : ℝ) + ε) / (t + g) := by
    rw [hX, ha, hXcast]; field_simp
  have hfloor : ⌊X⌋ = S := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · -- (S:ℝ) ≤ X
      have hle : ((g : ℝ) - 1) * (S : ℝ) ≤ ((g : ℝ) - 1) * X := by
        rw [hScast, hkey, le_div_iff₀ htg]
        nlinarith [hmg_lt, hgε0, ht1]
      exact le_of_mul_le_mul_left hle hg1
    · -- X < S + 1
      have hlt : ((g : ℝ) - 1) * X < ((g : ℝ) - 1) * ((S : ℝ) + 1) := by
        have hRHS : ((g : ℝ) - 1) * ((S : ℝ) + 1) = (g : ℝ) ^ k - 1 + ((g : ℝ) - 1) := by
          rw [mul_add, hScast, mul_one]
        rw [hkey, hRHS, div_lt_iff₀ htg]
        nlinarith [hmg_le, hgε1, ht1, ht2,
          mul_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2) (by linarith : (0 : ℝ) ≤ t - 1)]
      exact lt_of_mul_lt_mul_left hlt (le_of_lt hg1)
  -- conclude
  rw [hX] at hfloor
  rw [hfloor, hSdef]
  exact geomSumI_mul g k

/-- **Odd→even step** (exact).  At an odd index, the recurrence value `(g^k−1)/(g−1)` feeds the
`(b, 1/(g−1))` floor and produces `g^{k+1} + ⌊t·g^{k+1}/g⌋` exactly. -/
theorem step_oe (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (b : ℝ) (hb : b = ((g : ℝ) - 1) * (t + g))
    (k : ℕ) (v : ℤ) (hv : ((g : ℤ) - 1) * v = (g : ℤ) ^ k - 1) :
    ⌊b * ((v : ℝ) + 1 / ((g : ℝ) - 1))⌋ = (g : ℤ) ^ (k + 1) + ⌊t * (g : ℝ) ^ (k + 1) / g⌋ := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hg0 : (g : ℝ) ≠ 0 := ne_of_gt hgpos
  have hvcast : ((g : ℝ) - 1) * (v : ℝ) = (g : ℝ) ^ k - 1 := by exact_mod_cast hv
  -- b·(v + 1/(g-1)) = g^{k+1} + t·g^k
  have hval : b * ((v : ℝ) + 1 / ((g : ℝ) - 1)) = (g : ℝ) ^ (k + 1) + t * (g : ℝ) ^ k := by
    rw [hb]
    have hne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
    have expand : ((g : ℝ) - 1) * (t + g) * ((v : ℝ) + 1 / ((g : ℝ) - 1))
        = (t + g) * (((g : ℝ) - 1) * (v : ℝ)) + (t + g) := by field_simp
    rw [expand, hvcast, pow_succ]; ring
  rw [hval]
  -- align the RHS digit, then peel the integer off the floor
  have hdig : ⌊t * (g : ℝ) ^ (k + 1) / g⌋ = ⌊t * (g : ℝ) ^ k⌋ := by
    rw [show t * (g : ℝ) ^ (k + 1) / g = t * (g : ℝ) ^ k from by rw [pow_succ]; field_simp]
  rw [hdig, show (g : ℝ) ^ (k + 1) = (((g : ℤ) ^ (k + 1) : ℤ) : ℝ) from by norm_cast,
    Int.floor_intCast_add]

/-- **St05 Theorem 1.3 — the closed-form joint induction (unconditional).**  For the recurrence `gu`
(with `a = g/((g−1)(t+g))`, `b = (g−1)(t+g)`, mantissa `1 ≤ t < g`, base `g ≥ 2`, offset
`−1/g ≤ ε < (g+1)(g−2)/g`), both closed forms hold. -/
theorem thm13_closed (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a b : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hb : b = ((g : ℝ) - 1) * (t + g))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) :
    (∀ k, gu g a b ε (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋) ∧
      (∀ k, ((g : ℤ) - 1) * gu g a b ε (2 * k + 1) = (g : ℤ) ^ k - 1) := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  -- B_k from A_k via step_eo (index 2k is Even)
  have hBfromA : ∀ k, gu g a b ε (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ →
      ((g : ℤ) - 1) * gu g a b ε (2 * k + 1) = (g : ℤ) ^ k - 1 := by
    intro k hAk
    have hstep : gu g a b ε (2 * k + 1) = ⌊a * ((gu g a b ε (2 * k) : ℝ) + ε)⌋ := by
      rw [gu_succ, if_pos ⟨k, two_mul k⟩]
    rw [hstep, hAk]
    exact step_eo g hg t ht1 ht2 ε a ha hε0 hε1 k
  -- A_{k+1} from B_k via step_oe (index 2k+1 is Odd)
  have hAfromB : ∀ k, ((g : ℤ) - 1) * gu g a b ε (2 * k + 1) = (g : ℤ) ^ k - 1 →
      gu g a b ε (2 * (k + 1)) = (g : ℤ) ^ (k + 1) + ⌊t * (g : ℝ) ^ (k + 1) / g⌋ := by
    intro k hBk
    have hodd : ¬ Even (2 * k + 1) := by
      simp only [Nat.even_add_one, not_not]; exact ⟨k, two_mul k⟩
    have hstep : gu g a b ε (2 * (k + 1))
        = ⌊b * ((gu g a b ε (2 * k + 1) : ℝ) + 1 / ((g : ℝ) - 1))⌋ := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring, gu_succ, if_neg hodd]
    rw [hstep]
    exact step_oe g hg t b hb k (gu g a b ε (2 * k + 1)) hBk
  -- A by induction
  have hA : ∀ k, gu g a b ε (2 * k) = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.mul_zero, gu_zero, pow_zero, mul_one]
      have hfl : ⌊t / (g : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]
        exact ⟨by positivity, by rw [div_lt_one hgpos]; linarith⟩
      rw [hfl]; omega
    | succ n ih => exact hAfromB n (hBfromA n ih)
  exact ⟨hA, fun k => hBfromA k (hA k)⟩

/-- **St05 Theorem 1.3 — unconditional, end to end.**  For the recurrence `gu` with the St05
parameters (`a = g/((g−1)(t+g))`, `b = (g−1)(t+g)`, mantissa `1 ≤ t < g`, base `g ≥ 2`, offset
`−1/g ≤ ε < (g+1)(g−2)/g`), the Graham–Pollak difference `gu(2n) − g·gu(2n−2)` (which is
`u_{2n+1} − g·u_{2n−1}` in St05's 1-indexing, since `gu m = u_{m+1}`) is exactly the leading
base-`g` digit `Real.digits (t·g^{n−1}/g) g 0`.  No `sorry`, no custom axiom: this discharges
Theorem 1.3 completely. -/
theorem thm13_digits (g : ℕ) [NeZero g] (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (ε a b : ℝ) (ha : a = (g : ℝ) / (((g : ℝ) - 1) * (t + g)))
    (hb : b = ((g : ℝ) - 1) * (t + g))
    (hε0 : -1 / (g : ℝ) ≤ ε) (hε1 : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g)
    (n : ℕ) (hn : 1 ≤ n) :
    gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hclosed := (thm13_closed g hg t ht1 ht2 ε a b ha hb hε0 hε1).1
  have ht0 : (0 : ℝ) ≤ t := by linarith
  -- view gu as the 1-indexed u via u j = gu (j-1); then u(2k+1) = gu(2k) is the odd closed form
  have hodd : ∀ k, (fun j => gu g a b ε (j - 1)) (2 * k + 1)
      = (g : ℤ) ^ k + ⌊t * (g : ℝ) ^ k / g⌋ := by
    intro k; simpa using hclosed k
  have hmain := thm13_digit_realDigits g hg t ht0 (fun j => gu g a b ε (j - 1)) hodd n hn
  -- u(2n+1) = gu(2n),  u(2n-1) = gu(2n-2)
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : 2 * n - 1 - 1 = 2 * n - 2 := by omega
  simp only [e1, e2] at hmain
  exact hmain

/-- **Capstone digit ↔ literal mantissa digit.**  The shifted digit `Real.digits (t·g^{n−1}/g) g 0`
that `thm13_digits` outputs is exactly the `(n−2)`-th mathlib base-`g` digit of the mantissa `t`
itself (for `n ≥ 2`).  So the recurrence output reads off `t`'s genuine base-`g` digits. -/
theorem digit_recon (g : ℕ) [NeZero g] (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn : 2 ≤ n) :
    ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ)
      = ((Real.digits t g (n - 2) : ℕ) : ℤ) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hg0 : (g : ℝ) ≠ 0 := by positivity
  have hpow : t * (g : ℝ) ^ (n - 1) / g = t * (g : ℝ) ^ (n - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl, pow_succ]
    field_simp
  rw [realDigits_eq_digitStep g (t * (g : ℝ) ^ (n - 1) / g) (by positivity) 0,
    realDigits_eq_digitStep g t ht (n - 2)]
  simp only [digitStep, pow_zero, mul_one, hpow]

end LeanGallery.NumberTheory.Erdos482.General
