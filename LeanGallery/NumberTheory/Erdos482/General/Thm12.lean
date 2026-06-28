/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm13Closed

/-!
# Stoll [St05] Theorem 1.2 — binary digit extraction, two ∞-families (parameter `j`)

Theorem 1.2 gives, for every `j ∈ ℤ₊`, a binary floor-recurrence reading off the base-2 digits of any
`w > 0`.  The recurrence is `u₁ = 1`, `uₙ₊₁ = ⌊a(uₙ+½)⌋` for `n` odd, `⌊b(uₙ+ε)⌋` for `n` even, with
`b = 2/a`.  We treat **Case II** (`ε = ½`, `a = 2j − t/(t+2)`); its even-index closed form carries the
family parameter, while the odd-index closed form `u₂ₖ₊₁ = 2^k + ⌊t·2^k/2⌋` is identical to Thm 1.3 at
`g = 2`, so digit extraction reuses `thm13_digit_of_oddClosed`.

Closed forms verified numerically (`tools/sandbox/st05_thm12_verify.py`, all `j`, both cases, ε
endpoints).  `gv`-indexed (`gv m = u_{m+1}`, `u₁ = 1`):
* `gv(2k)   = 2^k + ⌊t·2^k/2⌋`                                   (odd-index, j-free)
* `gv(2k+1) = j·2^{k+1} + (2j−1)·⌊t·2^k/2⌋ + (j−1)`              (even-index, the j-family)
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- The binary two-offset recurrence of St05 Thm 1.2 (`gv a b ε m = u_{m+1}`, `u₁ = 1`): the step from
index `m` uses `(a, ½)` when `m` is even (original odd index `m+1`) and `(b, ε)` when `m` is odd. -/
noncomputable def gv (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((gv a b ε n : ℝ) + 1 / 2)⌋
      else ⌊b * ((gv a b ε n : ℝ) + ε)⌋

@[simp] theorem gv_zero (a b ε : ℝ) : gv a b ε 0 = 1 := rfl

theorem gv_succ (a b ε : ℝ) (n : ℕ) :
    gv a b ε (n + 1)
      = if Even n then ⌊a * ((gv a b ε n : ℝ) + 1 / 2)⌋ else ⌊b * ((gv a b ε n : ℝ) + ε)⌋ := rfl

/-- **Thm 1.2 Case II, even→odd step.**  At an even index the j-free value `2^k + ⌊t·2^k/2⌋` feeds the
`(a, ½)` floor and produces the j-family value `j·2^{k+1} + (2j−1)·⌊t·2^k/2⌋ + (j−1)`.  The parameter
`j` cancels in the error term `a·P − Q = 1 − (2f+t/2)/(t+2)`. -/
theorem thm12_caseII_eo (t : ℝ) (ht1 : 1 ≤ t) (_ht2 : t < 2) (j : ℕ) (_hj : 1 ≤ j)
    (a : ℝ) (ha : a = 2 * (j : ℝ) - t / (t + 2)) (k : ℕ) :
    ⌊a * ((((2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ : ℤ) : ℝ) + 1 / 2)⌋
      = (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1) := by
  have htpos : (0 : ℝ) < t + 2 := by linarith
  set m : ℤ := ⌊t * (2 : ℝ) ^ k / 2⌋ with hm
  have hlo2 : 2 * (m : ℝ) ≤ t * (2 : ℝ) ^ k := by
    have h := Int.floor_le (t * (2 : ℝ) ^ k / 2); rw [← hm] at h
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h; linarith
  have hhi2 : t * (2 : ℝ) ^ k < 2 * (m : ℝ) + 2 := by
    have h := Int.lt_floor_add_one (t * (2 : ℝ) ^ k / 2); rw [← hm] at h
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at h; linarith
  rw [Int.floor_eq_iff]
  have hPcast : ((((2 : ℤ) ^ k + m : ℤ) : ℝ)) = (2 : ℝ) ^ k + (m : ℝ) := by push_cast; ring
  rw [hPcast]
  -- the target integer, as a real
  set z : ℤ := (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * m + ((j : ℤ) - 1) with hz
  have hzcast : ((z : ℤ) : ℝ)
      = (j : ℝ) * (2 : ℝ) ^ (k + 1) + (2 * (j : ℝ) - 1) * (m : ℝ) + ((j : ℝ) - 1) := by
    rw [hz]; push_cast; ring
  -- KEY error identity: (t+2)·(a·P − z) = 2m − t·2^k + t/2 + 2
  have hkey : (t + 2) * (a * (((2 : ℝ) ^ k + (m : ℝ)) + 1 / 2) - (z : ℝ))
      = 2 * (m : ℝ) - t * (2 : ℝ) ^ k + t / 2 + 2 := by
    rw [ha, hzcast, pow_succ]; field_simp; ring
  refine ⟨?_, ?_⟩
  · -- z ≤ a·P
    nlinarith [hkey, hhi2, ht1, htpos]
  · -- a·P < z + 1
    nlinarith [hkey, hlo2, ht1, htpos]

/-- **Thm 1.2 Case II, odd→even step.**  At an odd index the j-family value feeds the `(b, ½)` floor
(`b = 2/a`) and produces the next j-free value `2^{k+1} + ⌊t·2^{k+1}/2⌋`.  The error identity
`Den·(b(Q+½) − (2^{k+1}+p)) = Den(1−p+2m) + 2t·2^k − 4m − 2` (with `Den = (2j−1)t+4j`,
`m = ⌊t·2^k/2⌋`, `p = ⌊t·2^k⌋ ∈ {2m, 2m+1}`) is exact; a case split on `p` closes the floor bound. -/
theorem thm12_caseII_oe (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (a b : ℝ) (ha : a = 2 * (j : ℝ) - t / (t + 2)) (hb : b = 2 / a) (k : ℕ) :
    ⌊b * ((((j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1) : ℤ) : ℝ)
        + 1 / 2)⌋
      = (2 : ℤ) ^ (k + 1) + ⌊t * (2 : ℝ) ^ (k + 1) / 2⌋ := by
  have htpos : (0 : ℝ) < t + 2 := by linarith
  have htne : t + 2 ≠ 0 := ne_of_gt htpos
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  -- Den = (2j−1)t + 4j ≥ 5 > 0
  set Den : ℝ := (2 * (j : ℝ) - 1) * t + 4 * j with hDen
  have hDenpos : (0 : ℝ) < Den := by rw [hDen]; nlinarith [hjR, ht1]
  have hDenne : Den ≠ 0 := ne_of_gt hDenpos
  -- a = Den/(t+2) > 0, b = 2(t+2)/Den
  have haval : a = Den / (t + 2) := by rw [ha, hDen]; field_simp; ring
  have hbval : b = 2 * (t + 2) / Den := by
    rw [hb, haval, div_div_eq_mul_div]
  have hDb : Den * b = 2 * (t + 2) := by rw [hbval]; field_simp
  -- m, p and their floor bounds
  set m : ℤ := ⌊t * (2 : ℝ) ^ k / 2⌋ with hm
  have hlo2 : 2 * (m : ℝ) ≤ t * (2 : ℝ) ^ k := by
    have h := Int.floor_le (t * (2 : ℝ) ^ k / 2); rw [← hm] at h
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h; linarith
  have hhi2 : t * (2 : ℝ) ^ k < 2 * (m : ℝ) + 2 := by
    have h := Int.lt_floor_add_one (t * (2 : ℝ) ^ k / 2); rw [← hm] at h
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at h; linarith
  have hpp : t * (2 : ℝ) ^ (k + 1) / 2 = t * (2 : ℝ) ^ k := by rw [pow_succ]; ring
  rw [hpp]
  set p : ℤ := ⌊t * (2 : ℝ) ^ k⌋ with hp
  have hplo : (p : ℝ) ≤ t * (2 : ℝ) ^ k := Int.floor_le _
  have hphi : t * (2 : ℝ) ^ k < (p : ℝ) + 1 := Int.lt_floor_add_one _
  -- p ∈ {2m, 2m+1}
  have hpge : 2 * m ≤ p := by rw [hp]; exact Int.le_floor.mpr (by push_cast; linarith [hlo2])
  have hple : p ≤ 2 * m + 1 := by
    rw [hp]; have : ⌊t * (2 : ℝ) ^ k⌋ < 2 * m + 2 := Int.floor_lt.mpr (by push_cast; linarith [hhi2])
    omega
  set Q : ℤ := (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * m + ((j : ℤ) - 1) with hQ
  have hQcast : ((Q : ℤ) : ℝ)
      = (j : ℝ) * (2 : ℝ) ^ (k + 1) + (2 * (j : ℝ) - 1) * (m : ℝ) + ((j : ℝ) - 1) := by
    rw [hQ]; push_cast; ring
  -- KEY exact identity: Den·(b(Q+½) − (2^{k+1}+p)) = Den(1−p+2m) + 2t·2^k − 4m − 2
  have hkey2 : Den * (b * ((Q : ℝ) + 1 / 2) - ((2 : ℝ) ^ (k + 1) + (p : ℝ)))
      = Den * (1 - (p : ℝ) + 2 * (m : ℝ)) + 2 * t * (2 : ℝ) ^ k - 4 * (m : ℝ) - 2 := by
    have hA : Den * (b * ((Q : ℝ) + 1 / 2)) = 2 * (t + 2) * ((Q : ℝ) + 1 / 2) := by
      rw [← mul_assoc, hDb]
    rw [mul_sub, hA, hQcast, hDen, pow_succ]; ring
  rw [Int.floor_eq_iff, show (((2 : ℤ) ^ (k + 1) + p : ℤ) : ℝ) = (2 : ℝ) ^ (k + 1) + (p : ℝ) from by
    push_cast; ring]
  -- case split on p = 2m or p = 2m+1
  rcases (by omega : p = 2 * m ∨ p = 2 * m + 1) with hpc | hpc
  · have hpcR : (p : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hpc
    refine ⟨?_, ?_⟩
    · nlinarith [hkey2, hphi, hDenpos, hlo2, hpcR]
    · nlinarith [hkey2, hlo2, hDenpos, hpcR]
  · have hpcR : (p : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hpc
    refine ⟨?_, ?_⟩
    · nlinarith [hkey2, hplo, hDenpos, hpcR]
    · nlinarith [hkey2, hhi2, hDenpos, hpcR]

/-- **St05 Theorem 1.2 Case II — the closed forms (unconditional).**  For the binary recurrence `gv`
with `a = 2j − t/(t+2)`, `b = 2/a`, `ε = ½`, mantissa `1 ≤ t < 2`, family `j ≥ 1`, both closed forms
hold. -/
theorem thm12_caseII_closed (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (a b : ℝ) (ha : a = 2 * (j : ℝ) - t / (t + 2)) (hb : b = 2 / a) :
    (∀ k, gv a b (1 / 2) (2 * k) = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋) ∧
      (∀ k, gv a b (1 / 2) (2 * k + 1)
        = (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1)) := by
  -- Q_k from P_k via the even→odd step (index 2k is Even)
  have hBfromA : ∀ k, gv a b (1 / 2) (2 * k) = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ →
      gv a b (1 / 2) (2 * k + 1)
        = (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1) := by
    intro k hAk
    have hstep : gv a b (1 / 2) (2 * k + 1) = ⌊a * ((gv a b (1 / 2) (2 * k) : ℝ) + 1 / 2)⌋ := by
      rw [gv_succ, if_pos ⟨k, two_mul k⟩]
    rw [hstep, hAk]
    exact thm12_caseII_eo t ht1 ht2 j hj a ha k
  -- P_{k+1} from Q_k via the odd→even step (index 2k+1 is Odd)
  have hAfromB : ∀ k, gv a b (1 / 2) (2 * k + 1)
        = (j : ℤ) * 2 ^ (k + 1) + (2 * j - 1) * ⌊t * (2 : ℝ) ^ k / 2⌋ + ((j : ℤ) - 1) →
      gv a b (1 / 2) (2 * (k + 1)) = (2 : ℤ) ^ (k + 1) + ⌊t * (2 : ℝ) ^ (k + 1) / 2⌋ := by
    intro k hBk
    have hodd : ¬ Even (2 * k + 1) := by
      simp only [Nat.even_add_one, not_not]; exact ⟨k, two_mul k⟩
    have hstep : gv a b (1 / 2) (2 * (k + 1))
        = ⌊b * ((gv a b (1 / 2) (2 * k + 1) : ℝ) + 1 / 2)⌋ := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring, gv_succ, if_neg hodd]
    rw [hstep, hBk]
    exact thm12_caseII_oe t ht1 ht2 j hj a b ha hb k
  -- P by induction
  have hA : ∀ k, gv a b (1 / 2) (2 * k) = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.mul_zero, gv_zero, pow_zero, mul_one]
      have hfl : ⌊t / (2 : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]
        exact ⟨by positivity, by rw [div_lt_one (by norm_num : (0 : ℝ) < 2)]; linarith⟩
      rw [hfl]; omega
    | succ n ih => exact hAfromB n (hBfromA n ih)
  exact ⟨hA, fun k => hBfromA k (hA k)⟩

/-- **St05 Theorem 1.2 Case II — digit extraction (unconditional, end to end).**  For every `j ≥ 1`,
the binary recurrence `gv (2j − t/(t+2)) (2/a) ½` reads off the base-2 digits of `w`: for `n ≥ 1`,
`gv(2n) − 2·gv(2n−2) = Real.digits (t·2^{n−1}/2) 2 0`.  Reuses the `g = 2` digit bridge
`thm13_digit_realDigits` (the odd-index closed form is shared across St05). -/
theorem thm12_caseII_digits (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (a b : ℝ) (ha : a = 2 * (j : ℝ) - t / (t + 2)) (hb : b = 2 / a) (n : ℕ) (hn : 1 ≤ n) :
    gv a b (1 / 2) (2 * n) - 2 * gv a b (1 / 2) (2 * n - 2)
      = ((Real.digits (t * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have hP := (thm12_caseII_closed t ht1 ht2 j hj a b ha hb).1
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hodd : ∀ k, (fun jj => gv a b (1 / 2) (jj - 1)) (2 * k + 1)
      = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ := by
    intro k; simpa using hP k
  have hmain := thm13_digit_realDigits 2 (by norm_num) t ht0
    (fun jj => gv a b (1 / 2) (jj - 1)) hodd n hn
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : 2 * n - 1 - 1 = 2 * n - 2 := by omega
  simp only [e1, e2] at hmain
  exact hmain

end LeanGallery.NumberTheory.Erdos482.General
