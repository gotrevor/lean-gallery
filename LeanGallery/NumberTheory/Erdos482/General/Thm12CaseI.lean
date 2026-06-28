/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Thm12

/-!
# Stoll [St05] Theorem 1.2 Case I — binary `j`-family over the ε-interval `[1/3, 2/3)`

Companion to `Thm12.lean` (Case II).  Case I uses `a = 2(j − 1/(t+2)) = 2j − 2/(t+2)`, `b = 2/a`, and
any offset `ε ∈ [1/3, 2/3)` (an interval, not a point).  The even-index closed form differs from
Case II; the odd-index one `gv(2k) = 2^k + ⌊t·2^k/2⌋` is shared (so digit extraction again reuses the
`g = 2` bridge).  `j = 1`, `t = √2` recovers Graham–Pollak (`a = b = √2`).

`gv`-indexed closed forms (`m := ⌊t·2^k/2⌋`, `p := ⌊t·2^k⌋ ∈ {2m, 2m+1}`):
* `gv(2k)   = 2^k + m`                                        (odd-index, shared)
* `gv(2k+1) = 2^k + p + (j−1)(2^{k+1} + 2m + 1)`              (even-index, the Case-I j-family)

Verified numerically (`tools/sandbox/st05_thm12_verify.py`, Case I, ε endpoints + interior).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- The Case-I even-index closed-form value (as an integer), abbreviated for reuse. -/
private noncomputable def cI (t : ℝ) (j k : ℕ) : ℤ :=
  (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k⌋ + ((j : ℤ) - 1) * (2 ^ (k + 1) + 2 * ⌊t * (2 : ℝ) ^ k / 2⌋ + 1)

/-- Floor bounds: `2m ≤ t·2^k`, `t·2^k < 2m+2`, `p ≤ t·2^k < p+1`, and `p ∈ {2m, 2m+1}`. -/
private theorem caseI_floor_facts (t : ℝ) (k : ℕ) :
    let m := ⌊t * (2 : ℝ) ^ k / 2⌋; let p := ⌊t * (2 : ℝ) ^ k⌋
    2 * (m : ℝ) ≤ t * (2 : ℝ) ^ k ∧ t * (2 : ℝ) ^ k < 2 * (m : ℝ) + 2 ∧
      (p : ℝ) ≤ t * (2 : ℝ) ^ k ∧ t * (2 : ℝ) ^ k < (p : ℝ) + 1 ∧ (p = 2 * m ∨ p = 2 * m + 1) := by
  intro m p
  have hlo2 : 2 * (m : ℝ) ≤ t * (2 : ℝ) ^ k := by
    have h := Int.floor_le (t * (2 : ℝ) ^ k / 2)
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h; linarith
  have hhi2 : t * (2 : ℝ) ^ k < 2 * (m : ℝ) + 2 := by
    have h := Int.lt_floor_add_one (t * (2 : ℝ) ^ k / 2)
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at h; linarith
  have hplo : (p : ℝ) ≤ t * (2 : ℝ) ^ k := Int.floor_le _
  have hphi : t * (2 : ℝ) ^ k < (p : ℝ) + 1 := Int.lt_floor_add_one _
  have hpc : p = 2 * m ∨ p = 2 * m + 1 := by
    have h1 : 2 * m ≤ p := Int.le_floor.mpr (by push_cast; linarith)
    have h2 : p < 2 * m + 2 := Int.floor_lt.mpr (by push_cast; linarith)
    omega
  exact ⟨hlo2, hhi2, hplo, hphi, hpc⟩

/-- **Thm 1.2 Case I, even→odd step.**  From `gv(2k) = 2^k + m`, the `(a, ½)` floor produces the
Case-I even value `cI`.  Error `a·P − C = 2^k + 2m + 1 − p − (2^{k+1}+2m+1)/(t+2)`; a `p`-split closes
it. -/
theorem thm12_caseI_eo (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (_hj : 1 ≤ j)
    (a : ℝ) (ha : a = 2 * (j : ℝ) - 2 / (t + 2)) (k : ℕ) :
    ⌊a * ((((2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ : ℤ) : ℝ) + 1 / 2)⌋ = cI t j k := by
  have htpos : (0 : ℝ) < t + 2 := by linarith
  obtain ⟨hlo2, hhi2, hplo, hphi, hpc⟩ := caseI_floor_facts t k
  set m : ℤ := ⌊t * (2 : ℝ) ^ k / 2⌋ with hm
  set p : ℤ := ⌊t * (2 : ℝ) ^ k⌋ with hp
  have hCcast : ((cI t j k : ℤ) : ℝ)
      = (2 : ℝ) ^ k + (p : ℝ) + ((j : ℝ) - 1) * ((2 : ℝ) ^ (k + 1) + 2 * (m : ℝ) + 1) := by
    rw [cI, ← hm, ← hp]; push_cast; ring
  rw [Int.floor_eq_iff,
    show (((2 : ℤ) ^ k + m : ℤ) : ℝ) = (2 : ℝ) ^ k + (m : ℝ) from by push_cast; ring]
  -- KEY: (t+2)·(a·P − C) = (t+2)(2^k + 2m + 1 − p) − (2^{k+1} + 2m + 1)
  have hkey : (t + 2) * (a * (((2 : ℝ) ^ k + (m : ℝ)) + 1 / 2) - (cI t j k : ℝ))
      = (t + 2) * ((2 : ℝ) ^ k + 2 * (m : ℝ) + 1 - (p : ℝ)) - (2 * (2 : ℝ) ^ k + 2 * (m : ℝ) + 1) := by
    rw [ha, hCcast, pow_succ]; field_simp; ring
  rcases hpc with hpc | hpc
  · have hpcR : (p : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hpc
    refine ⟨?_, ?_⟩
    · nlinarith [hkey, hlo2, htpos, hpcR]
    · nlinarith [hkey, hphi, htpos, hpcR]
  · have hpcR : (p : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hpc
    refine ⟨?_, ?_⟩
    · nlinarith [hkey, hplo, htpos, hpcR]
    · nlinarith [hkey, hhi2, htpos, hpcR]

set_option maxHeartbeats 800000 in
/-- **Thm 1.2 Case I, odd→even step** (ε-interval).  From `gv(2k+1) = cI`, the `(b, ε)` floor produces
`2^{k+1} + ⌊t·2^{k+1}/2⌋`, **uniformly for every `ε ∈ [1/3, 2/3)`**.  `Den1 := j(t+2) − 1`,
`Den1·(b(C+ε) − (2^{k+1}+p)) = −t·2^k + p + (j−1)(t+2)(2m−p) + (t+2)(j−1) + (t+2)ε`. -/
theorem thm12_caseI_oe (t : ℝ) (ht1 : 1 ≤ t) (_ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (ε a b : ℝ) (hε0 : 1 / 3 ≤ ε) (hε1 : ε < 2 / 3)
    (ha : a = 2 * (j : ℝ) - 2 / (t + 2)) (hb : b = 2 / a) (k : ℕ) :
    ⌊b * (((cI t j k : ℤ) : ℝ) + ε)⌋ = (2 : ℤ) ^ (k + 1) + ⌊t * (2 : ℝ) ^ (k + 1) / 2⌋ := by
  have htpos : (0 : ℝ) < t + 2 := by linarith
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  obtain ⟨hlo2, hhi2, hplo, hphi, hpc⟩ := caseI_floor_facts t k
  set m : ℤ := ⌊t * (2 : ℝ) ^ k / 2⌋ with hm
  set p : ℤ := ⌊t * (2 : ℝ) ^ k⌋ with hp
  set Den1 : ℝ := (j : ℝ) * (t + 2) - 1 with hDen1
  have hDpos : (0 : ℝ) < Den1 := by rw [hDen1]; nlinarith [hjR, ht1]
  have hDne : Den1 ≠ 0 := ne_of_gt hDpos
  -- a = 2·Den1/(t+2), b = (t+2)/Den1
  have haval : a = 2 * Den1 / (t + 2) := by rw [ha, hDen1]; field_simp
  have hane : a ≠ 0 := by rw [haval]; positivity
  have hbval : b = (t + 2) / Den1 := by rw [hb, haval]; field_simp
  have hDb : Den1 * b = t + 2 := by rw [hbval]; field_simp
  have hCcast : ((cI t j k : ℤ) : ℝ)
      = (2 : ℝ) ^ k + (p : ℝ) + ((j : ℝ) - 1) * ((2 : ℝ) ^ (k + 1) + 2 * (m : ℝ) + 1) := by
    rw [cI, ← hm, ← hp]; push_cast; ring
  have hpp : t * (2 : ℝ) ^ (k + 1) / 2 = t * (2 : ℝ) ^ k := by rw [pow_succ]; ring
  rw [hpp]
  rw [Int.floor_eq_iff, show (((2 : ℤ) ^ (k + 1) + p : ℤ) : ℝ) = (2 : ℝ) ^ (k + 1) + (p : ℝ) from by
    push_cast; ring]
  -- KEY identity (Den1 cleared)
  have hkey : Den1 * (b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ)))
      = -t * (2 : ℝ) ^ k + (p : ℝ) + ((j : ℝ) - 1) * (t + 2) * (2 * (m : ℝ) - (p : ℝ))
        + (t + 2) * ((j : ℝ) - 1) + (t + 2) * ε := by
    have hA : Den1 * (b * (((cI t j k : ℤ) : ℝ) + ε)) = (t + 2) * (((cI t j k : ℤ) : ℝ) + ε) := by
      rw [← mul_assoc, hDb]
    rw [mul_sub, hA, hCcast, hDen1, pow_succ]; ring
  have hje : (0 : ℝ) ≤ (t + 2) * ((j : ℝ) - 1) := mul_nonneg htpos.le (by linarith)
  have hεlo : (1 : ℝ) ≤ (t + 2) * ε := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ t + 2 - 3 by linarith) (show (0 : ℝ) ≤ ε - 1 / 3 by linarith),
      htpos, hε0, ht1]
  -- bound Den1·X directly (X := b(C+ε) − (2^{k+1}+p)); Den1 > 0 transfers the sign to X
  rcases hpc with hpc | hpc
  · have hpcR : (p : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hpc
    have hz : ((j : ℝ) - 1) * (t + 2) * (2 * (m : ℝ) - (p : ℝ)) = 0 := by rw [hpcR]; ring
    refine ⟨?_, ?_⟩
    · have hk : (0 : ℝ) ≤ Den1 * (b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ))) := by
        rw [hkey]; nlinarith [hz, hphi, hpcR, hje, hεlo]
      have hX : (0 : ℝ) ≤ b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ)) :=
        le_of_mul_le_mul_left (by rw [mul_zero]; exact hk) hDpos
      linarith
    · have hk : Den1 * (b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ))) < Den1 * 1 := by
        rw [hkey, mul_one]
        nlinarith [hz, hlo2, hpcR, htpos, mul_pos htpos (show (0 : ℝ) < 2 / 3 - ε by linarith)]
      have hX := lt_of_mul_lt_mul_left hk hDpos.le
      linarith
  · have hpcR : (p : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hpc
    have hz : ((j : ℝ) - 1) * (t + 2) * (2 * (m : ℝ) - (p : ℝ)) = -((t + 2) * ((j : ℝ) - 1)) := by
      rw [hpcR]; ring
    refine ⟨?_, ?_⟩
    · have hk : (0 : ℝ) ≤ Den1 * (b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ))) := by
        rw [hkey]; nlinarith [hz, hhi2, hpcR, hεlo]
      have hX : (0 : ℝ) ≤ b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ)) :=
        le_of_mul_le_mul_left (by rw [mul_zero]; exact hk) hDpos
      linarith
    · have hk : Den1 * (b * (((cI t j k : ℤ) : ℝ) + ε) - ((2 : ℝ) ^ (k + 1) + (p : ℝ))) < Den1 * 1 := by
        rw [hkey, mul_one]
        nlinarith [hz, hplo, hpcR, htpos, mul_pos htpos (show (0 : ℝ) < 2 / 3 - ε by linarith)]
      have hX := lt_of_mul_lt_mul_left hk hDpos.le
      linarith

/-- **St05 Theorem 1.2 Case I — the closed forms (unconditional, ε-interval).**  For the binary
recurrence `gv` with `a = 2j − 2/(t+2)`, `b = 2/a`, any `ε ∈ [1/3, 2/3)`, mantissa `1 ≤ t < 2`,
family `j ≥ 1`, both closed forms hold. -/
theorem thm12_caseI_closed (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (ε a b : ℝ) (hε0 : 1 / 3 ≤ ε) (hε1 : ε < 2 / 3)
    (ha : a = 2 * (j : ℝ) - 2 / (t + 2)) (hb : b = 2 / a) :
    (∀ k, gv a b ε (2 * k) = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋) ∧
      (∀ k, gv a b ε (2 * k + 1) = cI t j k) := by
  have hBfromA : ∀ k, gv a b ε (2 * k) = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ →
      gv a b ε (2 * k + 1) = cI t j k := by
    intro k hAk
    have hstep : gv a b ε (2 * k + 1) = ⌊a * ((gv a b ε (2 * k) : ℝ) + 1 / 2)⌋ := by
      rw [gv_succ, if_pos ⟨k, two_mul k⟩]
    rw [hstep, hAk]
    exact thm12_caseI_eo t ht1 ht2 j hj a ha k
  have hAfromB : ∀ k, gv a b ε (2 * k + 1) = cI t j k →
      gv a b ε (2 * (k + 1)) = (2 : ℤ) ^ (k + 1) + ⌊t * (2 : ℝ) ^ (k + 1) / 2⌋ := by
    intro k hBk
    have hodd : ¬ Even (2 * k + 1) := by
      simp only [Nat.even_add_one, not_not]; exact ⟨k, two_mul k⟩
    have hstep : gv a b ε (2 * (k + 1)) = ⌊b * ((gv a b ε (2 * k + 1) : ℝ) + ε)⌋ := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring, gv_succ, if_neg hodd]
    rw [hstep, hBk]
    exact thm12_caseI_oe t ht1 ht2 j hj ε a b hε0 hε1 ha hb k
  have hA : ∀ k, gv a b ε (2 * k) = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ := by
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

/-- **St05 Theorem 1.2 Case I — digit extraction (unconditional, ε-interval).**  For every `j ≥ 1` and
`ε ∈ [1/3, 2/3)`, the binary recurrence reads off the base-2 digits of `w`: for `n ≥ 1`,
`gv(2n) − 2·gv(2n−2) = Real.digits (t·2^{n−1}/2) 2 0`. -/
theorem thm12_caseI_digits (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (j : ℕ) (hj : 1 ≤ j)
    (ε a b : ℝ) (hε0 : 1 / 3 ≤ ε) (hε1 : ε < 2 / 3)
    (ha : a = 2 * (j : ℝ) - 2 / (t + 2)) (hb : b = 2 / a) (n : ℕ) (hn : 1 ≤ n) :
    gv a b ε (2 * n) - 2 * gv a b ε (2 * n - 2)
      = ((Real.digits (t * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have hP := (thm12_caseI_closed t ht1 ht2 j hj ε a b hε0 hε1 ha hb).1
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hodd : ∀ k, (fun jj => gv a b ε (jj - 1)) (2 * k + 1)
      = (2 : ℤ) ^ k + ⌊t * (2 : ℝ) ^ k / 2⌋ := by
    intro k; simpa using hP k
  have hmain := thm13_digit_realDigits 2 (by norm_num) t ht0 (fun jj => gv a b ε (jj - 1)) hodd n hn
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : 2 * n - 1 - 1 = 2 * n - 2 := by omega
  simp only [e1, e2] at hmain
  exact hmain

end LeanGallery.NumberTheory.Erdos482.General
