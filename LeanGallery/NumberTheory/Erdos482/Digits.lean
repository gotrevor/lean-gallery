/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.Basic

namespace LeanGallery.NumberTheory.Erdos482
open Real

/-! ## Bridge to mathlib's canonical `Real.digits`

`Real.digits y b i = Fin.ofNat _ ⌊y · b^(i+1)⌋₊` (the base-`b` digits of `y ∈ [0,1)`).
For `x` with `1 ≤ x < 2` (so `Int.fract x = x − 1`), the `i`-th base-2 digit of `Int.fract x`
equals Stoll's floor-difference digit `⌊x·2^(i+1)⌋ − 2·⌊x·2^i⌋`.  This certifies that our
`binDigit` is the standard binary-digit notion. -/

/-- **General digit-floor identity.**  For any `y ≥ 0`, the `i`-th base-2 digit of `y` (in mathlib's
`Real.digits`) is the floor-difference `⌊y·2^(i+1)⌋ − 2·⌊y·2^i⌋` (the `y < 1` domain restriction is
not needed for this identity). -/
theorem digits_eq_floor_sub (y : ℝ) (hy0 : 0 ≤ y) (i : ℕ) :
    ((Real.digits y 2 i : ℕ) : ℤ) = ⌊y * 2 ^ (i + 1)⌋ - 2 * ⌊y * 2 ^ i⌋ := by
  set N : ℤ := ⌊y * 2 ^ (i + 1)⌋ with hN
  set M : ℤ := ⌊y * 2 ^ i⌋ with hM
  have hz : y * 2 ^ (i + 1) = 2 * (y * 2 ^ i) := by ring
  have hy := Int.floor_le (y * 2 ^ i)
  have hy' := Int.lt_floor_add_one (y * 2 ^ i)
  have hNlb : 2 * M ≤ N := by rw [hN, hz, Int.le_floor]; push_cast; linarith
  have hNub : N ≤ 2 * M + 1 := by
    have h : ⌊2 * (y * 2 ^ i)⌋ < 2 * M + 2 := by rw [Int.floor_lt]; push_cast; linarith
    rw [hN, hz]; omega
  have hdval : ((Real.digits y 2 i : ℕ) : ℤ) = ((⌊y * 2 ^ (i + 1)⌋₊ % 2 : ℕ) : ℤ) := by
    simp only [Real.digits, Fin.val_ofNat, Nat.cast_ofNat]
  have hpos : (0:ℝ) ≤ y * 2 ^ (i + 1) := mul_nonneg hy0 (by positivity)
  have hfn : (⌊y * 2 ^ (i + 1)⌋₊ : ℤ) = N := by rw [Int.natCast_floor_eq_floor hpos]
  rw [hdval]; omega

/-- The digit bridge for `1 ≤ x < 2` (so `Int.fract x = x − 1`): the `i`-th binary digit of the
fractional part equals Stoll's floor-difference `⌊x·2^(i+1)⌋ − 2·⌊x·2^i⌋`.  Certifies that
`binDigit` is the standard binary-digit notion.  A corollary of `digits_eq_floor_sub`. -/
theorem digit_bridge (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x < 2) (i : ℕ) :
    ((Real.digits (Int.fract x) 2 i : ℕ) : ℤ)
      = ⌊x * 2 ^ (i + 1)⌋ - 2 * ⌊x * 2 ^ i⌋ := by
  have hfloor : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]; refine ⟨by exact_mod_cast hx1, by push_cast; linarith⟩
  have hfr : Int.fract x = x - 1 := by rw [← Int.self_sub_floor, hfloor]; push_cast; ring
  rw [digits_eq_floor_sub (Int.fract x) (Int.fract_nonneg x), hfr,
    show (x - 1) * 2 ^ (i + 1) = x * 2 ^ (i + 1) - ((2 ^ (i + 1) : ℤ) : ℝ) by push_cast; ring,
    show (x - 1) * 2 ^ i = x * 2 ^ i - ((2 ^ i : ℤ) : ℝ) by push_cast; ring,
    Int.floor_sub_intCast, Int.floor_sub_intCast]
  have hpow : (2:ℤ) ^ (i + 1) = 2 * 2 ^ i := by ring
  omega

/-- Floor doubling: `⌊2z⌋ − 2⌊z⌋ ∈ {0,1}`. -/
theorem floor_two_mul_sub (z : ℝ) :
    ⌊2 * z⌋ - 2 * ⌊z⌋ = 0 ∨ ⌊2 * z⌋ - 2 * ⌊z⌋ = 1 := by
  have hlb : 2 * ⌊z⌋ ≤ ⌊2 * z⌋ := by
    rw [Int.le_floor]; push_cast; linarith [Int.floor_le z]
  have hub : ⌊2 * z⌋ < 2 * ⌊z⌋ + 2 := by
    rw [Int.floor_lt]; push_cast; linarith [Int.lt_floor_add_one z]
  omega

/-- `binDigit x n` is a genuine bit: it is `0` or `1` (for `n ≥ 1`). -/
theorem binDigit_mem_zero_one (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    binDigit x n = 0 ∨ binDigit x n = 1 := by
  unfold binDigit
  have hpow : (2:ℝ) * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn]
  rw [show x * 2 ^ n = 2 * (x * 2 ^ (n - 1)) by rw [← hpow]; ring]
  exact floor_two_mul_sub (x * 2 ^ (n - 1))

/-- The fractional part `√2 − 1` whose binary digits we extract is irrational — so the digit
sequence is the genuine expansion of an irrational number (non-termination: see
`digits_sqrt2_not_eventually_zero` below). -/
theorem irrational_fract_sqrt2 : Irrational (Int.fract (Real.sqrt 2)) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hfloor : ⌊Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨by push_cast; nlinarith [hs2, hsnn], by push_cast; nlinarith [hs2, hsnn]⟩
  have he : Int.fract (Real.sqrt 2) = Real.sqrt 2 - 1 := by
    rw [← Int.self_sub_floor, hfloor]; push_cast; ring
  rw [he]
  simpa using (irrational_sqrt_two).sub_natCast 1

/-- **The expansion is non-terminating.**  The binary digits of `Int.fract √2` are not eventually
zero — if they were, `√2 − 1` would be a dyadic rational, contradicting irrationality.  Hence the
Graham–Pollak difference sequence has infinitely many `1`s.  Stated generally for any irrational
`y ≥ 0` (the expansion of an irrational never terminates). -/
theorem digits_two_irrational_not_eventually_zero
    (y : ℝ) (hy0 : 0 ≤ y) (hyirr : Irrational y) :
    ¬ ∃ N, ∀ i, N ≤ i → (Real.digits y 2 i : ℕ) = 0 := by
  rintro ⟨N, hN⟩
  -- digit i = 0  ⟹  ⌊y·2^(i+1)⌋ = 2⌊y·2^i⌋
  have hstep : ∀ i, N ≤ i → ⌊y * 2 ^ (i + 1)⌋ = 2 * ⌊y * 2 ^ i⌋ := by
    intro i hi
    have h := digits_eq_floor_sub y hy0 i
    rw [hN i hi] at h
    push_cast at h; omega
  -- chain:  ⌊y·2^(N+k)⌋ = 2^k · ⌊y·2^N⌋
  have hchain : ∀ k, ⌊y * 2 ^ (N + k)⌋ = 2 ^ k * ⌊y * 2 ^ N⌋ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : ⌊y * 2 ^ (N + k + 1)⌋ = 2 * ⌊y * 2 ^ (N + k)⌋ := hstep (N + k) (by omega)
      rw [show N + (k + 1) = (N + k) + 1 from by ring, h1, ih, pow_succ]; ring
  set M : ℤ := ⌊y * 2 ^ N⌋ with hM
  set c : ℝ := (M : ℝ) / 2 ^ N with hc
  have hpowN : (0:ℝ) < 2 ^ N := by positivity
  -- c ≤ y
  have hle : c ≤ y := by
    rw [hc, div_le_iff₀ hpowN]
    have := Int.floor_le (y * 2 ^ N); rw [← hM] at this; linarith
  -- y < c + 1/2^(N+k)  for every k
  have hlt : ∀ k, y < c + 1 / 2 ^ (N + k) := by
    intro k
    have hpos : (0:ℝ) < 2 ^ (N + k) := by positivity
    have h := Int.lt_floor_add_one (y * 2 ^ (N + k))
    rw [hchain k] at h
    push_cast at h
    have hpe : (2:ℝ) ^ (N + k) = 2 ^ N * 2 ^ k := by rw [pow_add]
    have hck : c * 2 ^ (N + k) = (M : ℝ) * 2 ^ k := by rw [hc, hpe]; field_simp
    have hfin : y - c < 1 / 2 ^ (N + k) := by
      rw [lt_div_iff₀ hpos]
      have hexp : (y - c) * 2 ^ (N + k) = y * 2 ^ (N + k) - c * 2 ^ (N + k) := by ring
      rw [hexp, hck]; nlinarith [h]
    linarith [hfin]
  -- conclude y = c
  have hyc : y = c := by
    rcases lt_or_eq_of_le hle with hlt' | heq
    · exfalso
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < y - c)
        (by norm_num : (1:ℝ) / 2 < 1)
      have h2 : (1:ℝ) / 2 ^ (N + k) ≤ (1 / 2) ^ k := by
        rw [div_pow, one_pow]
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have := hlt k
      linarith [hk, h2]
    · exact heq.symm
  -- y = M/2^N is rational, contradicting irrationality
  apply hyirr
  exact ⟨(M : ℚ) / 2 ^ N, by rw [hyc, hc]; push_cast; ring⟩

/-- **The √2 expansion is non-terminating.**  Corollary of the general irrational statement: the
binary digits of `Int.fract √2` are not eventually zero, so the Graham–Pollak difference sequence
has infinitely many `1`s. -/
theorem digits_sqrt2_not_eventually_zero :
    ¬ ∃ N, ∀ i, N ≤ i → (Real.digits (Int.fract (Real.sqrt 2)) 2 i : ℕ) = 0 :=
  digits_two_irrational_not_eventually_zero _ (Int.fract_nonneg _) irrational_fract_sqrt2

/-- **No all-ones tail.**  For any `y ≥ 0`, the base-2 `Real.digits` of `y` are never eventually
`1` — the floor convention always yields the terminating-style (no `0.0111…`) representation.
This holds for every real, not just `√2`, and rules out the dyadic-tail ambiguity. -/
theorem digits_two_not_eventually_one (y : ℝ) (hy0 : 0 ≤ y) :
    ¬ ∃ N, ∀ i, N ≤ i → (Real.digits y 2 i : ℕ) = 1 := by
  rintro ⟨N, hN⟩
  have hstep : ∀ i, N ≤ i → ⌊y * 2 ^ (i + 1)⌋ = 2 * ⌊y * 2 ^ i⌋ + 1 := by
    intro i hi
    have h := digits_eq_floor_sub y hy0 i
    rw [hN i hi] at h; push_cast at h; omega
  have hchain : ∀ k, ⌊y * 2 ^ (N + k)⌋ = 2 ^ k * ⌊y * 2 ^ N⌋ + (2 ^ k - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : ⌊y * 2 ^ (N + k + 1)⌋ = 2 * ⌊y * 2 ^ (N + k)⌋ + 1 := hstep (N + k) (by omega)
      rw [show N + (k + 1) = (N + k) + 1 from by ring, h1, ih, pow_succ]; ring
  set M : ℤ := ⌊y * 2 ^ N⌋ with hM
  set c : ℝ := ((M : ℝ) + 1) / 2 ^ N with hc
  have hpowN : (0:ℝ) < 2 ^ N := by positivity
  -- y < c  (from the floor at index N)
  have hlt : y < c := by
    rw [hc, lt_div_iff₀ hpowN]
    have := Int.lt_floor_add_one (y * 2 ^ N); rw [← hM] at this; linarith
  -- c - 1/2^(N+k) ≤ y  for every k
  have hge : ∀ k, c - 1 / 2 ^ (N + k) ≤ y := by
    intro k
    have hpos : (0:ℝ) < 2 ^ (N + k) := by positivity
    have h := Int.floor_le (y * 2 ^ (N + k))
    rw [hchain k] at h
    push_cast at h
    have hpe : (2:ℝ) ^ (N + k) = 2 ^ N * 2 ^ k := by rw [pow_add]
    have hck : c * 2 ^ (N + k) = ((M : ℝ) + 1) * 2 ^ k := by rw [hc, hpe]; field_simp
    have hfin : c - y ≤ 1 / 2 ^ (N + k) := by
      rw [le_div_iff₀ hpos]
      have hexp : (c - y) * 2 ^ (N + k) = c * 2 ^ (N + k) - y * 2 ^ (N + k) := by ring
      rw [hexp, hck]; nlinarith [h]
    linarith [hfin]
  -- Archimedean: c ≤ y, contradicting y < c
  have hcle : c ≤ y := by
    by_contra hlt'
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < c - y)
      (by norm_num : (1:ℝ) / 2 < 1)
    have h2 : (1:ℝ) / 2 ^ (N + k) ≤ (1 / 2) ^ k := by
      rw [div_pow, one_pow]
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have := hge k
    linarith [hk, h2]
  linarith [hlt, hcle]

end LeanGallery.NumberTheory.Erdos482
