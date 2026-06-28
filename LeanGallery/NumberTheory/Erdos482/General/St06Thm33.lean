/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.St06Example

/-!
# Stoll [St06] Theorem 3.3 — the binary (`g = 2`) family

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Theorem 3.3.  This is the binary analogue of Theorem 3.1 (`St06Thm31.lean`), which
explicitly **excludes** `g = 2`.  The recurrence (with `t ∈ [1,2)` the binary mantissa of `w`,
integers `m ≥ 1`, `0 ≤ l ≤ m−1`, `k ≥ 0`):

> `u₁ = m`,
> `u_{n+1} = ⌊a·(uₙ + ½)⌋`   (`n` odd),
> `u_{n+1} = ⌊b·(uₙ + ε)⌋`   (`n` even),
> with `a = 2k+1 + (t+2l)/(t+2m)`, `b = 2/a`, and the **`k`-independent** offset interval
> `½ − (2l+1)/(2(2m+1)) ≤ ε < ½ + (2l+1)/(2(2m+1))`.

Two conclusions:
* (1)  `u_{2n+1} − 2·u_{2n−1} = dₙ`                        (the `n`-th binary digit of `w`),
* (2)  `u_{2n+2} − 2·u_{2n} = d_{n+1} + k·(2dₙ − 1)`,

where `dₙ` is indexed with `d₁ = ⌊t·2⁰⌋ − 2⌊t·2^{−1}⌋` (the integer digit), the same convention as
`General/Cor13e.lean`.  `w = √2, (m,l,k) = (1,0,0), ε = ½` is the headline Graham–Pollak instance.

## Closed forms (`su` 0-indexed, `su n = u_{n+1}`, used as `su a b (1/2) ε m`)
* **odd index**   `su (2n)   = m·2ⁿ + ⌊t·2ⁿ/2⌋`                       (= `u_{2n+1}`),
* **even index**  `su (2n+1) = 2k·(m·2ⁿ+⌊t·2ⁿ/2⌋) + (m+l)·2ⁿ + ⌊t·2ⁿ⌋ + k`   (= `u_{2n+2}`).

Conclusion (1) is then `digit_of_evenClosed_coeff` (`St06Example.lean`) at `g = 2`, `c = m`.

Both closed forms verified numerically over many `(m,l,k,t,ε)` and to large `n`
(`tools/sandbox/st06_thm33_verify.py`, `/tmp/st06_*.py`).  Axiom-clean.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-! ## The two floor cruxes (abstracted over an integer `s ≥ 1` standing for `2ⁿ`).

Only the binary-digit relation `2B ≤ C ≤ 2B+1` (`B = ⌊t·s/2⌋`, `C = ⌊t·s⌋`) is used, so the cruxes
hold for **every** integer `s ≥ 1`, not just powers of two. -/

/-- **The `a`-step (odd→even) floor crux** (unconditional, no ε needed).  From the odd closed-form
value `A = m·s + B`, the `(a, ½)` floor lands on the even closed form `E = 2kA + (m+l)s + C + k`.
The reduction `(t+2m)·(a(A+½) − E) = (m−l)(t·s−C) + (1−(C−2B))(l+m+t)` is a ring identity; the bound
`∈ [0,1)` follows by the binary-digit case split `C − 2B ∈ {0,1}`. -/
theorem st06_thm33_acrux
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (s : ℤ) (_hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (_hk : 0 ≤ k)
    (B C : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (hC : (C : ℝ) ≤ t * s) (hC' : t * s < C + 1)
    (a : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) :
    ⌊a * (((m * s + B : ℤ) : ℝ) + 1 / 2)⌋ = 2 * k * (m * s + B) + (m + l) * s + C + k := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl0
  have hlmR : (l : ℝ) ≤ (m : ℝ) - 1 := by
    have : ((l : ℤ) : ℝ) ≤ (((m : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hlm
    push_cast at this; linarith
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hdenne : t + 2 * m ≠ 0 := ne_of_gt hden
  -- binary-digit bounds  2B ≤ C ≤ 2B+1
  have h2B_le : (2 * B : ℝ) ≤ t * s := by linarith
  have hts_lt : t * s < 2 * B + 2 := by linarith
  have h2BC : 2 * B ≤ C := by
    have : ((2 * B : ℤ) : ℝ) ≤ t * s := by push_cast; linarith
    have hle : (2 * B : ℤ) ≤ ⌊t * s⌋ := Int.le_floor.mpr this
    have hCeq : ⌊t * s⌋ = C := by
      rw [Int.floor_eq_iff]; exact ⟨hC, by linarith⟩
    omega
  have hCle : C ≤ 2 * B + 1 := by
    have : (C : ℝ) < 2 * B + 2 := by linarith
    have : (C : ℤ) < 2 * B + 2 := by exact_mod_cast this
    omega
  -- the floor value via Int.floor_eq_iff and the cleared identity
  rw [Int.floor_eq_iff]
  set E : ℤ := 2 * k * (m * s + B) + (m + l) * s + C + k with hE
  -- ring identity:  (t+2m)·(arg − E) = (m−l)(t·s−C) + (1−(C−2B))(l+m+t)
  have hN : (t + 2 * m) * (a * (((m * s + B : ℤ) : ℝ) + 1 / 2) - (E : ℝ))
      = ((m : ℝ) - l) * (t * s - C) + (1 - ((C : ℝ) - 2 * B)) * (l + m + t) := by
    rw [ha, hE]; push_cast; field_simp; ring
  -- bound the RHS in [0, t+2m)
  set y : ℝ := t * s - C with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hy1 : y < 1 := by rw [hy]; linarith
  have harg : a * (((m * s + B : ℤ) : ℝ) + 1 / 2) - (E : ℝ)
      = (((m : ℝ) - l) * y + (1 - ((C : ℝ) - 2 * B)) * (l + m + t)) / (t + 2 * m) := by
    rw [eq_div_iff hdenne, mul_comm]; exact hN
  -- C − 2B ∈ {0,1}  (as a real disjunction)
  have hcase : (C : ℝ) - 2 * B = 0 ∨ (C : ℝ) - 2 * B = 1 := by
    rcases (show C - 2 * B = 0 ∨ C - 2 * B = 1 from by omega) with hd | hd
    · left; have : ((C - 2 * B : ℤ) : ℝ) = 0 := by rw [hd]; norm_num
      push_cast at this; linarith
    · right; have : ((C - 2 * B : ℤ) : ℝ) = 1 := by rw [hd]; norm_num
      push_cast at this; linarith
  set q : ℝ := (((m : ℝ) - l) * y + (1 - ((C : ℝ) - 2 * B)) * (l + m + t)) / (t + 2 * m) with hq
  have hq0 : 0 ≤ q := by
    rw [hq]; apply div_nonneg _ (le_of_lt hden)
    rcases hcase with hd | hd <;> nlinarith [hy0, hy1, hmR, hlR, hlmR, ht1, hd]
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hden]
    rcases hcase with hd | hd <;> nlinarith [hy0, hy1, hmR, hlR, hlmR, ht1, hd]
  exact ⟨by linarith [harg], by linarith [harg]⟩

set_option maxHeartbeats 800000 in
/-- **The `b`-step (even→odd) floor crux** (carries the ε-interval).  From the even closed form
`E = 2kA + (m+l)s + C + k`, the `(b, ε)` floor lands on the next odd value `2ms + C`.  Numerically
verified 0/800k; mirror of `tools/aristotle/st06_thm33_bcrux`. -/
theorem st06_thm33_bcrux
    (t : ℝ) (ht1 : 1 ≤ t) (_ht2 : t < 2)
    (s : ℤ) (_hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (hk : 0 ≤ k)
    (B C : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (hC : (C : ℝ) ≤ t * s) (hC' : t * s < C + 1)
    (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - (2 * l + 1) / (2 * (2 * m + 1)) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + (2 * l + 1) / (2 * (2 * m + 1)))
    (a b : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) (hb : b = 2 / a) :
    ⌊b * (((2 * k * (m * s + B) + (m + l) * s + C + k : ℤ) : ℝ) + ε)⌋ = 2 * m * s + C := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl0
  have hlmR : (l : ℝ) ≤ (m : ℝ) - 1 := by
    have : ((l : ℤ) : ℝ) ≤ (((m : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hlm
    push_cast at this; linarith
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hdenne : t + 2 * m ≠ 0 := ne_of_gt hden
  -- a > 0, b > 0
  have hfrac_pos : (0 : ℝ) < (t + 2 * l) / (t + 2 * m) := div_pos (by linarith) hden
  have ha_pos : (0 : ℝ) < a := by rw [ha]; linarith
  have hane : a ≠ 0 := ne_of_gt ha_pos
  -- binary-digit bounds  2B ≤ C ≤ 2B+1
  have h2B_le : (2 * B : ℝ) ≤ t * s := by linarith
  have h2BC : 2 * B ≤ C := by
    have hle : (2 * B : ℤ) ≤ ⌊t * s⌋ := Int.le_floor.mpr (by push_cast; linarith)
    have hCeq : ⌊t * s⌋ = C := by rw [Int.floor_eq_iff]; exact ⟨hC, by linarith⟩
    omega
  have hCle : C ≤ 2 * B + 1 := by
    have : (C : ℤ) < 2 * B + 2 := by
      have : (C : ℝ) < 2 * B + 2 := by linarith
      exact_mod_cast this
    omega
  -- Da := (2k+1)(t+2m)+(t+2l) > 0, and b = 2(t+2m)/Da
  set Da : ℝ := (2 * k + 1) * (t + 2 * m) + (t + 2 * l) with hDa
  have hDa_pos : (0 : ℝ) < Da := by rw [hDa]; nlinarith [hkR, hden, ht1, hlR]
  have hDane : Da ≠ 0 := ne_of_gt hDa_pos
  have ha_eq : a = Da / (t + 2 * m) := by rw [ha, hDa]; field_simp
  have hb_eq : b = 2 * (t + 2 * m) / Da := by rw [hb, ha_eq, div_div_eq_mul_div]
  -- y := t·s − C ∈ [0,1)
  set y : ℝ := t * s - C with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hy1 : y < 1 := by rw [hy]; linarith
  -- digit as a real disjunction
  have hcase : (C : ℝ) - 2 * B = 0 ∨ (C : ℝ) - 2 * B = 1 := by
    rcases (show C - 2 * B = 0 ∨ C - 2 * B = 1 from by omega) with hd | hd
    · left; have : ((C - 2 * B : ℤ) : ℝ) = 0 := by rw [hd]; norm_num
      push_cast at this; linarith
    · right; have : ((C - 2 * B : ℤ) : ℝ) = 1 := by rw [hd]; norm_num
      push_cast at this; linarith
  set Nq : ℝ := ((m : ℝ) - l) * y + (1 - ((C : ℝ) - 2 * B)) * (l + m + t) with hNq
  -- the cleared a-step identity:  (t+2m)·E = Da·(A + ½) − Nq  (pure ring identity)
  have hclear : (t + 2 * m) * ((2 * k * (m * s + B) + (m + l) * s + C + k : ℤ) : ℝ)
      = Da * (((m * s + B : ℤ) : ℝ) + 1 / 2) - Nq := by
    rw [hDa, hNq, hy]; push_cast; ring
  -- value of the b-step argument:  b·(E+ε) = 2(ms+B)+1 − (2·Nq − 2(t+2m)ε)/Da
  have hval : b * (((2 * k * (m * s + B) + (m + l) * s + C + k : ℤ) : ℝ) + ε)
      = 2 * (((m * s + B : ℤ) : ℝ)) + 1 - (2 * Nq - 2 * (t + 2 * m) * ε) / Da := by
    rw [hb_eq, div_mul_eq_mul_div, eq_sub_iff_add_eq, ← add_div, div_eq_iff hDane]
    linear_combination (2 : ℝ) * hclear
  -- cleared ε bounds + ε ≥ 0
  have h2m1 : (0 : ℝ) < 2 * (2 * m + 1) := by linarith
  have hεlo2 : (1 / 2 - ε) * (2 * (2 * m + 1)) ≤ 2 * l + 1 :=
    (le_div_iff₀ h2m1).mp (by linarith)
  have hεhi2 : (ε - 1 / 2) * (2 * (2 * m + 1)) < 2 * l + 1 :=
    (lt_div_iff₀ h2m1).mp (by linarith)
  have hε0 : 0 ≤ ε := by nlinarith [hεlo2, hmR, hlmR]
  have hε1 : ε ≤ 1 := by nlinarith [hεhi2, hmR, hlmR]
  -- the two key bounds (no `s` left — only `y ∈ [0,1)`)
  have hpk : (0 : ℝ) ≤ (k : ℝ) * (t + 2 * m) := mul_nonneg hkR (le_of_lt hden)
  have hpy : (0 : ℝ) ≤ ((m : ℝ) - l) * (1 - y) :=
    mul_nonneg (by linarith) (by linarith)
  have hpe : (0 : ℝ) ≤ ε * (t - 1) := mul_nonneg hε0 (by linarith)
  have hp1 : (0 : ℝ) ≤ (t - 1) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
  have hL : 2 * Nq - 2 * (t + 2 * m) * ε ≤ (1 - ((C : ℝ) - 2 * B)) * Da := by
    rw [hNq, hDa]
    rcases hcase with hd | hd <;> rw [hd] <;> nlinarith [hεlo2, hpk, hpy, hpe, hmR, hlmR]
  have hU : -(((C : ℝ) - 2 * B)) * Da < 2 * Nq - 2 * (t + 2 * m) * ε := by
    rw [hNq, hDa]
    rcases hcase with hd | hd <;> rw [hd] <;> nlinarith [hεhi2, hpk, hpy, hp1, hmR, hlmR, hy0]
  -- assemble the floor equality
  rw [Int.floor_eq_iff, hval]
  have hfrac_lo : (2 * Nq - 2 * (t + 2 * m) * ε) / Da ≤ 1 - ((C : ℝ) - 2 * B) :=
    (div_le_iff₀ hDa_pos).mpr (by linarith [hL])
  have hfrac_hi : -(((C : ℝ) - 2 * B)) < (2 * Nq - 2 * (t + 2 * m) * ε) / Da :=
    (lt_div_iff₀ hDa_pos).mpr (by linarith [hU])
  constructor
  · push_cast; linarith [hfrac_lo]
  · push_cast; linarith [hfrac_hi]

/-! ## The closed forms and the two digit conclusions -/

/-- **St06 Theorem 3.3 — joint closed-form induction** (binary `g = 2`).  Using `su a b (1/2) ε m`
(the `a`-step carries the fixed shift `½`, the `b`-step the variable offset `ε`), both closed forms
hold: the odd-index `su(2j) = m·2ʲ + ⌊t·2ʲ/2⌋` and the even-index
`su(2j+1) = 2k(m·2ʲ+⌊t·2ʲ/2⌋) + (m+l)·2ʲ + ⌊t·2ʲ⌋ + k`.  Interleaved induction: `acrux` lifts the
odd form to the even form, `bcrux` lifts the even form to the next odd form. -/
theorem st06_thm33_closed (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (hk : 0 ≤ k)
    (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - (2 * l + 1) / (2 * (2 * m + 1)) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + (2 * l + 1) / (2 * (2 * m + 1)))
    (a b : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) (hb : b = 2 / a) :
    (∀ j, su a b (1 / 2) ε m (2 * j) = m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) ∧
      (∀ j, su a b (1 / 2) ε m (2 * j + 1)
        = 2 * k * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + (m + l) * 2 ^ j + ⌊t * (2 : ℝ) ^ j⌋ + k) := by
  have hone : ∀ j : ℕ, (1 : ℤ) ≤ 2 ^ j := fun j => one_le_pow₀ (by norm_num)
  have hsR : ∀ j : ℕ, ((2 ^ j : ℤ) : ℝ) = (2 : ℝ) ^ j := fun j => by push_cast; ring
  -- odd-form induction (uses both cruxes in the step)
  have hA : ∀ j, su a b (1 / 2) ε m (2 * j) = m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋ := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.mul_zero, su_zero, pow_zero, mul_one]
      have hfl : ⌊t / (2 : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
      rw [hfl]; ring
    | succ j ih =>
      -- the two floors at scale 2^j
      have hB : ((⌊t * (2 : ℝ) ^ j / 2⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) / 2 := by
        rw [hsR]; exact Int.floor_le _
      have hB' : t * ((2 ^ j : ℤ) : ℝ) / 2 < ⌊t * (2 : ℝ) ^ j / 2⌋ + 1 := by
        rw [hsR]; exact Int.lt_floor_add_one _
      have hC : ((⌊t * (2 : ℝ) ^ j⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) := by
        rw [hsR]; exact Int.floor_le _
      have hC' : t * ((2 ^ j : ℤ) : ℝ) < ⌊t * (2 : ℝ) ^ j⌋ + 1 := by
        rw [hsR]; exact Int.lt_floor_add_one _
      -- su(2j+1) via acrux
      have hsu1 : su a b (1 / 2) ε m (2 * j + 1)
          = 2 * k * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + (m + l) * 2 ^ j + ⌊t * (2 : ℝ) ^ j⌋ + k := by
        rw [su_succ, if_pos ⟨j, two_mul j⟩, ih]
        exact st06_thm33_acrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl0 hlm hk
          ⌊t * (2 : ℝ) ^ j / 2⌋ ⌊t * (2 : ℝ) ^ j⌋ hB hB' hC hC' a ha
      -- su(2(j+1)) via bcrux
      have hsu2 : su a b (1 / 2) ε m (2 * (j + 1))
          = 2 * m * 2 ^ j + ⌊t * (2 : ℝ) ^ j⌋ := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring, su_succ,
          if_neg (by simp [parity_simps]), hsu1]
        exact st06_thm33_bcrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl0 hlm hk
          ⌊t * (2 : ℝ) ^ j / 2⌋ ⌊t * (2 : ℝ) ^ j⌋ hB hB' hC hC' ε hεlo hεhi a b ha hb
      -- align with the closed form at j+1
      have hfl2 : ⌊t * (2 : ℝ) ^ (j + 1) / 2⌋ = ⌊t * (2 : ℝ) ^ j⌋ := by
        congr 1; rw [pow_succ]; ring
      rw [hsu2, hfl2, pow_succ]; ring
  refine ⟨hA, fun j => ?_⟩
  -- even form: re-run the acrux step off `hA j`
  have hB : ((⌊t * (2 : ℝ) ^ j / 2⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) / 2 := by
    rw [hsR]; exact Int.floor_le _
  have hB' : t * ((2 ^ j : ℤ) : ℝ) / 2 < ⌊t * (2 : ℝ) ^ j / 2⌋ + 1 := by
    rw [hsR]; exact Int.lt_floor_add_one _
  have hC : ((⌊t * (2 : ℝ) ^ j⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) := by
    rw [hsR]; exact Int.floor_le _
  have hC' : t * ((2 ^ j : ℤ) : ℝ) < ⌊t * (2 : ℝ) ^ j⌋ + 1 := by
    rw [hsR]; exact Int.lt_floor_add_one _
  rw [su_succ, if_pos ⟨j, two_mul j⟩, hA j]
  exact st06_thm33_acrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl0 hlm hk
    ⌊t * (2 : ℝ) ^ j / 2⌋ ⌊t * (2 : ℝ) ^ j⌋ hB hB' hC hC' a ha

/-- **St06 Theorem 3.3, conclusion (1)** — the Graham–Pollak difference of the odd-index subsequence
reads off `w`'s `n`-th binary digit (mathlib `Real.digits` form):
`su(2n) − 2·su(2n−2) = digits (t·2^{n−1}/2) 2 0`.  `w=√2, (m,l,k)=(1,0,0), ε=½` is Graham–Pollak. -/
theorem st06_thm33_digits (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (hk : 0 ≤ k)
    (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - (2 * l + 1) / (2 * (2 * m + 1)) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + (2 * l + 1) / (2 * (2 * m + 1)))
    (a b : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) ε m (2 * n) - 2 * su a b (1 / 2) ε m (2 * n - 2)
      = ((Real.digits (t * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hclosed := (st06_thm33_closed t ht1 ht2 m l k hm hl0 hlm hk ε hεlo hεhi a b ha hb).1
  have := digit_of_evenClosed_coeff 2 (le_refl 2) t ht0 m _ hclosed n hn
  simpa using this

/-- **St06 Theorem 3.3 — the Graham–Pollak difference is a genuine bit** (`0` or `1`): the conclusion-(1)
digit is a base-2 `Real.digits` value, hence `< 2`. -/
theorem st06_thm33_isBit (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (hk : 0 ≤ k)
    (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - (2 * l + 1) / (2 * (2 * m + 1)) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + (2 * l + 1) / (2 * (2 * m + 1)))
    (a b : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) ε m (2 * n) - 2 * su a b (1 / 2) ε m (2 * n - 2) = 0 ∨
      su a b (1 / 2) ε m (2 * n) - 2 * su a b (1 / 2) ε m (2 * n - 2) = 1 := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  rw [st06_thm33_digits t ht0 ht1 ht2 m l k hm hl0 hlm hk ε hεlo hεhi a b ha hb n hn,
    realDigits_eq_digitStep 2 (t * (2 : ℝ) ^ (n - 1) / 2) (by positivity) 0]
  simp only [pow_zero, mul_one]
  obtain ⟨h0, h2⟩ := digitStep_mem 2 (by norm_num) (t * (2 : ℝ) ^ (n - 1) / 2)
  omega

/-- **St06 Theorem 3.3, conclusion (2)** — the Graham–Pollak difference of the *even*-index
subsequence carries the extra `k`-term:  `su(2n+1) − 2·su(2n−1) = d_{n+1} + k·(2·dₙ − 1)`, where
`dⱼ = ⌊t·2ʲ⌋ − 2⌊t·2ʲ/2⌋` is the `j`-th binary digit.  (Pure algebra from the even closed form.) -/
theorem st06_thm33_even_digits (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 ≤ l) (hlm : l ≤ m - 1) (hk : 0 ≤ k)
    (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - (2 * l + 1) / (2 * (2 * m + 1)) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + (2 * l + 1) / (2 * (2 * m + 1)))
    (a b : ℝ) (ha : a = (2 * k + 1) + (t + 2 * l) / (t + 2 * m)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) ε m (2 * n + 1) - 2 * su a b (1 / 2) ε m (2 * n - 1)
      = (⌊t * (2 : ℝ) ^ n⌋ - 2 * ⌊t * (2 : ℝ) ^ n / 2⌋)
        + k * (2 * (⌊t * (2 : ℝ) ^ (n - 1)⌋ - 2 * ⌊t * (2 : ℝ) ^ (n - 1) / 2⌋) - 1) := by
  have hE := (st06_thm33_closed t ht1 ht2 m l k hm hl0 hlm hk ε hεlo hεhi a b ha hb).2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hfl : ⌊t * (2 : ℝ) ^ (n' + 1) / 2⌋ = ⌊t * (2 : ℝ) ^ n'⌋ := by congr 1; rw [pow_succ]; ring
  rw [hE (n' + 1), show 2 * (n' + 1) - 1 = 2 * n' + 1 from by omega, hE n',
    show n' + 1 - 1 = n' from by omega, hfl, pow_succ]
  ring

/-- **Cross-check: Graham–Pollak is the `(m,l,k) = (1,0,0)`, `ε = ½`, `w = √2` instance.**  Then
`a = 1 + √2/(√2+2)`, `b = 2/a`, and `st06_thm33_digits` reproduces the binary digits of `√2` — the
headline result.  `ε = ½ ∈ [⅓, ⅔)` is the offset interval `½ ± (2·0+1)/(2(2·1+1)) = ½ ± ⅙`. -/
theorem st06_thm33_grahampollak
    (a b : ℝ) (ha : a = 1 + Real.sqrt 2 / (Real.sqrt 2 + 2)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) (1 / 2) 1 (2 * n) - 2 * su a b (1 / 2) (1 / 2) 1 (2 * n - 2)
      = ((Real.digits (Real.sqrt 2 * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt h2, Real.sqrt_nonneg 2]
  have hs2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt h2, Real.sqrt_nonneg 2]
  exact st06_thm33_digits (Real.sqrt 2) (by linarith) hs1 hs2 1 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num) a b
    (by rw [ha]; push_cast; ring) hb n hn

end LeanGallery.NumberTheory.Erdos482.General
