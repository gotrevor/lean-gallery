/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.Crux

/-!
# The self-referential digit crux is exactly the √2 / base-2 phenomenon

**Context.** The headline Graham–Pollak result rests on `LeanGallery.NumberTheory.Erdos482.crux`: the *self-referential*
inequality `0 ≤ {x} − √2·{x/2} + √2/2 < 1`, where the recurrence's own coefficient `√2` equals the
algebraic generator of the number whose digits it reads.  A natural question (cf.
`notes/CUBIC-EXPLORATION.md`): does this self-reference generalize to other bases `g` — i.e. does
`u ↦ ⌊√g·(u + c)⌋` read base-`g` digits, via a `g`-analogue crux

> `0 ≤ {x} − √g·{x/g} + c·√g < 1`   for all `x`?

**Answer: NO for every `g ≥ 3`, for ANY offset `c`** (`selfref_crux_fails_of_three_le`).  Combined
with `LeanGallery.NumberTheory.Erdos482.crux` (the `g = 2`, `c = ½` case) this pins the phenomenon down completely: the elegant
self-referential digit extraction exists **iff `g = 2`** — it is a genuinely quadratic, base-2
miracle, not the tip of a tower of base-`g` analogues.  (Stoll's general St05/St06 results read *any*
real's base-`g` digits, but with a `w`-tuned rational coefficient, never the self-referential `√g`.)

**Proof idea.**  Two witnesses pin `c` between incompatible bounds when `g ≥ 3`:
* `x = g − 1`  has `{x} = 0`, `{x/g} = (g−1)/g`, so the lower bound forces `c·√g ≥ √g·(g−1)/g`,
  i.e. `c ≥ (g−1)/g`;
* `x = ½`  has `{x} = ½`, `{x/g} = 1/(2g)`, so the upper bound needs `½ − √g/(2g) + c·√g < 1`.
Substituting `c ≥ (g−1)/g` and `√g·√g = g` reduces the two to `2g − √g − 3 < 0`, which is false for
`g ≥ 3` (there `√g < g`, so `2g − √g − 3 > g − 3 ≥ 0`).  No `c` survives.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **The self-referential crux fails for every base `g ≥ 3`.**  For each integer `g ≥ 3` and each
offset `c`, there is a real `x` for which the `g`-analogue crux
`0 ≤ {x} − √g·{x/g} + c·√g < 1` is violated.  So no `u ↦ ⌊√g·(u + c)⌋` recurrence can read base-`g`
digits the way `⌊√2·(u + ½)⌋` reads base-2 digits.  (`g = 2`, `c = ½` is `LeanGallery.NumberTheory.Erdos482.crux`.) -/
theorem selfref_crux_fails_of_three_le (g : ℕ) (hg : 3 ≤ g) (c : ℝ) :
    ∃ x : ℝ, ¬ (0 ≤ Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g ∧
        Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g < 1) := by
  -- `s = √g` facts
  set s : ℝ := Real.sqrt g with hsdef
  have hgR3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgRpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgRpos
  have hs2 : s ^ 2 = (g : ℝ) := Real.sq_sqrt (le_of_lt hgRpos)
  have hspos : 0 < s := Real.sqrt_pos.mpr hgRpos
  have hs_gt1 : 1 < s := by nlinarith [hs2, hgR3, hspos]
  have hs_lt_g : s < (g : ℝ) := by nlinarith [hs2, mul_pos hspos (show (0 : ℝ) < s - 1 by linarith)]
  by_contra h
  push Not at h
  -- witness A : x = g − 1  ⇒  lower bound forces  s·(g−1) ≤ c·s·g
  have hA := h ((g : ℝ) - 1)
  have hfA1 : Int.fract ((g : ℝ) - 1) = 0 := by
    have heq : ((g : ℝ) - 1) = ((g - 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ g := by omega
      push_cast [h1]; ring
    rw [heq, Int.fract_natCast]
  have hfA2 : Int.fract (((g : ℝ) - 1) / g) = ((g : ℝ) - 1) / g := by
    apply Int.fract_eq_self.mpr
    refine ⟨div_nonneg (by linarith) (le_of_lt hgRpos), ?_⟩
    rw [div_lt_one hgRpos]; linarith
  rw [hfA1, hfA2] at hA
  have hA' : s * (((g : ℝ) - 1) / g) ≤ c * s := by linarith [hA.1]
  have hAg : s * ((g : ℝ) - 1) ≤ c * s * g := by
    rw [show s * (((g : ℝ) - 1) / g) = (s * ((g : ℝ) - 1)) / g by ring, div_le_iff₀ hgRpos] at hA'
    linarith [hA']
  -- witness B : x = 1/2  ⇒  upper bound  g − s + 2·c·s·g < 2g
  have hB := h (1 / 2)
  have hfB1 : Int.fract ((1 : ℝ) / 2) = 1 / 2 := Int.fract_eq_self.mpr (by constructor <;> norm_num)
  have hfB2 : Int.fract ((1 / 2 : ℝ) / g) = (1 / 2 : ℝ) / g := by
    apply Int.fract_eq_self.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hgRpos]; linarith
  rw [hfB1, hfB2] at hB
  have hB' : (g : ℝ) - s + 2 * (c * s * g) < 2 * g := by
    have heq : (1 / 2 - s * ((1 / 2 : ℝ) / g) + c * s) * (2 * g)
        = (g : ℝ) - s + 2 * (c * s * g) := by field_simp
    have h2g : (0 : ℝ) < 2 * g := by linarith
    nlinarith [mul_lt_mul_of_pos_right hB.2 h2g, heq]
  -- combine:  2·(s·g) − 3s − g < 0, then  2g − s − 3 < 0, false for g ≥ 3
  have hlin : 2 * (s * g) - 3 * s - (g : ℝ) < 0 := by nlinarith [hAg, hB']
  have hkey : 2 * (g : ℝ) - s - 3 < 0 := by
    by_contra hcon
    push Not at hcon
    have hmul : 0 ≤ s * (2 * (g : ℝ) - s - 3) := mul_nonneg (le_of_lt hspos) hcon
    nlinarith [hmul, hlin, hs2]
  nlinarith [hkey, hs_lt_g, hgR3]

/-- **Characterization: the self-referential digit crux is solvable iff the base is 2.**  For an
integer base `g ≥ 2`, there exists an offset `c` making `0 ≤ {x} − √g·{x/g} + c·√g < 1` hold for
**all** `x` **iff `g = 2`** (and then `c = ½` works, by `LeanGallery.NumberTheory.Erdos482.crux`).  This is the exact sense in
which Graham–Pollak's `⌊√2·(u + ½)⌋` digit recurrence is a one-off: no base `g ≥ 3` admits the
analogous self-referential extractor. -/
theorem selfref_crux_solvable_iff (g : ℕ) (hg : 2 ≤ g) :
    (∃ c : ℝ, ∀ x : ℝ, 0 ≤ Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g ∧
        Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g < 1) ↔ g = 2 := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hne
    obtain ⟨x, hx⟩ := selfref_crux_fails_of_three_le g (by omega) c
    exact hx (hc x)
  · rintro rfl
    refine ⟨1 / 2, fun x => ?_⟩
    have h := LeanGallery.NumberTheory.Erdos482.crux x
    have e1 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e1]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The offset is unique: `c = ½` is forced for `g = 2`.**  If `0 ≤ {x} − √2·{x/2} + c·√2 < 1`
holds for **all** `x`, then `c = ½`.  Lower bound `c ≥ ½` from `x = 1`; upper bound `c ≤ ½` from the
family `x = 1 − t` (`t ↓ 0`), whose upper crux gives `c·√2 < √2/2 + t·(1 − √2/2)` and hence `c ≤ ½`
in the limit.  Together with `selfref_crux_solvable_iff`: Graham–Pollak's `⌊√2·(u + ½)⌋` is the unique
self-referential base-`g` digit recurrence — both the base (`2`) and the offset (`½`) are forced. -/
theorem selfref_crux_offset_unique (c : ℝ)
    (hc : ∀ x : ℝ, 0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + c * Real.sqrt 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + c * Real.sqrt 2 < 1) :
    c = 1 / 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hspos]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  set s : ℝ := Real.sqrt 2 with hsdef
  -- lower bound : x = 1
  have hlo : 1 / 2 ≤ c := by
    have h1 := hc 1
    have hf1 : Int.fract (1 : ℝ) = 0 := by rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num,
      Int.fract_natCast]
    have hf2 : Int.fract ((1 : ℝ) / 2) = 1 / 2 := Int.fract_eq_self.mpr (by constructor <;> norm_num)
    rw [hf1, hf2] at h1
    nlinarith [h1.1, hspos]
  -- upper bound : x = 1 − t, t ↓ 0
  have hhi : c ≤ 1 / 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    set K : ℝ := (1 - s / 2) / s with hK
    have hKpos : 0 < K := by rw [hK]; exact div_pos (by linarith) hspos
    set t : ℝ := min (ε / K) (1 / 2) with ht
    have htpos : 0 < t := lt_min (div_pos hε hKpos) (by norm_num)
    have htle : t ≤ ε / K := min_le_left _ _
    have ht12 : t ≤ 1 / 2 := min_le_right _ _
    have hx := hc (1 - t)
    have hf1 : Int.fract (1 - t) = 1 - t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hf2 : Int.fract ((1 - t) / 2) = (1 - t) / 2 :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf1, hf2] at hx
    -- hx.2 : (1 − t) − s·((1−t)/2) + c·s < 1, i.e. c·s < s/2 + t·(1 − s/2)
    have hcs : c * s < s / 2 + t * (1 - s / 2) := by nlinarith [hx.2]
    -- t·(1 − s/2) ≤ ε·s   (from t ≤ ε/K and K = (1 − s/2)/s)
    have htK : t * (1 - s / 2) ≤ ε * s := by
      have h1 : t * (1 - s / 2) ≤ (ε / K) * (1 - s / 2) :=
        mul_le_mul_of_nonneg_right htle (by linarith)
      have h1s : (1 : ℝ) - s / 2 ≠ 0 := by linarith
      have h2 : (ε / K) * (1 - s / 2) = ε * s := by
        rw [hK, div_div_eq_mul_div, div_mul_cancel₀ _ h1s]
      linarith [h1, h2.le, h2.ge]
    nlinarith [hcs, htK, hspos]
  linarith [hlo, hhi]

/-!
## The single-internal-floor crux is *solvable* for every sub-2 multiplier — the cubic obstruction is NOT here

An ON-LINE literature finding (`archive/findings/…cubic-selfref-literature.md`) proposed a "Tier-1"
cubic impossibility: that for `α = 2^{1/3}` reading base 2, **no** constant offset `c` makes the
single-internal-floor crux `0 ≤ {x} − α·{x/2} + c·α < 1` hold for all `x` (expecting the two-witness
method of `selfref_crux_fails_of_three_le` to scale up).

**That expectation is FALSE.**  The two-witness method does *not* scale to this object, because here
the *division stays at base 2* while only the multiplier changes — unlike `selfref_crux_fails_of_three_le`,
where both the division (`/g`) and the multiplier (`√g`) grow together.  In fact `c = ½` works for
**every** multiplier `0 ≤ β < 2` (and fails exactly at `β = 2`).  The reason is a clean width-1 identity:
with `t := {x/2}` one has `{x} = 2t − ⌊2t⌋`, so

* for `t < ½`:  `{x} − β t + β/2 = t(2−β) + β/2 ∈ [β/2, 1)`;
* for `t ≥ ½`:  `{x} − β t + β/2 = t(2−β) − 1 + β/2 ∈ [0, 1−β/2)`.

Both half-open ranges sit inside `[0,1)` precisely when `0 ≤ β < 2`.  (HOSTCHECK: 2M random samples at
`β = 2^{1/3}` give zero violations; `β = 2` gives ~50%.)

**Consequence for the cubic story.**  The genuine cubic obstruction is therefore *not* at the
single-floor level at all — it lives in the **3-step offset schedule** (two internal floors whose
rounding errors must cancel simultaneously; the `j ≈ 64` numeric breakdown of `cubic_recover.py`).
`selfref_crux_solvable_iff` (multiplier *and* division both `= g`) is the self-referential statement
that genuinely fails for `g ≥ 3`; the divide-by-2 single floor below is a *different* object that
survives, and conflating the two was the finding doc's error.  This corrects the record and sharpens
where the cubic wall actually is.
-/

/-- **Single-internal-floor, divide-by-2 crux is solvable for every `0 ≤ β < 2`, with `c = ½`.**
For any multiplier `β ∈ [0,2)` and all `x`, `0 ≤ {x} − β·{x/2} + β/2 < 1`.  In particular the
`α = 2^{1/3}` "cubic single floor" *is* solvable (`onefloor_div2_crux_cbrt2`) — the proposed Tier-1
cubic impossibility is false; the real cubic obstruction is in the multi-floor schedule, not here. -/
theorem onefloor_div2_crux_solvable (β : ℝ) (hβ0 : 0 ≤ β) (hβ2 : β < 2) (x : ℝ) :
    0 ≤ Int.fract x - β * Int.fract (x / 2) + β / 2 ∧
      Int.fract x - β * Int.fract (x / 2) + β / 2 < 1 := by
  set t := Int.fract (x / 2) with ht
  have ht0 : 0 ≤ t := Int.fract_nonneg _
  have ht1 : t < 1 := Int.fract_lt_one _
  -- `{x} = {2t}` since `x = 2t + 2⌊x/2⌋` and `2⌊x/2⌋` is an integer
  have hxt : Int.fract x = Int.fract (2 * t) := by
    have hsplit : x = 2 * t + ((2 * ⌊x / 2⌋ : ℤ) : ℝ) := by
      have h := Int.floor_add_fract (x / 2)   -- ↑⌊x/2⌋ + {x/2} = x/2
      rw [← ht] at h
      push_cast
      linarith
    conv_lhs => rw [hsplit]
    rw [Int.fract_add_intCast]
  rcases lt_or_ge t (1 / 2) with hlt | hge
  · -- `2t ∈ [0,1)`
    have h2t : Int.fract (2 * t) = 2 * t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hxt, h2t]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg ht0 (show (0:ℝ) ≤ 2 - β by linarith), hβ0]
    · nlinarith [mul_pos (show (0:ℝ) < 1 / 2 - t by linarith) (show (0:ℝ) < 2 - β by linarith)]
  · -- `2t ∈ [1,2)`, so `{2t} = 2t − 1`
    have h2t : Int.fract (2 * t) = 2 * t - 1 := by
      have h1 : Int.fract (2 * t - ((1 : ℤ) : ℝ)) = Int.fract (2 * t) := Int.fract_sub_intCast (2 * t) 1
      rw [← h1, Int.fract_eq_self.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩]
      push_cast; ring
    rw [hxt, h2t]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ t - 1 / 2 by linarith) (show (0:ℝ) ≤ 2 - β by linarith)]
    · nlinarith [mul_pos (show (0:ℝ) < 1 - t by linarith) (show (0:ℝ) < 2 - β by linarith)]

/-- **The cubic single-internal-floor crux IS solvable** (`β = 2^{1/3}`, `c = ½`): for all `x`,
`0 ≤ {x} − 2^{1/3}·{x/2} + 2^{1/3}/2 < 1`.  Directly refutes the literature finding's proposed
"Tier-1" cubic impossibility — the obstruction is not at the single-floor level. -/
theorem onefloor_div2_crux_cbrt2 (x : ℝ) :
    0 ≤ Int.fract x - (2 : ℝ) ^ ((1 : ℝ) / 3) * Int.fract (x / 2) + (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 ∧
      Int.fract x - (2 : ℝ) ^ ((1 : ℝ) / 3) * Int.fract (x / 2) + (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 < 1 := by
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  have hlt : (2 : ℝ) ^ ((1 : ℝ) / 3) < 2 := by
    have h : (2 : ℝ) ^ ((1 : ℝ) / 3) < (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) / 3 < 1)
    rwa [Real.rpow_one] at h
  exact onefloor_div2_crux_solvable _ hnn hlt x

/-- **Sharp characterization of the single-floor divide-by-2 crux.**  For `0 ≤ β`, there exists an
offset `c` making `0 ≤ {x} − β·{x/2} + c·β < 1` hold for **all** `x` **iff `β < 2`**.  The forward
direction is `onefloor_div2_crux_solvable` (`c = ½`); the reverse needs only the two integer witnesses
`x = 0` (forces `c·β < 1`) and `x = 1` (forces `c·β ≥ β/2`), which together give `β/2 < 1`, i.e.
`β < 2` — no limit argument.  So `β = 2` is the exact breakdown point (and `β = √2`, `2^{1/3}` are both
comfortably inside the solvable régime; crux-solvability alone does *not* single out the base, unlike
the genuinely self-referential `selfref_crux_solvable_iff`). -/
theorem onefloor_div2_crux_solvable_iff (β : ℝ) (hβ0 : 0 ≤ β) :
    (∃ c : ℝ, ∀ x : ℝ, 0 ≤ Int.fract x - β * Int.fract (x / 2) + c * β ∧
        Int.fract x - β * Int.fract (x / 2) + c * β < 1) ↔ β < 2 := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hge
    push Not at hge   -- `2 ≤ β`
    have hf1 : Int.fract (1 : ℝ) = 0 := by
      rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) by norm_num, Int.fract_intCast]
    have hf12 : Int.fract ((1 : ℝ) / 2) = 1 / 2 := Int.fract_eq_self.mpr (by constructor <;> norm_num)
    have hf02 : Int.fract ((0 : ℝ) / 2) = 0 := by rw [show (0 : ℝ) / 2 = 0 by ring, Int.fract_zero]
    have h0 := hc 0
    have h1 := hc 1
    rw [Int.fract_zero, hf02] at h0
    rw [hf1, hf12] at h1
    nlinarith [h0.2, h1.1, hge]
  · intro hβ2
    exact ⟨1 / 2, fun x => by
      have h := onefloor_div2_crux_solvable β hβ0 hβ2 x
      exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩

/-- **The offset `c = ½` is unique** for the single-floor divide-by-2 crux at any multiplier
`β ∈ (0,2)`.  If `0 ≤ {x} − β·{x/2} + c·β < 1` holds for all `x`, then `c = ½`.  Lower bound `c ≥ ½`
from `x = 1`; upper bound `c ≤ ½` from the family `x = 1 − t`, `t ↓ 0`.  So across the whole solvable
régime the offset is rigid — exactly `½`, never the multiplier-dependent value one might expect; the
freedom is entirely in `β`, not in `c`. -/
theorem onefloor_div2_offset_unique (β : ℝ) (hβ0 : 0 < β) (hβ2 : β < 2) (c : ℝ)
    (hc : ∀ x : ℝ, 0 ≤ Int.fract x - β * Int.fract (x / 2) + c * β ∧
        Int.fract x - β * Int.fract (x / 2) + c * β < 1) :
    c = 1 / 2 := by
  -- lower bound : x = 1
  have hlo : 1 / 2 ≤ c := by
    have h1 := hc 1
    have hf1 : Int.fract (1 : ℝ) = 0 := by
      rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) by norm_num, Int.fract_intCast]
    have hf2 : Int.fract ((1 : ℝ) / 2) = 1 / 2 := Int.fract_eq_self.mpr (by constructor <;> norm_num)
    rw [hf1, hf2] at h1
    nlinarith [h1.1, hβ0]
  -- upper bound : x = 1 − t, t ↓ 0
  have hhi : c ≤ 1 / 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    set K : ℝ := (1 - β / 2) / β with hK
    have hKpos : 0 < K := div_pos (by linarith) hβ0
    set t : ℝ := min (ε / K) (1 / 2) with ht
    have htpos : 0 < t := lt_min (div_pos hε hKpos) (by norm_num)
    have htle : t ≤ ε / K := min_le_left _ _
    have ht12 : t ≤ 1 / 2 := min_le_right _ _
    have hx := hc (1 - t)
    have hf1 : Int.fract (1 - t) = 1 - t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hf2 : Int.fract ((1 - t) / 2) = (1 - t) / 2 :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf1, hf2] at hx
    have hcs : c * β < β / 2 + t * (1 - β / 2) := by nlinarith [hx.2]
    have htK : t * (1 - β / 2) ≤ ε * β := by
      have h1 : t * (1 - β / 2) ≤ (ε / K) * (1 - β / 2) :=
        mul_le_mul_of_nonneg_right htle (by linarith)
      have hne : (1 : ℝ) - β / 2 ≠ 0 := by linarith
      have h2 : (ε / K) * (1 - β / 2) = ε * β := by
        rw [hK, div_div_eq_mul_div, div_mul_cancel₀ _ hne]
      linarith [h1, h2.le, h2.ge]
    nlinarith [hcs, htK, hβ0]
  linarith

end LeanGallery.NumberTheory.Erdos482.General
