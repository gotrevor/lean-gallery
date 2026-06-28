/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.Cor11
import LeanGallery.NumberTheory.Erdos482.Main

/-!
# Two independent proofs of the √2 digit theorem meet on the *same* sequence

This file connects the two tracks of the repo at their common point, `√2`:

* the **original** Graham–Pollak track (`LeanGallery.NumberTheory.Erdos482.u`, `LeanGallery.NumberTheory.Erdos482.graham_pollak`), an elementary
  induction on the bespoke sequence `u 0 = 1`, `u(n+1) = ⌊√2·(u n + ½)⌋`; and
* the **general** St05 track (`gv`, `thm12_caseI_digits`, `cor11_binary_sqrt2_caseI`), where digit
  extraction for *any* `1 ≤ t < g` is proved once, by a closed-form joint induction, and √2 is one
  instantiation (Case I, `j = 1`).

The bridge is `gv_sqrt2_eq_u`: the general binary recurrence `gv √2 √2 ½`, which is the `j = 1`
slice of Cor 1.1's Case-I √2-family, is *literally the original sequence* `u` (cast to `ℤ`).
Consequently the general digit theorem, specialized, becomes a statement about the genuine
Graham–Pollak sequence — a second, independent proof of "√2's binary digits fall out of `u`",
sharing none of `graham_pollak`'s proof tree.

**The two proofs read complementary digit streams of the *same* `u`** (verified numerically):
`graham_pollak` reads the **odd-index** differences `u(2n+1) − 2u(2n−1) = 0,1,1,0,1,0,…` — the
*fractional* binary digits of `√2`; the general route here reads the **even-index** differences
`u(2n) − 2u(2n−2) = 1,0,1,1,0,1,…` — the *full* expansion `√2 = 1.0110101…₂`, leading `1` included.
That both parities are digit streams is special to the symmetric `a = b = √2` case.

Axiom-clean (inherits `cor11_binary_sqrt2_caseI` + an elementary `Nat.floor`/`Int.floor` induction).
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Real

/-- **The general recurrence `gv √2 √2 ½` is the original Graham–Pollak sequence `u`.**  For `a = b = √2`
and `ε = ½`, both branches of `gv`'s step collapse to `⌊√2·(· + ½)⌋`, the defining step of `u`; the only
difference is `u`'s `Nat.floor` vs `gv`'s `Int.floor`, reconciled since the argument is nonnegative.
Stated with `a, b, ε` as hypotheses so it applies directly to Cor 1.1's `j = 1` coefficients
(`a = 2(1−1)+√2`, `b = 2/(2(1−1)+√2)`), both of which equal `√2`. -/
theorem gv_sqrt2_eq_u (a b ε : ℝ) (ha : a = Real.sqrt 2) (hb : b = Real.sqrt 2) (hε : ε = 1 / 2)
    (m : ℕ) : gv a b ε m = (LeanGallery.NumberTheory.Erdos482.u m : ℤ) := by
  subst ha hb hε
  induction m with
  | zero => rfl
  | succ k ih =>
    have hnn : (0 : ℝ) ≤ Real.sqrt 2 * ((LeanGallery.NumberTheory.Erdos482.u k : ℝ) + 1 / 2) := by positivity
    rw [gv_succ]
    -- both parities use √2·(gv k + ½); fold the `if`
    have hfold : (if Even k then ⌊Real.sqrt 2 * ((gv (Real.sqrt 2) (Real.sqrt 2) (1 / 2) k : ℝ) + 1 / 2)⌋
        else ⌊Real.sqrt 2 * ((gv (Real.sqrt 2) (Real.sqrt 2) (1 / 2) k : ℝ) + 1 / 2)⌋)
        = ⌊Real.sqrt 2 * ((gv (Real.sqrt 2) (Real.sqrt 2) (1 / 2) k : ℝ) + 1 / 2)⌋ := by
      split <;> rfl
    rw [hfold, ih]
    -- u (k+1) = ⌊√2·(u k + ½)⌋₊ ; cast Nat.floor to Int.floor (argument ≥ 0)
    rw [show LeanGallery.NumberTheory.Erdos482.u (k + 1) = ⌊Real.sqrt 2 * ((LeanGallery.NumberTheory.Erdos482.u k : ℝ) + 1 / 2)⌋₊ from rfl,
      Int.natCast_floor_eq_floor hnn, Int.cast_natCast]

/-- **St05 → Graham–Pollak: digits of `√2` from the *original* sequence `u`, via the general theorem.**
Specializing Cor 1.1 (Case I, `j = 1`) through `gv_sqrt2_eq_u`: the even-index Graham–Pollak
difference of the genuine sequence `u` reads off the base-2 digits of `√2`,
`u(2n) − 2·u(2n−2) = Real.digits (√2·2^{n−1}/2) 2 0`.  This shares no proof machinery with
`LeanGallery.NumberTheory.Erdos482.graham_pollak` (which proves the companion odd-index identity by a direct induction) —
two independent routes to "√2's binary expansion is encoded in `u`". -/
theorem gp_sqrt2_digits_via_general (n : ℕ) (hn : 1 ≤ n) :
    (LeanGallery.NumberTheory.Erdos482.u (2 * n) : ℤ) - 2 * (LeanGallery.NumberTheory.Erdos482.u (2 * n - 2) : ℤ)
      = ((Real.digits (Real.sqrt 2 * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := le_of_lt ((Real.lt_sqrt (by norm_num)).mpr (by norm_num))
  -- the j = 1 coefficients both reduce to √2 (note `cor11` carries `(↑(1:ℕ) : ℝ)`)
  have ha : 2 * (((1 : ℕ) : ℝ) - 1) + Real.sqrt 2 = Real.sqrt 2 := by push_cast; ring
  have hb : 2 / (2 * (((1 : ℕ) : ℝ) - 1) + Real.sqrt 2) = Real.sqrt 2 := by
    rw [ha, div_eq_iff (by positivity)]; nlinarith [h2]
  rw [← gv_sqrt2_eq_u _ _ _ ha hb rfl (2 * n),
      ← gv_sqrt2_eq_u _ _ _ ha hb rfl (2 * n - 2)]
  exact cor11_binary_sqrt2_caseI 1 (le_refl 1) n hn

/-- **Literal-digit form of the general route.**  For `n ≥ 2`, the even-index difference of `u` is
exactly the `(n−2)`-th mathlib base-2 digit of `√2`: `u(2n) − 2u(2n−2) = Real.digits √2 2 (n−2)`. -/
theorem gp_sqrt2_digits_via_general_literal (n : ℕ) (hn : 2 ≤ n) :
    (LeanGallery.NumberTheory.Erdos482.u (2 * n) : ℤ) - 2 * (LeanGallery.NumberTheory.Erdos482.u (2 * n - 2) : ℤ)
      = ((Real.digits (Real.sqrt 2) 2 (n - 2) : ℕ) : ℤ) := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  rw [gp_sqrt2_digits_via_general n (by omega)]
  exact digit_recon 2 (Real.sqrt 2) (Real.sqrt_nonneg 2) n hn

end LeanGallery.NumberTheory.Erdos482.General
