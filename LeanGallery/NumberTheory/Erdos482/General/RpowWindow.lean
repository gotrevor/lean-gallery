/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# General degree-`d` partial-defect window width `> 2`

**Context (the general-`d` self-referential frontier).**  In the cubic/quartic impossibilities the
combined internal-floor defect `g = α^{d-1}f₁ + α^{d-2}f₂ + … + α f_{d-1}` (with `α = 2^{1/d}`,
`fᵢ ∈ [0,1)`) ranges over `[0, S_d)` with `S_d = α + α² + … + α^{d-1}`.  A base-2 digit forces
`g` into a window of width `2`; the impossibility is driven by `S_d > 2`, so a dense orbit of
`(f₁,…,f_{d-1})` must leave the window.  (`cubic_combined_defect_range_wide` is the `d = 3` instance.)

**This file proves the width brick uniformly for every `d ≥ 3`** (`rrt_window_gt_two`).  The clean
pivot is the closed form: since `α^d = 2`, the geometric sum gives `S_d = 1/(α-1) − 1 = (2-α)/(α-1)`,
and `S_d > 2 ⟺ α < 4/3 ⟺ 2 < (4/3)^d`, which holds for all `d ≥ 3` because `(4/3)³ = 64/27 > 2` and
`(4/3)^d` is increasing.  (For `d = 2`, `α = √2 ≈ 1.41 > 4/3`, `S_2 = √2 < 2` — consistent with the
original Graham–Pollak `√2` recurrence being solvable: the obstruction begins exactly at `d = 3`.)

Everything here depends only on the trust base `[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanGallery.NumberTheory.Erdos482.General

open Finset

/-- `α = 2^{1/d}` is positive. -/
theorem rrt_pos (d : ℕ) : 0 < (2 : ℝ) ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos (by norm_num) _

/-- `(2^{1/d})ᵈ = 2` for `d ≥ 1` — the `hα` hypothesis the general `GeneralDefect` engine needs to
instantiate at the concrete base `α = 2^{1/d}`. -/
theorem rrt_pow_self (d : ℕ) (hd : 1 ≤ d) : ((2 : ℝ) ^ ((1 : ℝ) / d)) ^ d = 2 := by
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / d)) d,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hdne, Real.rpow_one]

/-- **`g^{1/d} > 0`** for `g > 0` — base-`g` analogue of `rrt_pos`. -/
theorem rpow_inv_pos (g : ℝ) (hg : 0 < g) (d : ℕ) : 0 < (g : ℝ) ^ ((1 : ℝ) / d) :=
  Real.rpow_pos_of_pos hg _

/-- **`(g^{1/d})ᵈ = g`** for `g ≥ 0`, `d ≥ 1` — the `α^d = g` provider for the base-`g` chain
(`dStep_defect_identity_base` etc.).  Base-`g` analogue of `rrt_pow_self`. -/
theorem rpow_inv_pow_self (g : ℝ) (hg : 0 ≤ g) (d : ℕ) (hd : 1 ≤ d) :
    ((g : ℝ) ^ ((1 : ℝ) / d)) ^ d = g := by
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast ((g : ℝ) ^ ((1 : ℝ) / d)) d, ← Real.rpow_mul hg,
    one_div, inv_mul_cancel₀ hdne, Real.rpow_one]

/-- **`2^{1/d} < 4/3` for `d ≥ 3`.**  Equivalent to `2 < (4/3)^d`, which holds because `(4/3)³ = 64/27
> 2` and `n ↦ (4/3)ⁿ` is increasing.  This is the analytic pivot for the width bound: the partial
defect window has width `> 2` precisely when `α < 4/3`. -/
theorem rrt_lt_four_thirds (d : ℕ) (hd : 3 ≤ d) : (2 : ℝ) ^ ((1 : ℝ) / d) < 4 / 3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hdinv : (0 : ℝ) < (1 : ℝ) / d := div_pos one_pos hd0
  -- `2 < (4/3)^d`.
  have hpow : (2 : ℝ) < (4 / 3) ^ d := by
    have h3 : ((4 : ℝ) / 3) ^ 3 ≤ (4 / 3) ^ d := pow_le_pow_right₀ (by norm_num) hd
    have h64 : ((4 : ℝ) / 3) ^ 3 = 64 / 27 := by norm_num
    linarith [h3, h64]
  -- raise to the `1/d` power (strictly increasing on positives).
  have hlt := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 2) hpow hdinv
  have hrhs : ((4 / 3 : ℝ) ^ d) ^ ((1 : ℝ) / d) = 4 / 3 := by
    rw [← Real.rpow_natCast (4 / 3 : ℝ) d, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
      mul_one_div, div_self hdne, Real.rpow_one]
  rwa [hrhs] at hlt

/-- **Abstract geometric window-width bound (any base `g`).**  If `α > 1`, `αᵈ = g`, and the escape
condition `α < 2g/(g+1)` holds, then the partial-defect window width `∑_{1≤j<d} αʲ` exceeds the base
`g`.  The base-`g` brick: a base-`g` digit confines the defect to a window of width `g`, but the orbit's
defect ranges over `[0, ∑_{1≤j<d} αʲ)`, so this width bound drives the impossibility.  Proof: the
geometric sum collapses to `(g − α)/(α−1)`, and `(g − α)/(α−1) > g ⟺ α(g+1) < 2g ⟺ α < 2g/(g+1)`.
Specializes to `rrt_window_gt_two` (`g = 2`, bound `α < 4/3`). -/
theorem geom_window_gt_base (α : ℝ) (d : ℕ) (g : ℝ) (hα1 : 1 < α) (hd : 1 ≤ d)
    (hαd : α ^ d = g) (hbound : α < 2 * g / (g + 1)) (hg : 0 < g) :
    g < ∑ j ∈ Finset.Ico 1 d, α ^ j := by
  have hpos : 0 < α - 1 := by linarith
  have hg1 : 0 < g + 1 := by linarith
  have hexp : α * (g + 1) < 2 * g := (lt_div_iff₀ hg1).mp hbound
  rw [geom_sum_Ico (by linarith : α ≠ 1) hd, hαd, pow_one, lt_div_iff₀ hpos]
  nlinarith [hexp]

/-- **The partial-defect window width exceeds `2` for every `d ≥ 3`** (`α = 2^{1/d}`):
`2 < α + α² + … + α^{d-1}`.  The general-`d` analogue of `cubic_combined_defect_range_wide`.  The base-2
instance of `geom_window_gt_base` (`g = 2`, escape bound `α < 4/3 = 2·2/(2+1)`, `rrt_lt_four_thirds`). -/
theorem rrt_window_gt_two (d : ℕ) (hd : 3 ≤ d) :
    (2 : ℝ) < ∑ j ∈ Finset.Ico 1 d, ((2 : ℝ) ^ ((1 : ℝ) / d)) ^ j := by
  set α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / d) with hα
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hαpos : 0 < α := Real.rpow_pos_of_pos (by norm_num) _
  have hαd : α ^ d = 2 := by
    rw [hα, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / d)) d,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hdne, Real.rpow_one]
  have hα1 : 1 < α := by
    by_contra hc
    have : α ^ d ≤ 1 ^ d := pow_le_pow_left₀ hαpos.le (not_lt.mp hc) d
    rw [hαd, one_pow] at this; linarith
  exact geom_window_gt_base α d 2 hα1 (by omega) hαd
    (by rw [show (2 : ℝ) * 2 / (2 + 1) = 4 / 3 by norm_num]; exact rrt_lt_four_thirds d hd) (by norm_num)

/-- **A width-2 window cannot cover a width-`>2` interval.**  For any center `C` and any `W > 2`, some
`t ∈ [0, W)` lies outside the half-open window `(C-2, C]`.  This is the abstract geometric escape the
dense partial-defect orbit exploits: the orbit's value ranges over `[0, S_d)` with `S_d > 2`
(`rrt_window_gt_two`), but a base-2 digit pins it to `(C-2, C]` (`dStep_partial_mem_window`), so some
orbit point must produce a non-base-2 digit. -/
theorem window_not_cover (C W : ℝ) (hW : 2 < W) :
    ∃ t, t ∈ Set.Ico (0 : ℝ) W ∧ t ∉ Set.Ioc (C - 2) C := by
  by_cases h0 : (0 : ℝ) ∈ Set.Ioc (C - 2) C
  · rw [Set.mem_Ioc] at h0
    refine ⟨(C + W) / 2, ?_, ?_⟩
    · rw [Set.mem_Ico]; constructor <;> linarith [h0.1, h0.2]
    · rw [Set.mem_Ioc]; rintro ⟨_, ht⟩; linarith [h0.1]
  · exact ⟨0, by rw [Set.mem_Ico]; exact ⟨le_rfl, by linarith⟩, h0⟩

/-- **A positive-coefficient sum realizes every value in `[0, S)`.**  If `cₖ > 0` for `k < n` (`n ≥ 1`)
and `t ∈ [0, ∑ cₖ)`, there is a coefficient vector `f` with each `fₖ ∈ [0,1)` and `∑ cₖ fₖ = t`
(witness: the uniform `fₖ = t/S`).  Applied with `cₖ = α^{d-1-k}`, this says the partial-defect map
`(fₖ) ↦ ∑ α^{d-1-k} fₖ` surjects onto `[0, S_d)`; combined with `window_not_cover` (and `S_d > 2`,
`rrt_window_gt_two`) it gives the abstract geometry crux: a reachable partial defect outside any width-2
digit window. -/
theorem sum_pos_coeff_realize (n : ℕ) (hn : 0 < n) (c : ℕ → ℝ)
    (hc : ∀ k ∈ Finset.range n, 0 < c k) (t : ℝ)
    (ht : t ∈ Set.Ico (0 : ℝ) (∑ k ∈ Finset.range n, c k)) :
    ∃ f : ℕ → ℝ, (∀ k ∈ Finset.range n, f k ∈ Set.Ico (0 : ℝ) 1)
      ∧ ∑ k ∈ Finset.range n, c k * f k = t := by
  set S := ∑ k ∈ Finset.range n, c k with hS
  have hSpos : 0 < S := Finset.sum_pos hc (Finset.nonempty_range_iff.mpr (by omega))
  rw [Set.mem_Ico] at ht
  refine ⟨fun _ => t / S, fun k _ => ?_, ?_⟩
  · rw [Set.mem_Ico]
    exact ⟨div_nonneg ht.1 hSpos.le, (div_lt_one hSpos).mpr ht.2⟩
  · rw [← Finset.sum_mul, ← hS, mul_comm, div_mul_cancel₀ t (ne_of_gt hSpos)]

/-- **The abstract geometry crux for general `d ≥ 3`.**  For `α = 2^{1/d}` and any schedule constant
`C`, there is a reachable fract-configuration `f` (each `fₖ ∈ [0,1)`) whose partial defect
`g = ∑_{k<d-1} α^{d-1-k} fₖ` lies *outside* the width-2 base-2-digit window `(C-2, C]`.  In other
words, no fixed `C` makes *every* reachable partial defect a valid base-2 digit — the algebraic core of
the general-`d` impossibility (the remaining work is purely showing the orbit *reaches* such a `g`,
i.e. `Tᵈ` density).  Proof: the partial defect surjects onto `[0, S_d)` (`sum_pos_coeff_realize`) with
`S_d > 2` (`rrt_window_gt_two`, after an index reflection), and a width-2 window can't cover it
(`window_not_cover`). -/
theorem exists_partial_defect_outside_window (d : ℕ) (hd : 3 ≤ d) (C : ℝ) :
    ∃ f : ℕ → ℝ, (∀ k ∈ Finset.range (d - 1), f k ∈ Set.Ico (0 : ℝ) 1)
      ∧ (∑ k ∈ Finset.range (d - 1), ((2 : ℝ) ^ ((1 : ℝ) / d)) ^ (d - 1 - k) * f k)
          ∉ Set.Ioc (C - 2) C := by
  set α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / d) with hα
  set e := d - 1 with he
  have hαpos : 0 < α := Real.rpow_pos_of_pos (by norm_num) _
  -- index reflection: `∑_{k<e} α^{e-k} = ∑_{1≤j<d} α^j > 2`.
  have hSsum : ∑ k ∈ Finset.range e, α ^ (e - k) = ∑ j ∈ Finset.Ico 1 d, α ^ j := by
    rw [Finset.sum_Ico_eq_sum_range, ← he, ← Finset.sum_range_reflect (fun k => α ^ (1 + k)) e]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    congr 1; omega
  have hSgt : 2 < ∑ k ∈ Finset.range e, α ^ (e - k) := by
    rw [hSsum]; exact rrt_window_gt_two d hd
  obtain ⟨t, htin, htout⟩ := window_not_cover C (∑ k ∈ Finset.range e, α ^ (e - k)) hSgt
  obtain ⟨f, hf, hsum⟩ := sum_pos_coeff_realize e (by omega) (fun k => α ^ (e - k))
    (fun k _ => pow_pos hαpos _) t htin
  exact ⟨f, hf, by rw [hsum]; exact htout⟩

/-- **A strict-interior scaling escapes the window.**  For `S > 2` and any `C`, there is `τ ∈ (0,1)`
with `τ·S ∉ (C-2, C]`.  (`τ·S` ranges over the open interval `(0, S)` of length `> 2`.)  This is the
form needed for the final general-`d` assembly: take the constant defect target `fₖ = τ`, so the
partial defect is `τ·S_d` with `S_d > 2` (`rrt_window_gt_two`), realized strictly inside `(0,1)` so the
torus coordinates are nonzero. -/
theorem exists_scale_outside_window (S C : ℝ) (hS : 2 < S) :
    ∃ τ, τ ∈ Set.Ioo (0 : ℝ) 1 ∧ τ * S ∉ Set.Ioc (C - 2) C := by
  have hSpos : (0 : ℝ) < S := by linarith
  by_cases hC : C ≤ 0
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [Set.mem_Ioc]; rintro ⟨_, h2⟩; nlinarith
  · have hC : 0 < C := not_le.mp hC
    by_cases hCS : C < S
    · refine ⟨(C / S + 1) / 2, ⟨?_, ?_⟩, ?_⟩
      · have : (0 : ℝ) < C / S := div_pos hC hSpos; linarith
      · have : C / S < 1 := (div_lt_one hSpos).mpr hCS; linarith
      · rw [Set.mem_Ioc]; rintro ⟨_, h2⟩
        have hτS : (C / S + 1) / 2 * S = (C + S) / 2 := by field_simp
        rw [hτS] at h2; linarith
    · have hCS : S ≤ C := not_lt.mp hCS
      refine ⟨min ((C - 2) / S) (1 / 2), ⟨?_, ?_⟩, ?_⟩
      · exact lt_min (div_pos (by linarith) hSpos) (by norm_num)
      · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      · rw [Set.mem_Ioc]; rintro ⟨h1, _⟩
        have hle : min ((C - 2) / S) (1 / 2) * S ≤ (C - 2) / S * S :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hSpos.le
        rw [div_mul_cancel₀ _ (ne_of_gt hSpos)] at hle
        linarith

/-- **Base-`b` strict window escape.**  For window width `b > 0` and `S > b`, any `C`, there is
`τ ∈ (0,1)` with `τ·S` strictly outside the width-`b` window `(C-b, C]`.  Base-`b` analogue of
`exists_scale_outside_window_strict` (the `b = 2` case); used in the base-`g` general-degree assembly
with `S = S_d > g = b` (`geom_window_gt_base`). -/
theorem exists_scale_outside_window_strict_base (S C b : ℝ) (hb : 0 < b) (hS : b < S) :
    ∃ τ, τ ∈ Set.Ioo (0 : ℝ) 1 ∧ (τ * S < C - b ∨ C < τ * S) := by
  have hSpos : (0 : ℝ) < S := by linarith
  have hSne : S ≠ 0 := ne_of_gt hSpos
  by_cases hC : C ≤ 0
  · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, Or.inr (by linarith)⟩
  · have hC : 0 < C := not_le.mp hC
    by_cases hCS : C < S
    · refine ⟨(C / S + 1) / 2, ⟨?_, ?_⟩, Or.inr ?_⟩
      · have : (0 : ℝ) < C / S := div_pos hC hSpos; linarith
      · have : C / S < 1 := (div_lt_one hSpos).mpr hCS; linarith
      · have hτS : (C / S + 1) / 2 * S = (C + S) / 2 := by field_simp
        rw [hτS]; linarith
    · have hCS : S ≤ C := not_lt.mp hCS
      have hCb : 0 < C - b := by linarith
      set m : ℝ := min ((C - b) / S) 1 with hm
      have hmpos : 0 < m := lt_min (div_pos hCb hSpos) one_pos
      have hmle1 : m ≤ 1 := min_le_right _ _
      have hmS : m * S ≤ C - b := by
        have hml : m ≤ (C - b) / S := min_le_left _ _
        calc m * S ≤ (C - b) / S * S := by nlinarith
          _ = C - b := by field_simp
      refine ⟨m / 2, ⟨by linarith, by linarith⟩, Or.inl ?_⟩
      have hhalf : m / 2 * S = m * S / 2 := by ring
      rw [hhalf]; linarith

/-- **A strict-interior scaling escapes the window (strict form).**  For `S > 2` and any `C`, there is
`τ ∈ (0,1)` with `τ·S` *strictly* outside the half-open window `(C-2, C]`.  The `b = 2` instance of
`exists_scale_outside_window_strict_base`. -/
theorem exists_scale_outside_window_strict (S C : ℝ) (hS : 2 < S) :
    ∃ τ, τ ∈ Set.Ioo (0 : ℝ) 1 ∧ (τ * S < C - 2 ∨ C < τ * S) :=
  exists_scale_outside_window_strict_base S C 2 (by norm_num) hS

end LeanGallery.NumberTheory.Erdos482.General
