/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.General.WeylDoubling

/-!
# Base-`g` Weyl bricks for a.e. equidistribution of the orbit `{gⁿs}`

The base-`g` (`g ≥ 2`) analogue of `WeylDoubling`.  The a.e.-`W` general-`d` impossibility generalizes
from base 2 (doubling, window width 2, digits `{0,1}`) to base `g` (multiplier `gⁿ`, window width `g`,
digits `{0,…,g-1}`); the analytic engine is **base-agnostic** — the only base-specific input is the
injectivity `n ↦ gⁿ`, which here replaces `WeylDoubling.two_pow_inj`.

* `g_pow_inj`: `(g:ℤ)ⁿ = gᵐ ↔ n = m` for `g ≥ 2` (`Nat.pow_right_injective`).
* `baseG_weyl_L2_mean`: the Weyl L² mean `∫₀¹ (∑_{n,m<N} e(k(gⁿ−gᵐ)s)) ds = N` (`k ≠ 0`).
* `baseG_weyl_L2_normalized`: `∫₀¹ ‖(1/N)∑_{n<N} e(k·gⁿ·s)‖² ds = 1/N` — exactly `∫‖g_N‖²` for the DEL
  engine, summable along `N=j²`.

The abstract `weyl_double_sum_integral` + `char_int` (orthogonality) are reused verbatim from
`WeylDoubling`; only the diagonal-count lemma changes base.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- `(g:ℤ)ⁿ = gᵐ ↔ n = m` for `g ≥ 2`: the base-`g` powers are distinct, so `k·(gⁿ−gᵐ) = 0` (`k ≠ 0`)
exactly on the diagonal `n = m` — the terms surviving in the Weyl mean square.  Replaces `two_pow_inj`. -/
theorem g_pow_inj {g : ℕ} (hg : 2 ≤ g) (n m : ℕ) : ((g:ℤ)^n = (g:ℤ)^m) ↔ n = m := by
  constructor
  · intro h
    have : (g:ℕ)^n = g^m := by exact_mod_cast h
    exact Nat.pow_right_injective hg this
  · rintro rfl; rfl

/-- Each base-`g` exponential `e(k·gⁿ·s)` has unit modulus. -/
theorem norm_baseG_exp (g : ℕ) (k : ℤ) (n : ℕ) (s : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * s)‖ = 1 := by
  rw [show (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ) ^ n : ℤ) : ℂ) * (s:ℂ))
        = ((2 * Real.pi * (k * (g:ℤ) ^ n) * s : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Weyl L² mean of the base-`g` exponential sum.**  For `k ≠ 0`,
`∫₀¹ (∑_{n,m<N} e(k(gⁿ−gᵐ)s)) ds = N` — only the `N` diagonal terms `n=m` survive (`g_pow_inj`). -/
theorem baseG_weyl_L2_mean {g : ℕ} (hg : 2 ≤ g) (k : ℤ) (hk : k ≠ 0) (N : ℕ) :
    (∫ s in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * ((g:ℤ)^n - (g:ℤ)^m) : ℤ):ℂ) * s)) = (N:ℂ) := by
  rw [weyl_double_sum_integral (fun n m => k * ((g:ℤ)^n - (g:ℤ)^m)) N]
  have cond : ∀ n m : ℕ, (k * ((g:ℤ)^n - (g:ℤ)^m) = 0) ↔ (m = n) := by
    intro n m; rw [mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hk
      · exact ((g_pow_inj hg n m).mp h).symm
    · rintro rfl; right; rfl
  calc ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if k * ((g:ℤ)^n - (g:ℤ)^m) = 0 then (1:ℂ) else 0)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if m = n then (1:ℂ) else 0) :=
        Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => if_congr (cond n m) rfl rfl))
    _ = ∑ n ∈ Finset.range N, (1:ℂ) :=
        Finset.sum_congr rfl (fun n hn => by
          rw [Finset.sum_ite_eq' (Finset.range N) n (fun _ => (1:ℂ)), if_pos hn])
    _ = (N:ℂ) := by simp [Finset.sum_const, Finset.card_range]

/-- One product term of `|∑ e(k·gⁿ·s)|²`: `e(k·gⁿ·s)·conj(e(k·gᵐ·s)) = e(k(gⁿ−gᵐ)s)`. -/
theorem baseG_term_id (g : ℕ) (k : ℤ) (n m : ℕ) (x : ℝ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * x)
      * (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^m : ℤ):ℂ) * x))
      = Complex.exp (2 * ↑Real.pi * Complex.I * ((k * ((g:ℤ)^n - (g:ℤ)^m) : ℤ):ℂ) * x) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  have hconj : (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^m : ℤ):ℂ) * ↑x)
      = -(2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^m : ℤ):ℂ) * ↑x) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]; ring
  rw [hconj]; push_cast; ring

/-- **Base-`g` Weyl mean square (norm form).**  `∫₀¹ ‖∑_{n<N} e(k·gⁿ·s)‖² ds = N` for `k ≠ 0`. -/
theorem baseG_weyl_L2_mean_norm {g : ℕ} (hg : 2 ≤ g) (k : ℤ) (hk : k ≠ 0) (N : ℕ) :
    (∫ s in (0:ℝ)..1, ‖∑ n ∈ Finset.range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * s)‖ ^ 2) = (N:ℝ) := by
  have ptwise : ∀ x : ℝ,
      ((‖∑ n ∈ Finset.range N, Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * x)‖ ^ 2 : ℝ):ℂ)
        = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            Complex.exp (2 * ↑Real.pi * Complex.I * ((k * ((g:ℤ)^n - (g:ℤ)^m) : ℤ):ℂ) * x) := by
    intro x
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => baseG_term_id g k n m x))
  have hcplx : ((∫ s in (0:ℝ)..1, ‖∑ n ∈ Finset.range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * s)‖ ^ 2 : ℝ):ℂ) = (N:ℂ) := by
    rw [← intervalIntegral.integral_ofReal,
      show (∫ x in (0:ℝ)..1, ((‖∑ n ∈ Finset.range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * x)‖ ^ 2 : ℝ):ℂ))
        = ∫ x in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            Complex.exp (2 * ↑Real.pi * Complex.I * ((k * ((g:ℤ)^n - (g:ℤ)^m) : ℤ):ℂ) * x)
        from intervalIntegral.integral_congr (fun x _ => ptwise x)]
    exact baseG_weyl_L2_mean hg k hk N
  exact_mod_cast hcplx

/-- **Normalized base-`g` Weyl mean square** — exactly `∫₀¹‖g_N‖²` for `g_N := (1/N)·∑_{n<N} e(k·gⁿ·)`:
`∫₀¹ ‖(N:ℂ)⁻¹·∑_{n<N} e(k·gⁿ·s)‖² ds = 1/N`.  Along `N_j = j²` this is `1/j²`, summable. -/
theorem baseG_weyl_L2_normalized {g : ℕ} (hg : 2 ≤ g) (k : ℤ) (hk : k ≠ 0) (N : ℕ) :
    (∫ s in (0:ℝ)..1, ‖(N:ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * s)‖ ^ 2)
      = (N:ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hpt : ∀ s : ℝ, ‖(N:ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * s)‖ ^ 2
        = ((N:ℝ)⁻¹)^2 * ‖∑ n ∈ Finset.range N,
            Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (g:ℤ)^n : ℤ):ℂ) * s)‖ ^ 2 := by
      intro s; rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, baseG_weyl_L2_mean_norm hg k hk N]
    have hNne : (N:ℝ) ≠ 0 := by positivity
    field_simp

end LeanGallery.NumberTheory.Erdos482.General
