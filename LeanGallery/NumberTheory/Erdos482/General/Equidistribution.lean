/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries

/-!
# Equidistribution framework + Weyl's criterion (toward the a.e.-`W` cubic frontier)

`PENDING_WORK.md ★★` reduces the a.e.-`W` cubic impossibility to **a.e. equidistribution of the doubling
orbit `{2ⁿ s}`**, via Davenport–Erdős–LeVeque (DEL). The DEL chain produces
`(1/N_j)∑_{n<N_j} e(k·2ⁿ s) → 0` a.e. along the subsequence `N_j = j²`; two pieces then assemble the
equidistribution statement, and **neither is in mathlib**:

* **gap-filling** (`cesaro_fill_of_subseq_sq`): from convergence along the squares `N_j = j²` to
  convergence along *all* `N`, using only that the summands are bounded (`‖aₙ‖ ≤ 1`). Elementary, but
  the `Nat.sqrt`-squeeze bookkeeping is the work. Factored through `cesaro_fill_aux`, an abstract
  statement about any sequence of partial sums with `1`-Lipschitz increments.
* **Weyl's criterion** (to come): a sequence on `AddCircle 1` is equidistributed iff all its nonzero
  Weyl sums `(1/N)∑ fourier k` vanish — the `⟸` direction needs Stone–Weierstrass
  (`span_fourier_closure_eq_top`, present in mathlib).
-/

open Filter Finset MeasureTheory AddCircle
open scoped Topology

noncomputable section
namespace LeanGallery.NumberTheory.Erdos482.General

/-- **Integral of a Fourier monomial over the circle** (probability Haar measure):
`∫ fourier k = 1` if `k = 0` and `0` otherwise.  Immediate from `fourierCoeff_fourier`
(`fourierCoeff (fourier k) = Pi.single k 1`) and `fourierCoeff f 0 = ∫ f` (since `fourier 0 = 1`).
This identifies the limit in Weyl's criterion: for `k ≠ 0` the Cesàro average tends to `0 = ∫ fourier k`. -/
theorem integral_fourier_eq (k : ℤ) :
    (∫ y : AddCircle (1:ℝ), (fourier k) y ∂haarAddCircle) = if k = 0 then 1 else 0 := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  have e : fourierCoeff (T := (1:ℝ)) (fourier k) 0
      = ∫ y : AddCircle (1:ℝ), (fourier k) y ∂haarAddCircle := by
    simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]
  rw [← e, fourierCoeff_fourier, Pi.single_apply]
  by_cases hk : k = 0 <;> simp [hk, eq_comm]

/-- A sequence `x : ℕ → ℝ/ℤ` is **equidistributed** when, for every continuous test function
`f : C(ℝ/ℤ, ℂ)`, the Cesàro averages `(1/N)∑_{n<N} f(xₙ)` converge to the integral `∫ f` (w.r.t. the
probability Haar measure).  This is the "weak-* / continuous-function" form of uniform distribution;
it implies the orbit is dense (`isEquidistributed_dense`, to come) and is what Weyl's criterion
(`weyl_criterion`) produces from vanishing nonzero Weyl sums. -/
def IsEquidistributed (x : ℕ → AddCircle (1:ℝ)) : Prop :=
  ∀ f : C(AddCircle (1:ℝ), ℂ),
    Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, f (x n)) atTop
      (𝓝 (∫ y, f y ∂haarAddCircle))

/-- **Cesàro along squares ⇒ full Cesàro (abstract form).**  For any `S : ℕ → ℂ` whose increments are
`1`-Lipschitz in the counting sense (`‖S n − S m‖ ≤ n − m` for `m ≤ n`): if `(1/j²)·S(j²) → 0` along the
squares, then `(1/N)·S(N) → 0` along all `N`.  The `Nat.sqrt`-squeeze: write `j = ⌊√N⌋`, so
`j² ≤ N < (j+1)²`; then `‖S N‖ ≤ ‖S(j²)‖ + (N−j²) ≤ ‖S(j²)‖ + 2j`, giving
`‖S N‖/N ≤ ‖S(j²)‖/j² + 2/j → 0`. -/
theorem cesaro_fill_aux (S : ℕ → ℂ)
    (hinc : ∀ m n : ℕ, m ≤ n → ‖S n - S m‖ ≤ ((n - m : ℕ) : ℝ))
    (hsub : Tendsto (fun j : ℕ => ((j ^ 2 : ℕ) : ℂ)⁻¹ * S (j ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((N : ℕ) : ℂ)⁻¹ * S N) atTop (𝓝 0) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun b => ⟨b ^ 2, fun N hN => ?_⟩)
    calc b = Nat.sqrt (b ^ 2) := (Nat.sqrt_eq' b).symm
      _ ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN
  refine squeeze_zero_norm (a := fun N : ℕ =>
      ‖((Nat.sqrt N ^ 2 : ℕ) : ℂ)⁻¹ * S (Nat.sqrt N ^ 2)‖ + 2 / (Nat.sqrt N : ℝ))
    (fun N => ?_) ?_
  · -- per-`N` squeeze bound
    show ‖((N : ℕ) : ℂ)⁻¹ * S N‖
        ≤ ‖((Nat.sqrt N ^ 2 : ℕ) : ℂ)⁻¹ * S (Nat.sqrt N ^ 2)‖ + 2 / (Nat.sqrt N : ℝ)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · set j := Nat.sqrt N with hj
      have hjsq_le : j ^ 2 ≤ N := Nat.sqrt_le' N
      have hN_lt : N < (j + 1) ^ 2 := Nat.lt_succ_sqrt' N
      have hjpos : 0 < j := Nat.sqrt_pos.mpr hN
      have hNR : (0:ℝ) < N := by exact_mod_cast hN
      have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hjpos
      have hjsqR : (0:ℝ) < (j:ℝ) ^ 2 := by positivity
      have hjsq_leR : ((j:ℝ)) ^ 2 ≤ (N:ℝ) := by exact_mod_cast hjsq_le
      have hgap : (N - j ^ 2 : ℕ) ≤ 2 * j := by
        have hle : N ≤ (j + 1) ^ 2 - 1 := Nat.le_sub_one_of_lt hN_lt
        have hexp : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
        omega
      have hgapR : ((N - j ^ 2 : ℕ) : ℝ) ≤ 2 * (j:ℝ) := by exact_mod_cast hgap
      have key : ‖S N‖ ≤ ‖S (j ^ 2)‖ + 2 * (j:ℝ) := by
        have h1 : ‖S N - S (j ^ 2)‖ ≤ ((N - j ^ 2 : ℕ) : ℝ) := hinc (j ^ 2) N hjsq_le
        calc ‖S N‖ = ‖S (j ^ 2) + (S N - S (j ^ 2))‖ := by ring_nf
          _ ≤ ‖S (j ^ 2)‖ + ‖S N - S (j ^ 2)‖ := norm_add_le _ _
          _ ≤ ‖S (j ^ 2)‖ + 2 * (j:ℝ) := by linarith
      have e1 : ‖((j ^ 2 : ℕ) : ℂ)⁻¹ * S (j ^ 2)‖ = ‖S (j ^ 2)‖ / ((j:ℝ) ^ 2) := by
        rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
        congr 1
        push_cast; ring
      rw [norm_mul, norm_inv, Complex.norm_natCast, e1]
      have hNinv : (N:ℝ)⁻¹ ≤ ((j:ℝ) ^ 2)⁻¹ := inv_anti₀ hjsqR hjsq_leR
      calc (N:ℝ)⁻¹ * ‖S N‖
          ≤ ((j:ℝ) ^ 2)⁻¹ * (‖S (j ^ 2)‖ + 2 * (j:ℝ)) :=
            mul_le_mul hNinv key (norm_nonneg _) (by positivity)
        _ = ‖S (j ^ 2)‖ / ((j:ℝ) ^ 2) + 2 / (j:ℝ) := by
            have hjne : (j:ℝ) ≠ 0 := ne_of_gt hjR
            field_simp
  · -- the squeeze bound tends to `0`
    have h1 : Tendsto (fun N : ℕ => ‖((Nat.sqrt N ^ 2 : ℕ) : ℂ)⁻¹ * S (Nat.sqrt N ^ 2)‖)
        atTop (𝓝 0) := by
      have hnorm : Tendsto (fun j : ℕ => ‖((j ^ 2 : ℕ) : ℂ)⁻¹ * S (j ^ 2)‖) atTop (𝓝 0) := by
        simpa using hsub.norm
      exact hnorm.comp hsqrt
    have h2 : Tendsto (fun N : ℕ => 2 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun j : ℕ => (2:ℝ) / (j:ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 2
      exact hc.comp hsqrt
    simpa using h1.add h2

/-- **Gap-filling / Cesàro along squares ⇒ full Cesàro.**  If the partial sums `S N = ∑_{n<N} aₙ` of a
bounded sequence (`‖aₙ‖ ≤ 1`) satisfy `(1/j²)·S(j²) → 0` along the squares, then `(1/N)·S(N) → 0` along
*all* `N`.  This is the "fill the gaps between `N_j = j²` and `N_{j+1} = (j+1)²` via `|S_{N+1}−S_N| ≤ 1`"
step of the DEL assembly (`PENDING_WORK.md ★★` step (b)): along the squares the normalized Weyl sum is
`1/j²` (summable ⇒ `→ 0` a.e. by the DEL engine), and this lemma upgrades that to all `N`. -/
theorem cesaro_fill_of_subseq_sq (a : ℕ → ℂ) (hb : ∀ n, ‖a n‖ ≤ 1)
    (hsub : Tendsto (fun j : ℕ => ((j ^ 2 : ℕ) : ℂ)⁻¹ * ∑ n ∈ range (j ^ 2), a n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ range N, a n) atTop (𝓝 0) := by
  refine cesaro_fill_aux (fun N => ∑ n ∈ range N, a n) (fun m n hmn => ?_) hsub
  have hdiff : (∑ k ∈ range n, a k) - (∑ k ∈ range m, a k) = ∑ k ∈ Finset.Ico m n, a k :=
    (Finset.sum_Ico_eq_sub a hmn).symm
  rw [hdiff]
  calc ‖∑ k ∈ Finset.Ico m n, a k‖ ≤ ∑ k ∈ Finset.Ico m n, ‖a k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico m n, (1:ℝ) := Finset.sum_le_sum (fun k _ => hb k)
    _ = ((n - m : ℕ) : ℝ) := by simp

/-- **Fourier monomial on the doubling orbit = the explicit Weyl exponential.**
`fourier k (↑(2ⁿ·s)) = e^{2πi·(k·2ⁿ)·s}` on `ℝ/ℤ` (`T = 1`).  This bridges the abstract
`weyl_criterion` (whose input is `∑ fourier k (xₙ)` for `xₙ = ↑(2ⁿs)`) to the explicit doubling
exponential sum whose mean square is computed in `WeylDoubling` — the seam of path #2's step (b). -/
theorem fourier_doubling_eq (k : ℤ) (n : ℕ) (s : ℝ) :
    (fourier k) (((2:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))
      = Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **p-series finiteness for the DEL hypothesis**: `∑'_j ENNReal.ofReal((j²)⁻¹) ≠ ⊤`.  This is the
`∑_j ∫₀¹‖g_j‖² < ∞` input the DEL engine needs once the L² bridge turns
`doubling_weyl_L2_normalized` (`∫₀¹‖g_{j²}‖² = 1/j²`) into the `ℝ≥0∞` form. -/
theorem tsum_ofReal_inv_sq_ne_top :
    (∑' j : ℕ, ENNReal.ofReal (((j ^ 2 : ℕ) : ℝ)⁻¹)) ≠ ⊤ := by
  have hsummable : Summable (fun j : ℕ => ((j ^ 2 : ℕ) : ℝ)⁻¹) :=
    ((Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)).congr (fun j => by push_cast; ring)
  have h := ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℕ => ((j ^ 2 : ℕ) : ℝ)⁻¹)
    (fun j => by positivity) hsummable
  rw [← h]
  exact ENNReal.ofReal_ne_top

/-- **Cesàro averages are sup-norm bounded** (`N ≥ 1`): `‖(1/N)∑_{n<N} f(xₙ)‖ ≤ ‖f‖`.  The uniform
bound that lets the equidistribution property pass from the dense Fourier span to all continuous `f`.
Stated over any compact domain `X` so it serves both the 1-D and the torus (`MultidimWeyl`) criteria. -/
theorem norm_cesaro_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : ℕ → X) (f : C(X, ℂ)) {N : ℕ} (hN : 1 ≤ N) :
    ‖(N:ℂ)⁻¹ * ∑ n ∈ range N, f (x n)‖ ≤ ‖f‖ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ range N, f (x n)‖ ≤ (N:ℝ) * ‖f‖ := by
    calc ‖∑ n ∈ range N, f (x n)‖ ≤ ∑ n ∈ range N, ‖f (x n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, ‖f‖ := Finset.sum_le_sum (fun n _ => f.norm_coe_le_norm (x n))
      _ = (N:ℝ) * ‖f‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (N:ℝ)⁻¹ * ‖∑ n ∈ range N, f (x n)‖
      ≤ (N:ℝ)⁻¹ * ((N:ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖f‖ := by rw [inv_mul_cancel_left₀ (ne_of_gt hNR)]

/-- **Weyl's equidistribution criterion** (the direction needed for the cubic frontier).  If all
nonzero Weyl sums of `x` vanish in Cesàro mean — `(1/N)∑_{n<N} e(k·xₙ) → 0` for every `k ≠ 0` — then `x`
is equidistributed on `ℝ/ℤ`.

The proof: the property `avg(f) → ∫f` holds for every Fourier monomial (`k = 0` gives the constant `1`;
`k ≠ 0` is the hypothesis, with `∫ fourier k = 0` by `integral_fourier_eq`), extends to the Fourier span
by linearity (`Submodule.span_induction`), and then to *all* continuous `f` by uniform approximation —
the span is dense (`span_fourier_closure_eq_top`, Stone–Weierstrass) and the averages are uniformly
sup-norm bounded (`norm_cesaro_le`).  This is the only mathlib-absent analytic input of path #2's
final assembly. -/
theorem weyl_criterion (x : ℕ → AddCircle (1:ℝ))
    (h : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (fourier k) (x n)) atTop (𝓝 0)) :
    IsEquidistributed x := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  -- integrability of any continuous test function (compact domain, finite measure)
  have hInt : ∀ f : C(AddCircle (1:ℝ), ℂ), Integrable (fun y => f y) haarAddCircle := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Step 1: the property holds for every Fourier monomial.
  have hmono : ∀ k : ℤ, Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (fourier k) (x n)) atTop
      (𝓝 (∫ y : AddCircle (1:ℝ), (fourier k) y ∂haarAddCircle)) := by
    intro k
    rw [integral_fourier_eq]
    by_cases hk : k = 0
    · subst hk
      simp only [fourier_zero]
      refine Tendsto.congr' ?_ (show Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1) from tendsto_const_nhds)
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hNc]
    · rw [if_neg hk]; exact h k hk
  -- Step 2: the property holds on the Fourier span (linearity).
  have hspan : ∀ f ∈ Submodule.span ℂ (Set.range (fourier (T := (1:ℝ)))),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, f (x n)) atTop (𝓝 (∫ y, f y ∂haarAddCircle)) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem g hg => obtain ⟨k, rfl⟩ := hg; exact hmono k
    | zero =>
      simp only [ContinuousMap.zero_apply, Finset.sum_const_zero, mul_zero, integral_zero]
      exact tendsto_const_nhds
    | add g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      have hintadd : (∫ y, (g₁ + g₂) y ∂haarAddCircle)
          = (∫ y, g₁ y ∂haarAddCircle) + ∫ y, g₂ y ∂haarAddCircle := by
        simp only [ContinuousMap.add_apply]; exact integral_add (hInt g₁) (hInt g₂)
      have havg : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (g₁ + g₂) (x n))
          = fun N : ℕ => ((N:ℂ)⁻¹ * ∑ n ∈ range N, g₁ (x n))
              + ((N:ℂ)⁻¹ * ∑ n ∈ range N, g₂ (x n)) := by
        funext N; simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
      rw [hintadd, havg]; exact ih₁.add ih₂
    | smul c g hg ih =>
      have hintsmul : (∫ y, (c • g) y ∂haarAddCircle) = c * ∫ y, g y ∂haarAddCircle := by
        simp only [ContinuousMap.smul_apply]
        rw [integral_smul, smul_eq_mul]
      have havg : (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N, (c • g) (x n))
          = fun N : ℕ => c * ((N:ℂ)⁻¹ * ∑ n ∈ range N, g (x n)) := by
        funext N; simp only [ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]; ring_nf
      rw [hintsmul, havg]; exact ih.const_mul c
  -- Step 3: density extends the property to all continuous `f`.
  have hdense : Dense ((Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) : Set C(AddCircle (1:ℝ), ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  intro f
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hdense f) (ε / 3) (by positivity)
  have hfg_norm : ‖f - g‖ < ε / 3 := by rwa [dist_eq_norm] at hfg
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hspan g hg) (ε / 3) (by positivity)
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  -- bound (i): the averages of `f` and `g` differ by at most `‖f - g‖`
  have hi : dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k)) ((n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k)) ≤ ‖f - g‖ := by
    rw [dist_eq_norm]
    have hd : (n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k) - (n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k)
        = (n:ℂ)⁻¹ * ∑ k ∈ range n, (f - g) (x k) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]; simp only [ContinuousMap.sub_apply]
    rw [hd]; exact norm_cesaro_le x (f - g) hn1
  -- bound (iii): the integrals of `f` and `g` differ by at most `‖f - g‖`
  have hiii : dist (∫ y, g y ∂haarAddCircle) (∫ y, f y ∂haarAddCircle) ≤ ‖f - g‖ := by
    rw [dist_eq_norm]
    have hsub : (∫ y, g y ∂haarAddCircle) - ∫ y, f y ∂haarAddCircle = ∫ y, (g - f) y ∂haarAddCircle := by
      rw [← integral_sub (hInt g) (hInt f)]; simp only [ContinuousMap.sub_apply]
    rw [hsub]
    calc ‖∫ y, (g - f) y ∂haarAddCircle‖
        ≤ ‖g - f‖ * (haarAddCircle (Set.univ : Set (AddCircle (1:ℝ)))).toReal :=
          norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall (fun y => (g - f).norm_coe_le_norm y))
      _ = ‖f - g‖ := by rw [measure_univ, ENNReal.toReal_one, mul_one, norm_sub_rev]
  -- assemble the three bounds
  calc dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k)) (∫ y, f y ∂haarAddCircle)
      ≤ dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, f (x k)) ((n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k))
        + dist ((n:ℂ)⁻¹ * ∑ k ∈ range n, g (x k)) (∫ y, g y ∂haarAddCircle)
        + dist (∫ y, g y ∂haarAddCircle) (∫ y, f y ∂haarAddCircle) := dist_triangle4 _ _ _ _
    _ < ε := by have := hN₀ n hn₀; linarith [hi, hiii, hfg_norm]

end LeanGallery.NumberTheory.Erdos482.General
