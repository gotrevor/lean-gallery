/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.Statement

/-!
# Borwein's general Theorem 1 — `∑ 1/(qⁿ + c)` is irrational (GENERALIZATION, in progress)

The headline result of this repository, `erdos_1050_irrational : Irrational S` (`Statement.lean`),
is the `q = 2, c = −3` instance of a far more general theorem of Borwein:

> **Theorem 1** (P. B. Borwein, *On the irrationality of certain series*, Math. Proc. Camb. Phil.
> Soc. **112** (1992) 141–146). Let `q` be an integer with `|q| > 1` and `c` a non-zero rational
> with `c ≠ −qⁿ` for all `n`. Then `∑_{n≥1} 1/(qⁿ + c)` is irrational.

This file states that theorem faithfully in Lean (`borwein_thm1`) and **reduces it, provably and in
full generality, to a single q-harmonic irrationality core** — exactly the form Borwein himself reduces
to (his eq. (2) and the remark immediately after Lemma 1: "the irrationality of `∑ 1/(q^n+c)` is
equivalent to the irrationality of `∑ 1/(1 − c·qʰ)`"). The reduction here is the *elementary* affine
one: writing `C = −1/c`,
  `1/(qⁿ + c) = (1/c)·(1 − C·qⁿ)⁻¹`,
so `c·(∑ 1/(qⁿ+c)) = ∑ (1 − C·qⁿ)⁻¹`, and irrationality is invariant under the nonzero-rational
scaling by `c` (`irrational_ratCast_mul_iff`). Both steps are **unconditional** (`tsum_mul_left`,
`tsum_congr`) — no summability hypothesis is needed for the algebraic identity — so the reduction
holds verbatim for every integer `q` with `|q| > 1`, negative `q` included.

## Status of the core
The remaining content — that the reduced value `∑ (1 − C·qⁿ)⁻¹` is irrational — is Borwein's
Padé/contour engine (his Lemmas 1–5: residue identity, denominator integrality, numerator
integrality, super-exponential error bound, non-vanishing). It is stated here as the disclosed,
cited **`axiom qharmonic_irrational`**.

That axiom is **already discharged in this repo for `q = 2`**: `LeanGallery.NumberTheory.Erdos1050.irrational_zB` proves exactly
`Irrational (∑ (1 − (8/3)·2ʲ)⁻¹)`, axiom-clean, via the elementary route (`Residue.lean`,
`QLagrange.lean`, `Lemma3.lean`). Discharging `qharmonic_irrational` in general is the live target:
parametrise that engine in `(q, c)`. The `q = 2` discharge shows the wall is breachable; the general
case needs the residue/integrality lemmas re-derived parametrically (the numerator integrality `N_h`,
proved 2-adically for `q = 2`, is the genuine nub).

**This file does not touch `erdos_1050_irrational`, which remains axiom-clean** (`#print axioms`
shows only `propext, Classical.choice, Quot.sound`). `borwein_thm1` is a strictly more general
statement, proved modulo the one cited core axiom.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- **The general q-harmonic value converges.** For real `q` with `|q| ≥ 2` and `C ≠ 0`, the series
`∑ₙ (1 − C·q^{n+1})⁻¹` is summable. (So the reduced value in `borwein_approximants` /
`qharmonic_irrational` is the genuine convergent sum, not the junk default of a divergent `tsum`.)

Proof: eventually `|1 − C·q^{n+1}| ≥ |C|·|q|^{n+1} − 1 ≥ |C|·|q|^{n+1}/2`, so the terms are bounded by
the convergent geometric majorant `(2/|C|)·(|q|⁻¹)ⁿ`. -/
theorem qharmonic_summable (q C : ℝ) (hq : 2 ≤ |q|) (hC : C ≠ 0) :
    Summable (fun n : ℕ => (1 - C * q ^ (n + 1))⁻¹) := by
  have hq1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hCpos : (0 : ℝ) < |C| := abs_pos.mpr hC
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 / |C|) * (|q|⁻¹) ^ n)
    ((summable_geometric_of_lt_one (by positivity) hinvlt).mul_left (2 / |C|)) ?_
  have htend : Filter.Tendsto (fun n : ℕ => |C| * |q| ^ (n + 1)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hCpos
      ((tendsto_pow_atTop_atTop_of_one_lt hq1).comp (Filter.tendsto_add_atTop_nat 1))
  filter_upwards [htend.eventually_ge_atTop 2] with n hn
  rw [Real.norm_eq_abs, abs_inv]
  have hlow : |C| * |q| ^ (n + 1) / 2 ≤ |1 - C * q ^ (n + 1)| := by
    have htri := abs_sub_abs_le_abs_sub (C * q ^ (n + 1)) 1
    rw [abs_one, abs_mul, abs_pow, abs_sub_comm] at htri
    linarith [htri, hn]
  have h2pos : (0 : ℝ) < |C| * |q| ^ (n + 1) / 2 := by positivity
  calc |1 - C * q ^ (n + 1)|⁻¹
      ≤ (|C| * |q| ^ (n + 1) / 2)⁻¹ := inv_anti₀ h2pos hlow
    _ = (2 / |C|) * (|q|⁻¹) ^ (n + 1) := by
        rw [inv_pow]
        field_simp
    _ ≤ (2 / |C|) * (|q|⁻¹) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (|q|⁻¹) ^ (n + 1) = (|q|⁻¹) ^ n * |q|⁻¹ := pow_succ _ _
          _ ≤ (|q|⁻¹) ^ n * 1 :=
              mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (le_of_lt hq1))
                (pow_nonneg (by positivity) n)
          _ = (|q|⁻¹) ^ n := mul_one _

/-! ### Down-payment on `borwein_approximants`: denominator integrality (Borwein Lemma 2), general

`pValG q C n` is Borwein's q-Padé denominator `pₙ(C,q)` (second/Gaussian-binomial form), real-valued;
`pIntG q α β n` is its `β^{n-1}`-cleared integer version for integer `q` and `C = α/β`. The lemma
`pIntG_cast` says they agree after clearing — so `β^{n-1}·pₙ(α/β,q) ∈ ℤ` for ALL integer `q` and
rational `C = α/β`. This generalizes `pInt_cast` (the `q=2, C=8/3` case in `Pade.lean`) and is the
Lemma-2 sub-obligation of the general engine (`PENDING_WORK.md`, path 2). Self-contained: rests only on
the general Gaussian-binomial bridge `qBin_map` (`QBinom.lean`). -/

/-- General real-valued q-Padé denominator `pₙ(C,q)` (Borwein Lemma 2, Gaussian-binomial form). -/
noncomputable def pValG (q C : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-C) ^ k * q ^ (k * (k + 3) / 2)
    * qBin q (n - 1) k * qBin q (n + k - 1) (n - 1)

/-- The `β^{n-1}`-cleared **integer** q-Padé denominator for integer `q` and `C = α/β`. -/
def pIntG (q α β : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-α) ^ k * β ^ (n - 1 - k) * q ^ (k * (k + 3) / 2)
    * qBin q (n - 1) k * qBin q (n + k - 1) (n - 1)

/-- **Borwein Lemma 2, general form.** `(pIntG q α β n : ℝ) = β^{n-1} · pₙ(α/β, q)`. So for every
integer `q` and rational `C = α/β`, the `β^{n-1}`-cleared q-Padé denominator is an integer.
Generalizes `pInt_cast` (`q=2, C=8/3`); a down-payment on discharging `borwein_approximants`. -/
lemma pIntG_cast (q α β : ℤ) (hβ : β ≠ 0) (n : ℕ) :
    (pIntG q α β n : ℝ) = (β : ℝ) ^ (n - 1) * pValG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  have hβr : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  rw [pIntG, pValG, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hclear : (β : ℝ) ^ (n - 1) * (-((α : ℝ) / (β : ℝ))) ^ k
      = (-(α : ℝ)) ^ k * (β : ℝ) ^ (n - 1 - k) := by
    have hbk : (β : ℝ) ^ (n - 1) = (β : ℝ) ^ (n - 1 - k) * (β : ℝ) ^ k := by
      rw [← pow_add]; congr 1; omega
    have hkey : (β : ℝ) ^ k * (-((α : ℝ) / (β : ℝ))) ^ k = (-(α : ℝ)) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hbk, mul_assoc, hkey]; ring
  have hb1 : qBin ((q : ℤ) : ℝ) (n - 1) k = ((qBin q (n - 1) k : ℤ) : ℝ) :=
    qBin_map (Int.castRingHom ℝ) q (n - 1) k
  have hb2 : qBin ((q : ℤ) : ℝ) (n + k - 1) (n - 1) = ((qBin q (n + k - 1) (n - 1) : ℤ) : ℝ) :=
    qBin_map (Int.castRingHom ℝ) q (n + k - 1) (n - 1)
  rw [hb1, hb2, ← hclear]
  ring

/-- General `β^n`-cleared `c`-product `∏_{k=1}^n (β − α·qᵏ) ∈ ℤ` (clears `∏(1 − C·qᵏ)`, `C = α/β`). -/
def CPintG (q α β : ℤ) (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc 1 n, (β - α * q ^ k)

/-- General integer `q`-product `∏_{k=⌈n/2⌉}^n (1 − qᵏ) ∈ ℤ` (equals `∏(1 − qᵏ)` for integer `q`). -/
def QPintG (q : ℤ) (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)

/-- `(CPintG q α β n : ℝ) = βⁿ · ∏_{k=1}^n (1 − (α/β)·qᵏ)` (generalizes `CPint_cast`, `q=2,C=8/3`). -/
lemma CPintG_cast (q α β : ℤ) (hβ : β ≠ 0) (n : ℕ) :
    (CPintG q α β n : ℝ)
      = (β : ℝ) ^ n * ∏ k ∈ Finset.Icc 1 n, (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ k) := by
  have hβr : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  rw [CPintG]
  push_cast
  rw [show (β : ℝ) ^ n = ∏ _k ∈ Finset.Icc 1 n, (β : ℝ) from by rw [Finset.prod_const, hcard],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  field_simp

/-- `(QPintG q n : ℝ) = ∏_{k=⌈n/2⌉}^n (1 − qᵏ)` (generalizes `QPint_cast`, `q=2`). -/
lemma QPintG_cast (q : ℤ) (n : ℕ) :
    (QPintG q n : ℝ) = ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - (q : ℝ) ^ k) := by
  rw [QPintG]
  push_cast
  rfl

/-- General clearing factor `Wₙ(C,q) = (n−2)!·∏_{k=1}^n(1−C·qᵏ)·∏_{k=⌈n/2⌉}^n(1−qᵏ)`
(generalizes `Wterm`, the `q=2,C=8/3` case). -/
noncomputable def WtermG (q C : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)
    * (∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k))
    * (∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k))

/-- The general cleared **integer denominator** `β^{2n}·Wₙ·pₙ`, for integer `q` and `C = α/β`. -/
def BdenG (q α β : ℤ) (n : ℕ) : ℤ :=
  β * (Nat.factorial (n - 2)) * CPintG q α β n * QPintG q n * pIntG q α β n

/-- **Borwein Lemma 2 (denominator integrality), general form — MILESTONE.** For every integer `q`
and rational `C = α/β` (β ≠ 0, n ≥ 1), `(BdenG q α β n : ℝ) = β^{2n}·Wₙ(α/β,q)·pₙ(α/β,q)`, so the
q-Padé denominator coefficient `β^{2n}·Wₙ·pₙ` is an integer. Generalizes `Bden_cast` (the `q=2,C=8/3`
case) by assembling `CPintG_cast`, `QPintG_cast`, `pIntG_cast`. This fully discharges the Lemma-2
sub-obligation of the general `borwein_approximants` (`PENDING_WORK.md`, path 2). -/
lemma BdenG_cast (q α β : ℤ) (hβ : β ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (BdenG q α β n : ℝ)
      = (β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
          * pValG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  have hb : (β : ℝ) ^ (2 * n) = (β : ℝ) ^ n * (β : ℝ) ^ (n - 1) * (β : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show 2 * (m + 1) = (m + 1) + m + 1 from by ring,
      pow_add, pow_add, pow_one]
  rw [BdenG]
  push_cast
  rw [CPintG_cast q α β hβ, QPintG_cast q, pIntG_cast q α β hβ, WtermG, hb]
  ring

/-- **The series in `borwein_thm1` converges.** For integer `q` with `|q| ≥ 2` and any rational `c`,
`∑ₙ 1/(qⁿ⁺¹ + c)` is summable — so the headline general statement is about a genuine convergent sum.
(Same geometric-majorant argument as `qharmonic_summable`.) -/
theorem Sgen_summable (q : ℤ) (hq : 2 ≤ |q|) (c : ℚ) :
    Summable (fun n : ℕ => (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have hq1 : (1 : ℝ) < |(q : ℝ)| := by linarith
  have hqpos : (0 : ℝ) < |(q : ℝ)| := by linarith
  have hinvlt : |(q : ℝ)|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 : ℝ) * (|(q : ℝ)|⁻¹) ^ n)
    ((summable_geometric_of_lt_one (by positivity) hinvlt).mul_left 2) ?_
  have htend : Filter.Tendsto (fun n : ℕ => |(q : ℝ)| ^ (n + 1)) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hq1).comp (Filter.tendsto_add_atTop_nat 1)
  filter_upwards [htend.eventually_ge_atTop (2 * |(c : ℝ)| + 2)] with n hn
  rw [Real.norm_eq_abs, abs_div, abs_one]
  have hlow : |(q : ℝ)| ^ (n + 1) / 2 ≤ |(q : ℝ) ^ (n + 1) + (c : ℝ)| := by
    have htri := abs_sub_abs_le_abs_sub ((q : ℝ) ^ (n + 1)) (-(c : ℝ))
    rw [abs_pow, abs_neg, sub_neg_eq_add] at htri
    linarith [htri, hn]
  have h2pos : (0 : ℝ) < |(q : ℝ)| ^ (n + 1) / 2 := by positivity
  calc (1 : ℝ) / |(q : ℝ) ^ (n + 1) + (c : ℝ)|
      ≤ 1 / (|(q : ℝ)| ^ (n + 1) / 2) := one_div_le_one_div_of_le h2pos hlow
    _ = 2 * (|(q : ℝ)|⁻¹) ^ (n + 1) := by rw [inv_pow]; field_simp
    _ ≤ 2 * (|(q : ℝ)|⁻¹) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc (|(q : ℝ)|⁻¹) ^ (n + 1) = (|(q : ℝ)|⁻¹) ^ n * |(q : ℝ)|⁻¹ := pow_succ _ _
          _ ≤ (|(q : ℝ)|⁻¹) ^ n * 1 :=
              mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (le_of_lt hq1))
                (pow_nonneg (by positivity) n)
          _ = (|(q : ℝ)|⁻¹) ^ n := mul_one _

/-! ### Down-payment on the GENERAL numerator integrality (Borwein Lemma 3, path 3b)

Borwein's general numerator-integrality proof (paper p.143) needs the divisibility
`(1 − qᵐ) | ∏_{k=⌈n/2⌉}^n (1 − qᵏ)` for `1 ≤ m ≤ n` (it lets the `q`-denominators of the residue
derivative cancel). Proved here in full for integer `q`. -/

/-- The interval `⌈n/2⌉ .. n` contains a multiple of `m` (for `1 ≤ m ≤ n`): either the largest
multiple `m·⌊n/m⌋` (when it reaches `⌈n/2⌉`) or `m` itself (which then lies in the interval). -/
theorem mult_in_upper_half (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∃ k ∈ Finset.Icc ((n + 1) / 2) n, m ∣ k := by
  have hmod : n % m < m := Nat.mod_lt n (by omega)
  have hdm : m * (n / m) + n % m = n := Nat.div_add_mod n m
  set q0 := m * (n / m) with hq0
  by_cases hc : (n + 1) / 2 ≤ q0
  · exact ⟨q0, Finset.mem_Icc.mpr ⟨hc, by omega⟩, hq0 ▸ dvd_mul_right m (n / m)⟩
  · exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, hmn⟩, dvd_refl m⟩

/-- **Borwein's divisibility fact** (Lemma 3 proof, general `q`): for integer `q` and `1 ≤ m ≤ n`,
`(1 − qᵐ)` divides `∏_{k=⌈n/2⌉}^n (1 − qᵏ)`. -/
theorem borwein_div (q : ℤ) (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (1 - q ^ m) ∣ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k) := by
  obtain ⟨k, hk, j, hj⟩ := mult_in_upper_half n m hm hmn
  have hdvd : (1 - q ^ m) ∣ (1 - q ^ k) := by
    have hqk : q ^ k = (q ^ m) ^ j := by rw [hj, pow_mul]
    rw [hqk]
    simpa using sub_dvd_pow_sub_pow (1 : ℤ) (q ^ m) j
  exact hdvd.trans (Finset.dvd_prod_of_mem _ hk)

/-- **Path-3a building block:** `qᵃ⁺¹ − 1` is coprime to `q` (`qᵃ⁺¹ − 1 ≡ −1 mod q`). This is why the
q-Lagrange coefficients `μⱼ` — whose denominators are products of factors `q^d − 1` — have
denominators coprime to `q`; combined with the `q`-power clearing it gives `N_h ∈ ℤ` for general `q`
(the general analog of the `q=2` 2-adic ∧ odd-denominator argument, `PENDING_WORK.md` path 3a). -/
theorem coprime_qpow_sub_one (q : ℤ) (a : ℕ) : IsCoprime (q ^ (a + 1) - 1) q :=
  ⟨-1, q ^ a, by rw [pow_succ]; ring⟩

/-! The former `axiom borwein_approximants` (and the theorems `qharmonic_irrational`, `borwein_thm1`,
`irrational_sum_two_pow_sub_one` it underwrote) have been **fully discharged**: every one of Borwein's
five lemmas — including Lemma 5 non-vanishing for negative base `q ≤ −2` via the sign dichotomy — is
now machine-checked. The axiom-free headlines live in `GeneralAssembly.lean`:
`qharmonic_irrational_abs`, `borwein_thm1_abs`, `irrational_sum_two_pow_sub_one_abs`, all for
`2 ≤ |q|` (both signs), with `#print axioms = [propext, Classical.choice, Quot.sound]`. -/

end LeanGallery.NumberTheory.Erdos1050
