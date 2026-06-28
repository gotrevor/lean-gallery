/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050.Integrality

/-!
# Borwein Lemma 3 (numerator integrality) — elementary route

Discharges `residue_open`'s second clause: `∃ a:ℕ→ℤ, ∀ n≥1, (a n:ℝ) = −β^{2n}·Wₙ·Acorr n`.

See `LEMMA3-ELEMENTARY-STRATEGY.md`. The key simplification over Borwein's residue/derivative proof:
the same q-Lagrange identity that gives `pFirst = pVal` also clears the Vandermonde `μ_j`
denominators in the numerator. This file builds the clearing infrastructure bottom-up.

## Section 1: the `QPint` divisibility (number-theoretic clearing of `Rrat`'s `q^l−1` denominators)
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- For `1 ≤ l ≤ n` the interval `[⌈n/2⌉, n]` (here `⌈n/2⌉ = (n+1)/2`) contains a multiple of `l`.
Either `l` is small enough that the interval (length `⌊(n+1)/2⌋ ≥ l`) spans a full residue cycle, or
`l` itself lies in `[⌈n/2⌉, n]`. -/
lemma interval_has_multiple {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n) :
    ∃ k ∈ Finset.Icc ((n + 1) / 2) n, l ∣ k := by
  -- largest multiple of `l` not exceeding `n`
  have hdiv : n = l * (n / l) + n % l := (Nat.div_add_mod n l).symm
  have hmod : n % l < l := Nat.mod_lt n (by omega)
  have h1 : 1 ≤ n / l := (Nat.one_le_div_iff (by omega)).mpr hln
  have h2 : l ≤ l * (n / l) := Nat.le_mul_of_pos_right l h1
  refine ⟨l * (n / l), Finset.mem_Icc.mpr ⟨?_, by omega⟩, Dvd.intro _ rfl⟩
  -- `l * (n/l) ≥ (n+1)/2`: either `l` small (interval spans a full cycle) or `l` itself qualifies
  by_cases hsmall : l ≤ (n + 1) / 2
  · omega
  · omega

/-- `(2^l − 1) ∣ (2^k − 1)` in `ℤ` whenever `l ∣ k`. -/
lemma two_pow_sub_one_dvd {l k : ℕ} (h : l ∣ k) :
    ((2 : ℤ) ^ l - 1) ∣ ((2 : ℤ) ^ k - 1) := by
  obtain ⟨s, rfl⟩ := h
  have := sub_dvd_pow_sub_pow ((2 : ℤ) ^ l) 1 s
  simpa [pow_mul] using this

/-- **`QPint` divisibility.** For `1 ≤ l ≤ n−1`, `(2^l − 1) ∣ QPint n`. This clears `Rrat`'s
denominators `q^l − 1` (Borwein's note: `(1−q^m) | ∏_{k=⌈n/2⌉}^n (1−q^k)`). -/
lemma QPint_dvd {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n - 1) :
    ((2 : ℤ) ^ l - 1) ∣ QPint n := by
  have hln' : l ≤ n := by omega
  obtain ⟨k, hk, hdvd⟩ := interval_has_multiple hl hln'
  have hfactor : ((2 : ℤ) ^ k - 1) ∣ QPint n := by
    have hmem : (1 - 2 ^ k) ∈ (Finset.Icc ((n + 1) / 2) n).image (fun k => (1 - 2 ^ k : ℤ)) := by
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    rw [QPint]
    have : ((2 : ℤ) ^ k - 1) ∣ (1 - 2 ^ k) := ⟨-1, by ring⟩
    exact this.trans (Finset.dvd_prod_of_mem _ hk)
  exact (two_pow_sub_one_dvd hdvd).trans hfactor

/-! ## Section 2: reorganizing `Acorr`'s headS-part

The headS-part of `Acorr` is `∑_t (∏_{k∈t}-q^k) ∑_j muW n j q^{|t|j} headS|t| j n`. Summing the
subset `t` first turns the inner factor into `∏_{k=1}^{n-1}(1-q^{k+j-h})`, which vanishes for `h>j`,
so the head sum truncates. See `LEMMA3-ELEMENTARY-STRATEGY.md`. -/

/-- `headS` with the inner sum reindexed from `range (n+j-1)` to `Icc 1 (n+j-1)` (set `h = m'+1`). -/
lemma headS_Icc (i j n : ℕ) :
    headS i j n = ∑ h ∈ Finset.Icc 1 (n + j - 1), (qB ^ (i * h))⁻¹ * (1 - cB * qB ^ h)⁻¹ := by
  rw [headS, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro m' _
  rw [Nat.add_comm 1 m']

/-- **Subset-product collapse** (signed, with a scalar `w`): `∑_{t⊆[1,m]} (∏_{k∈t}-q^k)·w^{|t|}
= ∏_{k=1}^m (1 - q^k·w)`. The engine of the headS reorganization (reverse of `Dterm_expand`). -/
lemma subset_prod_local (w : ℝ) (m : ℕ) :
    ∑ t ∈ (Finset.Icc 1 m).powerset, (∏ k ∈ t, (-qB ^ k)) * w ^ t.card
      = ∏ k ∈ Finset.Icc 1 m, (1 - qB ^ k * w) := by
  have hf : ∀ k, (1 : ℝ) - qB ^ k * w = 1 + (-qB ^ k) * w := by intro k; ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- `qB^{t·j}·(qB^{t·h})⁻¹ = (qB^{j−h})^t` (mixing nat powers and a zpow base). -/
lemma wpow (j h t : ℕ) : (qB ^ (t * j) : ℝ) * (qB ^ (t * h))⁻¹ = (qB ^ ((j : ℤ) - h)) ^ t := by
  rw [← zpow_natCast (qB ^ ((j : ℤ) - h)) t, ← zpow_mul, ← zpow_natCast qB (t * j),
    ← zpow_natCast qB (t * h), ← zpow_neg, ← zpow_add₀ qB_ne]
  congr 1
  push_cast; ring

/-- **Per-`j` headS reorganization.** Summing the subset `t ⊆ [1,n−1]` first collapses the headS-part
into a single product `∏_{k=1}^{n−1}(1−q^{k+j−h})` over the head index `h`:

`∑_t (∏_{k∈t}−q^k)·(q^{|t|·j}·headS|t| j n) = ∑_{h=1}^{n+j−1} u_h·∏_{k=1}^{n−1}(1−q^{k+j−h})`,
`u_h = (1−c·q^h)⁻¹`. -/
lemma headPart_inner (n j : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-qB ^ k)) * (qB ^ (t.card * j) * headS t.card j n)
      = ∑ h ∈ Finset.Icc 1 (n + j - 1),
        (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  -- substitute headS_Icc and distribute the t-term over the h-sum
  have hstep : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset,
      (∏ k ∈ t, (-qB ^ k)) * (qB ^ (t.card * j) * headS t.card j n)
        = ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - cB * qB ^ h)⁻¹ * ((∏ k ∈ t, (-qB ^ k)) * (qB ^ ((j : ℤ) - h)) ^ t.card) := by
    intro t _
    rw [headS_Icc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← wpow j h t.card]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ k * qB ^ ((j : ℤ) - h)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [← zpow_natCast qB k, ← zpow_add₀ qB_ne]
    congr 2
    ring
  rw [hprod, ← subset_prod_local (qB ^ ((j : ℤ) - h)) (n - 1), Finset.mul_sum]

/-- The full headS-part of `Acorr`, reorganized: pull `muW n j` out and apply `headPart_inner`. -/
lemma AccH_reorg (n : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * headS t.card j n)
      = ∑ j ∈ Finset.Icc 1 n, muW n j *
          ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← headPart_inner n j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **`Acorr` reorganized** into its Rrat-part (first sum) and the reorganized headS-part (second
sum). The headS-part's high-`h` heads have cancelled (via `headPart_inner`'s product collapse). -/
lemma Acorr_reorg (n : ℕ) :
    Acorr n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                  (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card))
              + ∑ j ∈ Finset.Icc 1 n, muW n j *
                  ∑ h ∈ Finset.Icc 1 (n + j - 1),
                    (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  have key : (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card))
              - (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * headS t.card j n))
            = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [Acorr, ← key, AccH_reorg]
  abel

/-! ## Section 3: head truncation + q-Lagrange clearing

`head_truncate` (auto-formalized by Aristotle, run `332e491b`, verified axiom-clean) removes the
high-`h` heads `h ∈ [j+1, n+j−1]` (the product `∏(1−q^{k+j−h})` vanishes there). The surviving
`∑_{h=1}^j` then re-indexes (j,h)-swap with the j-sum extended to `[1,n]` (the added `j<h` terms also
vanish), exposing the q-Lagrange combination `N_h = ∑_j muW n j ∏(1−q^{k+j−h}) ∈ ℤ`. -/

/-- **Head truncation** (Aristotle `332e491b`): for `1 ≤ n`, the head sum over `h ∈ [1, n+j−1]`
truncates to `h ∈ [1, j]` because the product `∏_{k=1}^{n−1}(1−q^{k+j−h})` vanishes for `h > j`
(the `k = h−j ∈ [1,n−1]` factor is `1 − q^0 = 0`). -/
theorem head_truncate (q : ℝ) (u : ℕ → ℝ) (n j : ℕ) (hn : 1 ≤ n) :
    ∑ h ∈ Finset.Icc 1 (n + j - 1),
        u h * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 j,
        u h * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( show j ≤ n + j - 1 from Nat.le_sub_one_of_lt ( by omega ) ) ) ];
  intros x hx hnx
  obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Icc 1 (n - 1), (k : ℤ) + j - x = 0 := by
    exact ⟨ x - j, Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt <| lt_of_not_ge fun h => hnx <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩, Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel <| show 1 ≤ n from hn, Nat.sub_add_cancel <| show 1 ≤ n + j from by linarith ] ⟩, by rw [ Nat.cast_sub <| by linarith [ Finset.mem_Icc.mp hx, not_le.mp fun h => hnx <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩ ] ] ; ring ⟩;
  rw [ Finset.prod_eq_zero hk.1 ] <;> aesop

/-- The product `∏_{k=1}^{n−1}(1−q^{k+j−h})` vanishes for `j < h ≤ n` (the `k = h−j ∈ [1,n−1]`
factor is `1 − q^0 = 0`). Used to extend partial `j`-sums to full ones. -/
lemma prod_vanish {n j h : ℕ} (hj : 1 ≤ j) (hjh : j < h) (hhn : h ≤ n) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 := by
  apply Finset.prod_eq_zero (i := h - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have : ((h - j : ℕ) : ℤ) + j - h = 0 := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [this, zpow_zero, sub_self]

/-- **headS-part in `N_h` form.** After truncation (`head_truncate`) the (j,h)-sum swaps and the
inner `j`-sum extends to `[1,n]` (the added `j<h` terms vanish by `prod_vanish`), exposing the
q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})`:

`∑_j muW n j ∑_{h=1}^{n+j−1} u_h ∏(…) = ∑_{h=1}^n u_h · (∑_j muW n j ∏(…))`. -/
lemma headSPart_NhForm (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j *
        ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
          ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  -- Step 1: truncate each head sum to h ≤ j, and bring muW inside.
  have h1 : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
        = ∑ h ∈ Finset.Icc 1 j,
            muW n j * ((1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) := by
    intro j _
    rw [head_truncate qB (fun h => (1 - cB * qB ^ h)⁻¹) n j hn, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  -- Step 2: swap the triangular double sum ∑_{j} ∑_{h≤j} = ∑_{h} ∑_{j≥h}.
  rw [Finset.sum_comm' (s := Finset.Icc 1 n) (t := fun j => Finset.Icc 1 j)
        (t' := Finset.Icc 1 n) (s' := fun h => Finset.Icc h n)
        (by intro j h
            show (j ∈ Finset.Icc 1 n ∧ h ∈ Finset.Icc 1 j)
              ↔ (j ∈ Finset.Icc h n ∧ h ∈ Finset.Icc 1 n)
            simp only [Finset.mem_Icc]; omega)]
  -- Step 3: extend the inner j-sum to [1,n] and pull u_h out.
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : (1 : ℕ) ≤ h))]
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j hj hjh
    rw [Finset.mem_Icc] at hj hjh
    have : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 :=
      prod_vanish (by omega) (by omega) hh.2
    rw [this]; ring

/-- **Rrat-part via q-Lagrange.** Each `t`-term's `j`-sum `∑_j muW n j (q^j)^{|t|}` is the Gaussian
binomial `q^{|t|}·[n+|t|−1,n−1]_q` (`qLag_thm`, valid as `|t| ≤ n−1 < n`), eliminating the Vandermonde
`muW` denominators. The result is `muW`-free: integer products times `Rrat |t|`. -/
lemma RratPart_qLag (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card)
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1
    omega
  have hpull : ∑ j ∈ Finset.Icc 1 n, (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card)
      = (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ t.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm j t.card]; ring
  rw [hpull, qLag_thm hn t.card hcard]

/-- **`Acorr` in clean form** — the structural target of the elementary Lemma-3 route. The Rrat-part
is now `muW`-free (Gaussian binomials), and the headS-part is `∑_{h=1}^n u_h·N_h` with the
q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})`. Integrality of
`β^{2n}·Wₙ·Acorr n` reduces to: (i) `β^{2n}·Wₙ·(Rrat-part) ∈ ℤ` (clear `Rrat`'s `q^l−1` denominators
by `QPint_dvd` and `c`-powers by `β`); (ii) `N_h ∈ ℤ` (out to Aristotle, `Lemma3-Nh-Leaf.lean`) with
`β^{2n}·Wₙ·u_h ∈ ℤ` (clear `u_h` by `CPint`). -/
theorem Acorr_clean (n : ℕ) (hn : 1 ≤ n) :
    Acorr n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
                  (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)))
              + ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
                  ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Acorr_reorg n, RratPart_qLag n hn, headSPart_NhForm n hn]

/-! ## Section 4: the integer clearing factor `β^{2n}·Wₙ` -/

/-- The cleared **integer** form of `β^{2n}·Wₙ = 3^{2n}·(n−2)!·∏(1−c·q^k)·∏(1−q^k)`. Since
`3^n·∏(1−c·q^k) = CPint` and `∏(1−q^k) = QPint`, this is `3^n·(n−2)!·CPint·QPint ∈ ℤ`. -/
def WI (n : ℕ) : ℤ := 3 ^ n * (Nat.factorial (n - 2)) * CPint n * QPint n

/-- `(WI n : ℝ) = β^{2n}·Wₙ`: the clearing factor is a machine-checked integer. -/
lemma WI_cast (n : ℕ) : (WI n : ℝ) = (βB : ℝ) ^ (2 * n) * Wterm n := by
  rw [WI, Wterm]
  push_cast
  rw [CPint_cast, QPint_cast]
  have hb : (βB : ℝ) ^ (2 * n) = 3 ^ n * 3 ^ n := by
    rw [show (βB : ℝ) = 3 from by simp [βB], ← pow_add]; congr 1; omega
  rw [hb]; ring

/-- The integer witness for `β^{2n}·Wₙ·(c^{i−l}/(q^l−1))`: clears `3^{i−l}` by `3^n` and `q^l−1` by
`QPint` (via `QPint_dvd`). -/
def RratTermInt (n i l : ℕ) : ℤ :=
  8 ^ (i - l) * 3 ^ (n - (i - l)) * (Nat.factorial (n - 2)) * CPint n * (QPint n / (2 ^ l - 1))

/-- **Per-term Rrat clearing**: `(RratTermInt n i l : ℝ) = WI n · c^{i−l}/(q^l−1)` for `1 ≤ l ≤ n−1`,
`l ≤ i ≤ n−1`. -/
lemma RratTermInt_cast {n i l : ℕ} (hn : 1 ≤ n) (hl1 : 1 ≤ l) (hli : l ≤ i) (hin : i ≤ n - 1) :
    (RratTermInt n i l : ℝ) = (WI n : ℝ) * (cB ^ (i - l) / (qB ^ l - 1)) := by
  obtain ⟨d, hd⟩ := QPint_dvd (l := l) (n := n) hl1 (by omega)
  have hne : ((2 : ℤ) ^ l - 1) ≠ 0 := by
    have : (1 : ℤ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℤ) ^ l ≠ 1 := by
      have : (2 : ℤ) ^ 1 ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl1
      omega
    omega
  have hdiv : QPint n / (2 ^ l - 1) = d := by rw [hd]; exact Int.mul_ediv_cancel_left d hne
  have hq : (qB ^ l - 1 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ qB ^ l := two_le_pow hl1
    simp only [qB] at this ⊢; linarith
  have hQ : (QPint n : ℝ) = (qB ^ l - 1) * (d : ℝ) := by
    have h1 : (QPint n : ℝ) = (((2 ^ l - 1) * d : ℤ) : ℝ) := by rw [← hd]
    rw [h1]; push_cast; simp only [qB]
  have h3 : (3 : ℝ) ^ n = 3 ^ (i - l) * 3 ^ (n - (i - l)) := by rw [← pow_add]; congr 1; omega
  rw [RratTermInt, hdiv, WI]
  push_cast
  rw [hQ, h3, show (cB : ℝ) = 8 / 3 from rfl, div_pow]
  field_simp

/-- **Rrat clearing.** `WI n · Rrat i ∈ ℤ` for `i ≤ n−1`: each `Rrat_closed` term clears. -/
lemma WI_mul_Rrat_int {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i ≤ n - 1) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) * Rrat i := by
  refine ⟨∑ l ∈ Finset.Icc 1 i, RratTermInt n i l, ?_⟩
  rw [Rrat_closed, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  exact RratTermInt_cast hn hl.1 hl.2 hi

/-- Per-`t` integer witness for the whole Rrat-part of `Acorr_clean`. -/
def RratCleanTermInt (n : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-(2 : ℤ) ^ k)) * (2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1))
    * (∑ l ∈ Finset.Icc 1 t.card, RratTermInt n t.card l)

/-- Each Rrat-part `t`-term, times `β^{2n}·Wₙ`, is the integer `RratCleanTermInt n t`. -/
lemma RratCleanTermInt_cast {n : ℕ} (hn : 1 ≤ n) {t : Finset ℕ}
    (ht : t ∈ (Finset.Icc 1 (n - 1)).powerset) :
    (RratCleanTermInt n t : ℝ) = (WI n : ℝ) *
      ((∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1))) := by
  have hcard : t.card ≤ n - 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have e1 : ((∏ k ∈ t, (-(2 : ℤ) ^ k) : ℤ) : ℝ) = ∏ k ∈ t, (-qB ^ k) := by
    rw [Int.cast_prod]; apply Finset.prod_congr rfl; intro k _; push_cast; simp [qB]
  have e4 : ((∑ l ∈ Finset.Icc 1 t.card, RratTermInt n t.card l : ℤ) : ℝ)
      = (WI n : ℝ) * Rrat t.card := by
    rw [Rrat_closed, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_Icc] at hl
    exact RratTermInt_cast hn hl.1 hl.2 hcard
  rw [RratCleanTermInt, Int.cast_mul, Int.cast_mul, e4, e1,
    show ((2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1) : ℤ) : ℝ)
        = qB ^ t.card * qBin qB (n + t.card - 1) (n - 1) from by
      push_cast [← qBin_two_cast]; simp [qB]]
  ring

/-- **Rrat-part integrality.** `β^{2n}·Wₙ · (Rrat-part of `Acorr_clean`) ∈ ℤ` — the entire `muW`-free
Rrat-part clears (integer products × `WI·Rrat`). The "clean half" of Lemma 3. -/
lemma WI_mul_RratClean_int (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) * ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, RratCleanTermInt n t, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact RratCleanTermInt_cast hn ht

/-! ## Section 5: the headS-part `u_h` clearing (toward headS-part integrality)

The headS-part is `∑_{h=1}^n u_h·N_h`, `u_h = (1−c·q^h)⁻¹`. `β^{2n}·Wₙ·u_h ∈ ℤ` because
`CPint = ∏_{k=1}^n(3−8·2^k)` carries the factor `(3−8·2^h)` that `u_h = 3/(3−8·2^h)` exposes. The
other factor `N_h ∈ ℤ` is the q-Lagrange crux (Aristotle leaf `06c2c62c`). -/

/-- `CPint` with its `h`-th factor removed (`h ∈ [1,n]`). -/
def CPdrop (n h : ℕ) : ℤ := ∏ k ∈ (Finset.Icc 1 n).erase h, (3 - 8 * 2 ^ k)

/-- `(3 − 8·2^h)·CPdrop n h = CPint n` for `h ∈ [1,n]`. -/
lemma CPint_factor {n h : ℕ} (hh : h ∈ Finset.Icc 1 n) :
    (3 - 8 * 2 ^ h) * CPdrop n h = CPint n :=
  Finset.mul_prod_erase (Finset.Icc 1 n) (fun k => 3 - 8 * 2 ^ k) hh

/-- The integer witness for `β^{2n}·Wₙ·u_h = 3^{n+1}·(n−2)!·QPint·CPdrop`. -/
def uClearInt (n h : ℕ) : ℤ := 3 ^ (n + 1) * (Nat.factorial (n - 2)) * QPint n * CPdrop n h

/-- **`u_h` clearing**: `(uClearInt n h : ℝ) = β^{2n}·Wₙ·(1−c·q^h)⁻¹` for `1 ≤ h ≤ n`. -/
lemma uClearInt_cast {n h : ℕ} (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    (uClearInt n h : ℝ) = (WI n : ℝ) * (1 - cB * qB ^ h)⁻¹ := by
  have hmem : h ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hh1, hhn⟩
  have hfac : (3 - 8 * 2 ^ h) * CPdrop n h = CPint n := CPint_factor hmem
  have h2 : (2 : ℝ) ≤ qB ^ h := two_le_pow hh1
  have hne : (3 - 8 * qB ^ h : ℝ) ≠ 0 := by simp only [qB] at h2 ⊢; nlinarith
  have hu : (1 - cB * qB ^ h)⁻¹ = 3 / (3 - 8 * qB ^ h) := by
    rw [show (1 - cB * qB ^ h : ℝ) = (3 - 8 * qB ^ h) / 3 from by simp only [cB]; ring, inv_div]
  have hCP : (CPint n : ℝ) = (3 - 8 * qB ^ h) * (CPdrop n h : ℝ) := by
    rw [← hfac]; push_cast; simp only [qB]
  rw [uClearInt, WI]
  push_cast
  rw [hu, hCP]
  field_simp
  ring

/-! ## Section 6: headS-part integrality and the full numerator clearing (conditional on `N_h ∈ ℤ`) -/

/-- **headS-part integrality**, given integer witnesses `Nz h = N_h`. `β^{2n}·Wₙ·(headS-part)
= ∑_h (β^{2n}·Wₙ·u_h)·N_h = ∑_h uClearInt·Nz h ∈ ℤ`. -/
lemma WI_mul_headS_int (n : ℕ) (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) *
      ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
        ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  refine ⟨∑ h ∈ Finset.Icc 1 n, uClearInt n h * Nz h, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Int.cast_mul, uClearInt_cast hh.1 hh.2, hNz h hh.1 hh.2]
  ring

/-- **Borwein Lemma 3 (numerator integrality), conditional on `N_h ∈ ℤ`.** Combines the Rrat-part
(`WI_mul_RratClean_int`) and headS-part (`WI_mul_headS_int`) integralities via `Acorr_clean` and
`WI_cast`: `−β^{2n}·Wₙ·Acorr n ∈ ℤ`. -/
lemma Acorr_int (n : ℕ) (hn : 1 ≤ n) (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) :
    ∃ a : ℤ, (a : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
  obtain ⟨rInt, hr⟩ := WI_mul_RratClean_int n hn
  obtain ⟨hInt, hh⟩ := WI_mul_headS_int n Nz hNz
  refine ⟨rInt - hInt, ?_⟩
  rw [← WI_cast]
  push_cast
  rw [hr, hh, Acorr_clean n hn]
  ring

/-! ## Section 6b: toward `N_h ∈ ℤ` — the 2-adic cleared product (port scaffold)

The crux integrality `N_h ∈ ℤ` rests on a 2-adic clearing: `qB^{(n−1)h}·∏_{k=1}^{n−1}(1−q^{k+j−h})`
is an INTEGER-coefficient polynomial in `qB^j` (`clearedProd`), so `qB^{(n−1)h}·N_h ∈ ℤ` via q-Lagrange;
combined with `μ_j`'s odd denominator this gives `N_h ∈ ℤ`. This lemma is the foundation either way
(local proof or porting the Aristotle result). -/

/-- **Cleared product**: `(qB^h)^{n−1}·∏_{k=1}^{n−1}(1−qB^{k+j−h}) = ∏_{k=1}^{n−1}(qB^h−qB^{k+j})`,
turning the zpow product (with `q^{−h}` denominators) into an integer-valued nat-power product. -/
lemma clearedProd (n j h : ℕ) :
    (qB ^ h) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j)) := by
  have hcard : (qB ^ h) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), qB ^ h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [mul_sub, mul_one]
  congr 1
  rw [← zpow_natCast qB h, ← zpow_add₀ qB_ne, ← zpow_natCast qB (k + j)]
  congr 1
  push_cast
  ring

/-- **2-adic clearing of `N_h`**: `qB^{(n−1)h}·N_h = ∑_j muW n j ∏_{k=1}^{n−1}(qB^h−qB^{k+j})`. The RHS
product is an INTEGER-coefficient polynomial in `qB^j` (each factor `2^h−2^{k+j} ∈ ℤ`), so by
`qLag_thm` (termwise, after expanding the product) the RHS — hence `qB^{(n−1)h}·N_h` — is an integer.
This is the 2-adic half (`N_h ∈ ℤ[1/2]`) of `N_h ∈ ℤ`. -/
lemma Nh_2adic (n h : ℕ) :
    (qB ^ h) ^ (n - 1) *
        ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, clearedProd n j h]

/-- Expand `∏_{k=1}^{n−1}(qB^h − qB^{k+j})` over subsets `t ⊆ [1,n−1]` as a polynomial in `qB^j`. -/
lemma prod_diff_expand (n j h : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * (qB ^ j) ^ t.card * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card) := by
  have hf : ∀ k, (qB ^ h - qB ^ (k + j) : ℝ) = (-qB ^ (k + j)) + qB ^ h := fun k => by ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const]
  have hexp : ∏ k ∈ t, (-qB ^ (k + j)) = (∏ k ∈ t, (-qB ^ k)) * (qB ^ j) ^ t.card := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _; rw [pow_add]; ring
  rw [hexp]

/-- **q-Lagrange reduction of the cleared `N_h`** (the `muW`-free form): `∑_j muW n j ∏(qB^h−qB^{k+j})`
equals a sum over subsets `t` of integer-valued terms (Gaussian binomials), via `prod_diff_expand` +
`qLag_thm`. With `Nh_2adic`, this gives `qB^{(n−1)h}·N_h ∈ ℤ` (the 2-adic half of `N_h ∈ ℤ`). -/
lemma Nh_prod_qLag (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muW n j * (qB ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expand n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLag_thm hn t.card hcard]

/-- Per-`t` integer witness for the cleared `N_h`. -/
def Nh2TermInt (n h : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-(2 : ℤ) ^ k)) * (2 ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
    * (2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1))

/-- Each `Nh_prod_qLag` `t`-term is the integer `Nh2TermInt n h t`. -/
lemma Nh2TermInt_cast (n h : ℕ) (t : Finset ℕ) :
    (Nh2TermInt n h t : ℝ) = (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
      * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  rw [Nh2TermInt]
  push_cast [← qBin_two_cast]
  simp only [qB]

/-- **Part (a) of `N_h ∈ ℤ`: the 2-adic half.** `(qB^h)^{n−1}·N_h ∈ ℤ`. (Combined with `μ_j`'s odd
denominator — part (b), still TODO — this gives `N_h ∈ ℤ`, discharging `Nh_integral`.) -/
lemma Nh_2adic_int (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (qB ^ h) ^ (n - 1) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Nh_2adic n h, Nh_prod_qLag n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermInt n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermInt_cast n h t

/-- **The combine** `ℤ[1/2] ∩ ℤ[1/odd] = ℤ`: if `2^m·N` and `D·N` are integers with `D` odd, then
`N` is an integer. (`A·D = 2^m·B`, `IsCoprime 2^m D` ⟹ `2^m ∣ A` ⟹ `N = A/2^m ∈ ℤ`.) -/
lemma int_of_clearings {N : ℝ} {A B D : ℤ} {m : ℕ} (hD : Odd D)
    (hA : (A : ℝ) = (2 : ℝ) ^ m * N) (hB : (B : ℝ) = (D : ℝ) * N) :
    ∃ z : ℤ, (z : ℝ) = N := by
  have hAD : A * D = 2 ^ m * B := by
    have hr : ((A * D : ℤ) : ℝ) = ((2 ^ m * B : ℤ) : ℝ) := by
      push_cast; rw [hA, hB]; ring
    exact_mod_cast hr
  have hmod : D % 2 = 1 := Int.odd_iff.mp hD
  have hnd : ¬ (2 : ℤ) ∣ D := by rw [Int.dvd_iff_emod_eq_zero]; omega
  have hdvd : (2 : ℤ) ^ m ∣ A :=
    (Int.prime_two).pow_dvd_of_dvd_mul_right m hnd ⟨B, hAD⟩
  obtain ⟨C, hC⟩ := hdvd
  refine ⟨C, ?_⟩
  have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
  have : (2 : ℝ) ^ m * (C : ℝ) = (2 : ℝ) ^ m * N := by
    rw [← hA, hC]; push_cast; ring
  exact mul_left_cancel₀ h2m this

/-! ### Part (b): `μ_j` has odd denominator (the last piece of `N_h ∈ ℤ`)

`muW n j = ∏_{l≠j}(1−q^l/q^j)⁻¹`. Multiplying the `l`-factor by the ODD integer `2^{|j−l|}−1` gives an
integer (`−1` if `l>j`, `2^{j−l}` if `l<j`), so the odd product `Vodd n j = ∏_{l≠j}(2^{|j−l|}−1)`
clears `muW n j`. Hence `N_h ∈ ℤ[1/odd]`, which with part (a) and `int_of_clearings` gives `N_h ∈ ℤ`. -/

/-- The explicit integer value of the cleared `l`-factor: `2^{j−l}` if `l<j`, else `−1`. -/
def zfac (j l : ℕ) : ℤ := if l < j then 2 ^ (j - l) else -1

/-- Per-factor odd clearing: `(2^{|j−l|}−1)·(1−q^l/q^j)⁻¹ = zfac j l ∈ ℤ`. -/
lemma factor_clear {j l : ℕ} (hlj : l ≠ j) :
    ((zfac j l : ℤ) : ℝ) = (((2 : ℤ) ^ (max j l - min j l) - 1 : ℤ) : ℝ) * (1 - qB ^ l / qB ^ j)⁻¹ := by
  have hq2 : (qB : ℝ) = 2 := rfl
  rw [zfac]
  rcases lt_or_gt_of_ne hlj with hlt | hgt
  · -- l < j : value 2^{j−l}
    rw [if_pos hlt]
    have hmm : max j l - min j l = j - l := by omega
    have ha1 : (2 : ℝ) ^ (j - l) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (j - l) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hdiv : (qB ^ l / qB ^ j : ℝ) = ((2 : ℝ) ^ (j - l))⁻¹ := by
      rw [hq2, show (2 : ℝ) ^ j = 2 ^ (j - l) * 2 ^ l from by rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    field_simp
  · -- l > j : value −1
    rw [if_neg (by omega)]
    have hmm : max j l - min j l = l - j := by omega
    have ha1 : (2 : ℝ) ^ (l - j) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (l - j) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hdiv : (qB ^ l / qB ^ j : ℝ) = (2 : ℝ) ^ (l - j) := by
      rw [hq2, show (2 : ℝ) ^ l = 2 ^ (l - j) * 2 ^ j from by rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    rw [show (1 : ℝ) - 2 ^ (l - j) = -(2 ^ (l - j) - 1) from by ring, inv_neg]
    field_simp

/-- The **odd** clearing product `Vodd n j = ∏_{l≠j}(2^{|j−l|}−1)`. -/
def Vodd (n j : ℕ) : ℤ := ∏ l ∈ (Finset.Icc 1 n).erase j, ((2 : ℤ) ^ (max j l - min j l) - 1)

/-- `Vodd n j` is odd (product of `2^{|j−l|}−1`, each odd since `|j−l| ≥ 1`). -/
lemma Vodd_odd (n j : ℕ) : Odd (Vodd n j) := by
  rw [Vodd]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro l hl
  have hne : max j l - min j l ≠ 0 := by
    have : l ≠ j := (Finset.mem_erase.mp hl).1; omega
  have heven : Even ((2 : ℤ) ^ (max j l - min j l)) := by
    rw [Int.even_pow]; exact ⟨by decide, hne⟩
  exact heven.sub_odd odd_one

/-- **Part (b): the odd clearing.** `Vodd n j · muW n j ∈ ℤ` — the odd product clears `μ_j`'s
denominator (per-factor `factor_clear`). -/
lemma Vodd_muW_int (n j : ℕ) : ∃ z : ℤ, (z : ℝ) = (Vodd n j : ℝ) * muW n j := by
  refine ⟨∏ l ∈ (Finset.Icc 1 n).erase j, zfac j l, ?_⟩
  rw [Int.cast_prod, Vodd, Int.cast_prod, muW, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  exact factor_clear (Finset.mem_erase.mp hl).1

/-- The odd common denominator `Dfull n = ∏_{j∈[1,n]} Vodd n j`, clearing every `muW n j`. -/
def Dfull (n : ℕ) : ℤ := ∏ j ∈ Finset.Icc 1 n, Vodd n j

/-- `Dfull n` is odd. -/
lemma Dfull_odd (n : ℕ) : Odd (Dfull n) := by
  rw [Dfull]
  exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun j _ => Vodd_odd n j)

/-- `Dfull n · muW n j ∈ ℤ` for `j ∈ [1,n]`. -/
lemma Dfull_muW_int {n j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    ∃ m : ℤ, (m : ℝ) = (Dfull n : ℝ) * muW n j := by
  obtain ⟨z, hz⟩ := Vodd_muW_int n j
  refine ⟨(∏ j' ∈ (Finset.Icc 1 n).erase j, Vodd n j') * z, ?_⟩
  have hD : (Dfull n : ℝ)
      = (Vodd n j : ℝ) * ((∏ j' ∈ (Finset.Icc 1 n).erase j, Vodd n j' : ℤ) : ℝ) := by
    rw [Dfull, ← Finset.mul_prod_erase (Finset.Icc 1 n) (Vodd n) hj]; push_cast; ring
  rw [hD]; push_cast; rw [hz]; ring

/-- `P_j = ∏_{k=1}^{n−1}(1−q^{k+j−h})` is an integer when `j ≥ h` (all exponents `≥ 1`). -/
lemma Pj_int {n j h : ℕ} (hjh : h ≤ j) :
    ∃ p : ℤ, (p : ℝ) = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  refine ⟨∏ k ∈ Finset.Icc 1 (n - 1), (1 - 2 ^ (k + j - h)), ?_⟩
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [show ((k : ℤ) + j - h) = ((k + j - h : ℕ) : ℤ) from by omega, zpow_natCast]
  push_cast
  simp [qB]

/-- **Part (b) at the `N_h` level**: `Dfull n · N_h ∈ ℤ`, with `Dfull n` odd. So `N_h ∈ ℤ[1/odd]`. -/
lemma Nh_odd_int (n h : ℕ) (_hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (Dfull n : ℝ) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc 1 n, ∃ b : ℤ, (b : ℝ) = (Dfull n : ℝ) *
      (muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) := by
    intro j hj
    rcases Nat.lt_or_ge j h with hlt | hge
    · refine ⟨0, ?_⟩
      rw [Finset.mem_Icc] at hj
      have hv : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 :=
        prod_vanish hj.1 hlt hhn
      rw [hv]; push_cast; ring
    · obtain ⟨m, hm⟩ := Dfull_muW_int hj
      obtain ⟨p, hp⟩ := Pj_int (n := n) hge
      exact ⟨m * p, by push_cast; rw [hm, hp]; ring⟩
  choose b hb using hterm
  refine ⟨∑ j ∈ (Finset.Icc 1 n).attach, b j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.Icc 1 n) _]
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  exact hb j hj

/-- **`N_h ∈ ℤ`** (per `(n,h)`): combine part (a) (`Nh_2adic_int`, 2-adic) and part (b)
(`Nh_odd_int`, odd) via `int_of_clearings`. -/
lemma Nh_int (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) =
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  obtain ⟨A, hA⟩ := Nh_2adic_int n h hn
  obtain ⟨B, hB⟩ := Nh_odd_int n h hh1 hhn
  have hA' : (A : ℝ) = (2 : ℝ) ^ (h * (n - 1)) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
    rw [hA, show (qB ^ h) ^ (n - 1) = (2 : ℝ) ^ (h * (n - 1)) from by
      rw [show qB = (2 : ℝ) from rfl, ← pow_mul]]
  exact int_of_clearings (Dfull_odd n) hA' hB

/-! ## Section 7: `N_h ∈ ℤ` DISCHARGED — and the now axiom-clean headline

The integrality of the q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})` — the
last open input — is now **machine-checked** (`Nh_int`), via 2-adic (`Nh_2adic_int`) ∧ odd-denominator
(`Nh_odd_int`) ⟹ `int_of_clearings`. So `Nh_integral` is a THEOREM and `erdos_1050` is axiom-clean. -/

/-- **`N_h ∈ ℤ`, now a THEOREM** (was the last axiom). For each `n ≥ 1` there are integer witnesses
`Nz h = N_h` (`1 ≤ h ≤ n`), assembled from the per-`(n,h)` integrality `Nh_int`. -/
theorem Nh_integral : ∀ n, 1 ≤ n → ∃ Nz : ℕ → ℤ, ∀ h, 1 ≤ h → h ≤ n →
    (Nz h : ℝ) = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  intro n hn
  choose Nz hNz using fun h (hh1 : 1 ≤ h) (hhn : h ≤ n) => Nh_int n h hn hh1 hhn
  refine ⟨fun h => if H : 1 ≤ h ∧ h ≤ n then Nz h H.1 H.2 else 0, fun h hh1 hhn => ?_⟩
  show ((dite (1 ≤ h ∧ h ≤ n) (fun H => Nz h H.1 H.2) (fun _ => 0) : ℤ) : ℝ) = _
  rw [dif_pos (⟨hh1, hhn⟩ : 1 ≤ h ∧ h ≤ n)]
  exact hNz h hh1 hhn

/-- **Borwein Lemma 3 (numerator integrality), now a THEOREM** modulo `Nh_integral`: there is an
integer sequence `aₙ = −β^{2n}·Wₙ·Acorr n`. -/
theorem numerator_integrality : ∃ a : ℕ → ℤ, ∀ n, 1 ≤ n →
    (a n : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
  have key : ∀ n, 1 ≤ n → ∃ a : ℤ, (a : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
    intro n hn
    obtain ⟨Nz, hNz⟩ := Nh_integral n hn
    exact Acorr_int n hn Nz hNz
  choose a ha using key
  exact ⟨fun n => if h : 1 ≤ n then a n h else 0, fun n hn => by simp only [dif_pos hn]; exact ha n hn⟩

/-- **O1 — Borwein Lemmas 1+2+3, all discharged modulo `Nh_integral`.** -/
theorem borwein_integrality : ∃ a b : ℕ → ℤ, ∀ n, 1 ≤ n →
    (b n : ℝ) * zB - a n = (βB : ℝ) ^ (2 * n) * Wterm n * Eterm n := by
  obtain ⟨a, ha⟩ := numerator_integrality
  refine ⟨a, fun n => -Bden n, fun n hn => ?_⟩
  rw [Eterm_eq_pVal hn (qLag_thm hn)]
  have hB := Bden_cast hn
  push_cast
  rw [ha n hn, hB]
  ring

/-- The reduced q-harmonic value `z = ∑_{j≥1} 1/(1 − (8/3)·2^j)` is irrational. -/
theorem irrational_zB : Irrational zB := by
  obtain ⟨a, b, hab⟩ := borwein_integrality
  apply irrational_of_intApprox zB (fun n => a (n + 1)) (fun n => b (n + 1))
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (Wterm_ne_zero (by omega))) (Eterm_ne_zero (by omega))
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by decide))
  · have hshift : Filter.Tendsto
        (fun n => (βB : ℝ) ^ (2 * (n + 1)) * Wterm (n + 1) * Eterm (n + 1)) Filter.atTop (nhds 0) :=
      cleared_error_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- **Erdős #1050.** The series `∑ 1/(2ⁿ − 3)` is irrational. -/
theorem erdos_1050 : Irrational S := irrational_S_iff_zB.mpr irrational_zB

end LeanGallery.NumberTheory.Erdos1050
