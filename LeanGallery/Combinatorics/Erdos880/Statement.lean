/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Construction
import LeanGallery.Combinatorics.Erdos880.Delta
import LeanGallery.Combinatorics.Erdos880.Thm9

/-!
# Erdős #880 — the designated statement (AUDIT SURFACE)

**If you are checking that this repository proves the right thing, read THIS file.**

`Construction.lean` is the proof engine. The two theorems below are the load-bearing statements
(definitionally the `Basic.lean` headlines), with the claims spelled out.

To confirm faithfulness, read — in addition to the signatures below — these definitions from
`Basic.lean` (≈ 10 lines total): `restrictedSumset`, `sumsetLE`, `restrictedSums`, `IsBasisOfOrder`,
`UnboundedGaps`, `BoundedGapsBy`.

**The problem (erdosproblems.com/880).** `A ⊆ ℕ` a basis of order `k`; `B` = integers that are a sum of
`k` or fewer distinct elements of `A`. Are the gaps `b_{n+1} − b_n` bounded? **Answer: yes for `k=2`,
NO for `k ≥ 3`** (Hegyvári–Hennecart–Plagne 2007). The headline is the negative `k ≥ 3` result.

⚠️ Direction matters: the theorem to prove is `UnboundedGaps`, not bounded gaps. (An earlier KB note
had this backwards.)

Source: N. Hegyvári, F. Hennecart, A. Plagne, *Answer to a question by Burr and Erdős on restricted
addition, and related results*, Combin. Probab. Comput. **16** (2007) 747–756.

When proven, `#print axioms` should end at `[propext, Classical.choice, Quot.sound]` (kernel-pure).
-/

namespace LeanGallery.Combinatorics.Erdos880

/-- **Erdős Problem #880 (the resolution, `k ≥ 3`).** For every order `h ≥ 3` there exists an additive
basis `A` of order `h` whose set of restricted sums (sums of `≤ h` distinct elements) has arbitrarily
long gaps. So the Burr–Erdős gap-boundedness fails for `k ≥ 3`. -/
theorem erdos_880 (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ UnboundedGaps (restrictedSums A h) :=
  erdos_880_unbounded h hh

/-- **Erdős Problem #880 (the `k = 2` case).** For a basis `A` of order `2`, the restricted-sum set has
gaps eventually bounded by `2`. -/
theorem erdos_880_order_two (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    BoundedGapsBy (restrictedSums A 2) 2 :=
  erdos_880_k2 A hbasis

/-- **Erdős Problem #880 — strengthened to HHP07 Theorem 1(ii) in full.** For every `h ≥ 3` the witness
basis `A` has order *exactly* `h`: it is a basis of order `h` but **not** of order `h − 1`, and its
restricted-sum set still has unbounded gaps. So the counterexample is genuinely an order-`h` basis, not
an order-`<h` basis in disguise. (The plain `erdos_880` above is already a faithful negative answer,
since the problem asks for *some* basis of order `h`; this records the sharper construction.) -/
theorem erdos_880_exact_order (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ ¬ IsBasisOfOrder A (h - 1) ∧
      UnboundedGaps (restrictedSums A h) :=
  erdos_880_exact h hh

/-- **HHP07 Theorem 3 — the quantitative companion `k(h) ≥ 2^{h-2}+h−1`.** The same witness basis `A`
keeps unbounded gaps not just for the `h`-fold restricted sums but for the exact `l`-fold restricted
sumset `l × A` (`restrictedSumset A l`) for *every* `l` up to `2^{h-2}+h−2`. So for this `A`, the
restricted-order gap threshold `min{k : Δ(k × A) finite}` is `≥ 2^{h-2}+h−1`, which is the lower bound
`k(h) ≥ 2^{h-2}+h−1` of HHP07 Theorem 3. (Proved by the *same elementary construction* as `erdos_880`
— no Kneser/Erdős–Rado, contrary to earlier project notes. `k(h)`'s finiteness is HHP07 Conjecture 2,
open, so the witness form is the faithful statement.) -/
theorem erdos_880_thm3_kh (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧
      ∀ l, 1 ≤ l → l ≤ 2 ^ (h - 2) + h - 2 → UnboundedGaps (restrictedSumset A l) :=
  erdos_880_thm3 h hh

/-- **HHP07 Theorem 4 — `f(h) ≥ 2^{h-2}+h−1`.** The same witness basis `A = constA h` has restricted
order **exactly** `2^{h-2}+h−1`: it is a restricted basis of that order (`IsRestrictedBasisOfOrder A
(2^{h-2}+h−1)` — every large integer is a sum of `≤ 2^{h-2}+h−1` *distinct* elements of `A`) but **not**
of order `2^{h-2}+h−2` (its `(2^{h-2}+h−2)`-fold restricted sums have unbounded gaps, by Theorem 3).
By monotonicity this pins `ord_r(A) = 2^{h-2}+h−1`, giving `f(h) ≥ 2^{h-2}+h−1`. Proved by the *same
elementary construction* (no Kneser). Witness form: `f`'s finiteness is open (HHP07 Conj 2), as for
`k`. -/
theorem erdos_880_thm4_fh (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧
      IsRestrictedBasisOfOrder A (2 ^ (h - 2) + h - 1) ∧
      ¬ IsRestrictedBasisOfOrder A (2 ^ (h - 2) + h - 2) :=
  erdos_880_thm4 h hh

/-- **HHP07 Theorem 4, sharp.** The witness basis's restricted order is *exactly* `2^{h-2}+h−1`:
`restrictedOrder (constA h) = 2^{h-2}+h−1` (the explicit `ord_r`, via `Nat.sInf`). -/
theorem erdos_880_thm4_exact (h : ℕ) (hh : 3 ≤ h) :
    restrictedOrder (constA h) = 2 ^ (h - 2) + h - 1 :=
  constA_restrictedOrder_eq h hh

/-! ### Faithful `Δ` form (HHP07 §1 definition of `Δ = limsup` gaps)

The headlines above use the predicates `UnboundedGaps` / `BoundedGapsBy`. The two below restate the
`k ≥ 3` and `k = 2` answers using the paper's actual gap functional `Δ(X) = limsup(a_{i+1}−a_i) ∈ ℕ∞`
(faithfully formalized in `Delta.lean` as `Delta`, the least eventual gap bound). These are the exact
statements `Δ(𝒜 ∪ 2×𝒜 ∪ ⋯ ∪ h×𝒜) = +∞` and `Δ(2×𝒜) ≤ 2` of Theorem 1. -/

/-- **Erdős #880, faithful `Δ` form (`k ≥ 3`).** For every `h ≥ 3` the witness basis `constA h` is an
order-`h` basis whose restricted-sum set has asymptotic gap functional `Δ = +∞`, exactly the paper's
`Δ(𝒜 ∪ 2×𝒜 ∪ ⋯ ∪ h×𝒜) = +∞` (Theorem 1(ii)). -/
theorem erdos_880_delta (h : ℕ) (hh : 3 ≤ h) :
    Delta (restrictedSums (constA h) h) = ⊤ :=
  Delta_eq_top_of_unboundedGaps
    (restrictedSums_infinite (by omega) (constA_infinite h hh))
    (constA_unboundedGaps h hh)

/-- **Erdős #880, faithful `Δ` form (`k = 2`).** For a basis `A` of order `2`, the restricted-sum set
has asymptotic gap functional `Δ(2×A) ≤ 2` — the paper's Theorem 1(i). -/
theorem erdos_880_order_two_delta (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    Delta (restrictedSums A 2) ≤ 2 :=
  Delta_restrictedSums_two_le A hbasis

/-- **HHP07 Proposition 7 (sharp form), the first non-construction frontier theorem.** For *every*
infinite set of positive integers `A`, `Δ(3 × A) ≤ Δ(2 × A)` — the paper's sharp bound (no `+1`),
obtained via a strict-successor cover (`EvGapLe.cover`) that transfers the gap bound with the same `d`.
This is a genuinely-new result about general sets, not the #880 construction. -/
theorem erdos_880_prop7 (A : Set ℕ) (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) :
    Delta (restrictedSumset A 3) ≤ Delta (restrictedSumset A 2) :=
  Delta_restrictedSumset_three_le A hA hpos

/-- **HHP07 Proposition 5 (exact-fold form), a non-construction frontier theorem.** For *every*
infinite set of positive integers `A` and `1 ≤ h₀ ≤ h`: if `Δ(h₀ × A)` is finite then so is
`Δ(h × A)`. Gap-finiteness of the exact `h`-fold restricted sumset propagates upward in the fold
count. This is the genuine Proposition 5 of HHP07 (the general-`h` generalization of Proposition 7),
proved kernel-pure via the bounded-extension covering (`Delta.lean`). -/
theorem erdos_880_prop5 {A : Set ℕ} {h₀ h : ℕ} (hA : A.Infinite) (hh₀ : 1 ≤ h₀) (hle : h₀ ≤ h)
    (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    Delta (restrictedSumset A h) < ⊤ :=
  Delta_restrictedSumset_lt_top_of_le hA hh₀ hle hfin

/-- **HHP07 Theorem 9, one-step inequality (structural core).** The combinatorial heart of Theorem 9,
*independent* of its two deep ingredients (the Erdős–Rado sunflower lemma and the density estimate,
which only serve to *produce* the configuration below). If an integer `n₀` admits `h + 1`
representations as sums of `g` pairwise-distinct elements of `A` whose `h + 1` summand-sets are
**pairwise disjoint** (the paper's `Eⱼ ∖ F` with `g = h+1−|F|`), then `Δ((h+g) × A) ≤ Δ(h × A)`. This
is exactly the inequality `Δ(hⱼ₊₁ × A) ≤ Δ(hⱼ × A)` driving the monotone subsequence of Theorem 9
(`h₁ = h + g = 2h+1−|F|`). Proved kernel-pure via the disjoint-pigeonhole covering (`Thm9.lean`). -/
theorem erdos_880_thm9_step {A : Set ℕ} {h g n₀ : ℕ} (hA : A.Infinite) (hh : 1 ≤ h)
    (R : Fin (h + 1) → Finset ℕ) (hRA : ∀ i, ↑(R i) ⊆ A) (hRcard : ∀ i, (R i).card = g)
    (hRsum : ∀ i, ∑ a ∈ R i, a = n₀) (hRdisj : ∀ i j, i ≠ j → Disjoint (R i) (R j)) :
    Delta (restrictedSumset A (h + g)) ≤ Delta (restrictedSumset A h) :=
  Delta_restrictedSumset_le_of_disjoint_reps hA hh R hRA hRcard hRsum hRdisj

/-- **HHP07 Theorem 8 (the monotone subsequence), the deepest non-construction result formalized.**
For every infinite set `A` of positive integers with `Δ(h₀ × A)` finite (`h₀ ≥ 1`), there is a strictly
increasing sequence `(seq j)` from `h₀` along which `Δ(seq j × A)` is non-increasing. Fully
machine-checked and kernel-pure: built on the **Erdős–Rado sunflower lemma** (`Sunflower.lean`, mathlib
has none) plus the density estimate (`Thm9.lean`: `evGapLe_count_lower` + `restrictedSumset_count_le` +
`density_growth`) and the iteration `thm8_iteration`. -/
theorem erdos_880_thm8' {A : Set ℕ} {h₀ : ℕ}
    (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) (hh₀ : 1 ≤ h₀)
    (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ seq 0 = h₀ ∧
      ∀ j, Delta (restrictedSumset A (seq (j + 1))) ≤ Delta (restrictedSumset A (seq j)) :=
  erdos_880_thm8 hA hpos hh₀ hfin

/-- **HHP07 Theorem 9 (the precise refinement of Theorem 8).** For every infinite set `A` of positive
integers with `Δ(h₀ × A)` finite (`h₀ ≥ 1`), there is a sequence `(seq j)` from `h₀` with the paper's
exact increment bounds `seq j + 2 ≤ seq (j+1) ≤ seq j + h₀ + 1` and `Δ(seq (j+1) × A) ≤ Δ(seq j × A)`.
Fully machine-checked and kernel-pure: the sunflower is taken with the *fixed* `(h₀+1)`-sized objects
at each step (`Thm9.lean`, `exists_fold_Delta_le_precise`). -/
theorem erdos_880_thm9' {A : Set ℕ} {h₀ : ℕ}
    (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) (hh₀ : 1 ≤ h₀)
    (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    ∃ seq : ℕ → ℕ, seq 0 = h₀ ∧ ∀ j,
      seq j + 2 ≤ seq (j + 1) ∧ seq (j + 1) ≤ seq j + h₀ + 1 ∧
      Delta (restrictedSumset A (seq (j + 1))) ≤ Delta (restrictedSumset A (seq j)) :=
  erdos_880_thm9 hA hpos hh₀ hfin

/-- **Δ of the restricted-sum set is antitone in the order** (general, non-construction). For any
infinite `A` and `1 ≤ k ≤ k'`, `Δ(restrictedSums A k') ≤ Δ(restrictedSums A k)` — allowing more folds
can only shrink the gaps (a subset has gaps at least as large). A monotonicity in the direction of
HHP07 Conjecture 6, holding for *every* infinite set `A`. -/
theorem Delta_restrictedSums_anti {A : Set ℕ} {k k' : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ k')
    (hA : A.Infinite) :
    Delta (restrictedSums A k') ≤ Delta (restrictedSums A k) :=
  Delta_anti (restrictedSums_mono hk) (restrictedSums_infinite hk1 hA)

/-- **HHP07 Proposition 5, cumulative form.** Gap-finiteness of the restricted-sum set propagates
*upward* in the order: for any infinite `A`, if `Δ(restrictedSums A k) < +∞` and `k ≤ k'` (with
`1 ≤ k`), then `Δ(restrictedSums A k') < +∞`. (The exact-fold form `Δ(h×A)` of Prop 5 needs the paper's
`α(i)` density argument; this cumulative `≤k`-fold version is immediate from `Δ`-antitonicity.) -/
theorem Delta_restrictedSums_lt_top_of_le {A : Set ℕ} {k k' : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ k')
    (hA : A.Infinite) (hfin : Delta (restrictedSums A k) < ⊤) :
    Delta (restrictedSums A k') < ⊤ :=
  lt_of_le_of_lt (Delta_restrictedSums_anti hk1 hk hA) hfin

/-- **HHP07 Theorem 3, faithful `Δ` form.** For the witness basis `A = constA h`, *every* exact fold
`l × A` with `1 ≤ l ≤ 2^{h-2}+h−2` has asymptotic gap functional `Δ(l × A) = +∞` — the genuine
`Δ = limsup` reading of the lower bound `k(h) ≥ 2^{h-2}+h−1` (Theorem 3). -/
theorem erdos_880_thm3_delta (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧
      ∀ l, 1 ≤ l → l ≤ 2 ^ (h - 2) + h - 2 → Delta (restrictedSumset A l) = ⊤ :=
  ⟨constA h, constA_isBasis h hh, fun _l hl1 hl2 =>
    Delta_eq_top_of_unboundedGaps
      (restrictedSumset_infinite hl1 (constA_infinite h hh))
      (UnboundedGaps_mono (restrictedSumset_subset_restrictedSums hl1 hl2)
        (constA_unboundedGaps_L h hh))⟩

/-- **HHP07 Theorem 4, faithful `Δ`-transition form.** For the witness basis `A = constA h` the
asymptotic gap functional of its `≤ k`-fold restricted-sum set jumps from `+∞` to finite *exactly* at
the restricted order `k = 2^{h-2}+h−1`:

* `Δ(restrictedSums A (2^{h-2}+h−2)) = +∞` — still unbounded one fold below the threshold (Theorem 3);
* `Δ(restrictedSums A (2^{h-2}+h−1)) < +∞` — bounded at the threshold (`A` is a restricted basis of
  that order, so the set is cofinite).

This is the genuine `Δ = limsup` reading of `restrictedOrder (constA h) = 2^{h-2}+h−1`
(`erdos_880_thm4_exact`): the restricted order is precisely the gap-finiteness threshold. -/
theorem erdos_880_thm4_delta_transition (h : ℕ) (hh : 3 ≤ h) :
    Delta (restrictedSums (constA h) (2 ^ (h - 2) + h - 2)) = ⊤ ∧
      Delta (restrictedSums (constA h) (2 ^ (h - 2) + h - 1)) < ⊤ :=
  ⟨Delta_eq_top_of_unboundedGaps
      (restrictedSums_infinite
        (by have : 0 < 2 ^ (h - 2) := pow_pos (by norm_num) _; omega)
        (constA_infinite h hh))
      (constA_unboundedGaps_L h hh),
    lt_of_le_of_lt (Delta_le_one_of_cofinite (constA_isRestrictedBasis h hh))
      (by exact_mod_cast ENat.natCast_lt_top 1)⟩

end LeanGallery.Combinatorics.Erdos880
