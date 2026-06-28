/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Delta
import LeanGallery.Combinatorics.Erdos880.Sunflower

/-!
# HHP07 Theorem 9 — structural core (sunflower-free, density-free)

Theorem 9 of HHP07 builds an increasing sequence `(hⱼ)` with `Δ(hⱼ₊₁ × A) ≤ Δ(hⱼ × A)`. Each step
rests on a purely combinatorial fact about the restricted sumset, **independent** of the two deep
ingredients used to *produce* the configuration (the Erdős–Rado sunflower lemma, and the density
estimate `A(x) ≫ x^{1/h}`). That combinatorial core is proved here.

The configuration the sunflower lemma supplies, stripped of the core `F`, is: an integer `n₀` with
`h + 1` representations as sums of `g` pairwise-distinct elements of `A`, whose `h + 1` summand-sets
are **pairwise disjoint**. (In the paper's notation the representations are `Eⱼ ∖ F`, `g = h+1−|F|`,
and pairwise-disjointness is exactly `Eᵢ ∩ Eⱼ = F`.) Given that, this file shows
`n₀ + (h × A) ⊆ (h+g) × A`, hence `Δ((h+g) × A) ≤ Δ(h × A)` — the one-step inequality of Theorem 9,
with `h₁ = h + g = 2h + 1 − |F|` (so `0 ≤ |F| ≤ h−1` yields the paper's `h+2 ≤ h₁ ≤ 2h+1`).

The mechanism: any `m ∈ h × A` is a sum over an `h`-set `S ⊆ A`; among the `h + 1` pairwise-disjoint
summand-sets at most `h` can meet `S`, so one is disjoint from `S` (pigeonhole), and gluing it to `S`
gives an `(h+g)`-set summing to `n₀ + m`.
-/

namespace LeanGallery.Combinatorics.Erdos880

open Finset

/-- **Disjoint pigeonhole.** Among `N` pairwise-disjoint finsets, at most `|S|` of them can meet a
fixed finset `S`; so if `|S| < N`, at least one is disjoint from `S`. (Proof: a transversal of the
meeting sets injects into `S`.) -/
lemma exists_disjoint_of_card_lt {α : Type*} [DecidableEq α] {N : ℕ} (R : Fin N → Finset α)
    (hRdisj : ∀ i j, i ≠ j → Disjoint (R i) (R j)) (S : Finset α) (hS : S.card < N) :
    ∃ i, Disjoint (R i) S := by
  by_contra hcon
  push Not at hcon
  choose g hg using fun i => not_disjoint_iff_nonempty_inter.mp (hcon i)
  -- `g i ∈ R i ∩ S`; the transversal `g` is injective because the `R i` are pairwise disjoint
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hi : g i ∈ R i := (mem_inter.mp (hg i)).1
    have hj : g j ∈ R j := (mem_inter.mp (hg j)).1
    rw [hij] at hi
    exact (disjoint_left.mp (hRdisj i j hne) hi) hj
  have hSg : (Finset.univ.image g) ⊆ S := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact (mem_inter.mp (hg i)).2
  have hNle : N ≤ S.card := by
    have h := Finset.card_le_card hSg
    rwa [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- **Theorem 9 structural core (set inclusion).** If `n₀` has `h + 1` representations as sums of `g`
pairwise-distinct elements of `A` whose summand-sets `R i` are pairwise disjoint, then translating the
`h`-fold restricted sumset by `n₀` lands inside the `(h+g)`-fold one: `n₀ + (h × A) ⊆ (h+g) × A`. -/
lemma translate_restrictedSumset_subset {A : Set ℕ} {h g n₀ : ℕ} (R : Fin (h + 1) → Finset ℕ)
    (hRA : ∀ i, ↑(R i) ⊆ A) (hRcard : ∀ i, (R i).card = g) (hRsum : ∀ i, ∑ a ∈ R i, a = n₀)
    (hRdisj : ∀ i j, i ≠ j → Disjoint (R i) (R j)) :
    (fun x => x + n₀) '' restrictedSumset A h ⊆ restrictedSumset A (h + g) := by
  rintro y ⟨m, ⟨S, hSA, hScard, hSsum⟩, rfl⟩
  -- the `h+1` disjoint summand-sets, against the `h`-set `S`, leave one disjoint from `S`
  obtain ⟨i, hi⟩ := exists_disjoint_of_card_lt R hRdisj S (by omega)
  refine ⟨R i ∪ S, ?_, ?_, ?_⟩
  · rw [Finset.coe_union]; exact Set.union_subset (hRA i) hSA
  · rw [Finset.card_union_of_disjoint hi, hRcard i, hScard]; omega
  · show ∑ a ∈ R i ∪ S, a = m + n₀
    rw [Finset.sum_union hi, hRsum i, hSsum]; omega

/-- **Theorem 9, one-step inequality.** Under the same disjoint-representation hypothesis (with `h ≥ 1`
and `A` infinite so the sumsets are infinite), `Δ((h+g) × A) ≤ Δ(h × A)`. This is the inequality
`Δ(hⱼ₊₁ × A) ≤ Δ(hⱼ × A)` of HHP07 Theorem 9, the configuration being supplied by the Erdős–Rado
sunflower lemma plus the density estimate (both still to be formalized). -/
theorem Delta_restrictedSumset_le_of_disjoint_reps {A : Set ℕ} {h g n₀ : ℕ}
    (hA : A.Infinite) (hh : 1 ≤ h) (R : Fin (h + 1) → Finset ℕ)
    (hRA : ∀ i, ↑(R i) ⊆ A) (hRcard : ∀ i, (R i).card = g) (hRsum : ∀ i, ∑ a ∈ R i, a = n₀)
    (hRdisj : ∀ i j, i ≠ j → Disjoint (R i) (R j)) :
    Delta (restrictedSumset A (h + g)) ≤ Delta (restrictedSumset A h) := by
  have hsub := translate_restrictedSumset_subset R hRA hRcard hRsum hRdisj
  have hinj : Function.Injective (fun x : ℕ => x + n₀) := fun a b hab => Nat.add_right_cancel hab
  have hinf : ((fun x => x + n₀) '' restrictedSumset A h).Infinite :=
    (Set.infinite_image_iff hinj.injOn).mpr (restrictedSumset_infinite hh hA)
  calc Delta (restrictedSumset A (h + g))
      ≤ Delta ((fun x => x + n₀) '' restrictedSumset A h) := Delta_anti hsub hinf
    _ = Delta (restrictedSumset A h) := Delta_image_add n₀

/-! ### Sunflower → disjoint representations

The bridge from a *sunflower* (the output of the Erdős–Rado lemma, Aristotle job `c9a76ac5`) to the
disjoint-representation hypothesis of `Delta_restrictedSumset_le_of_disjoint_reps`. A sunflower is a
family `E : Fin (h+1) → Finset ℕ` of `r`-element subsets of `A`, all summing to the same `n`, with a
common pairwise intersection `F` (the *core*). Its *petals* `E i ∖ F` are then pairwise disjoint
`(r−|F|)`-sets all summing to `n − ∑F`, exactly the configuration Theorem 9 needs. -/

/-- **Sunflower step of HHP07 Theorem 9.** If `E : Fin (h+1) → Finset ℕ` is a sunflower with core `F`
— each `E i ⊆ A` of card `r`, all summing to `n`, pairwise intersections all equal to `F` — then
`Δ((h + (r − |F|)) × A) ≤ Δ(h × A)`. (The petals `E i ∖ F` supply the disjoint representations of
`n₀ = n − ∑F`.) Combined with the Erdős–Rado lemma `r = h+1, k = h+1`, this is the engine of the
monotone subsequence in Theorem 9. -/
theorem Delta_restrictedSumset_le_of_sunflower {A : Set ℕ} {h r n : ℕ} {F : Finset ℕ}
    (hA : A.Infinite) (hh : 1 ≤ h) (E : Fin (h + 1) → Finset ℕ)
    (hEA : ∀ i, ↑(E i) ⊆ A) (hEcard : ∀ i, (E i).card = r) (hEsum : ∀ i, ∑ a ∈ E i, a = n)
    (hsun : ∀ i j, i ≠ j → E i ∩ E j = F) :
    Delta (restrictedSumset A (h + (r - F.card))) ≤ Delta (restrictedSumset A h) := by
  -- the core sits inside every petal (use a second index `j ≠ i`, available since `h + 1 ≥ 2`)
  have hFsub : ∀ i : Fin (h + 1), F ⊆ E i := by
    intro i
    obtain ⟨a, -, b, -, hab⟩ := Finset.one_lt_card.mp
      (show 1 < (Finset.univ : Finset (Fin (h + 1))).card by
        rw [Finset.card_univ, Fintype.card_fin]; omega)
    obtain ⟨j, hji⟩ : ∃ j, j ≠ i := by
      rcases eq_or_ne a i with rfl | hai
      · exact ⟨b, fun hbi => hab hbi.symm⟩
      · exact ⟨a, hai⟩
    rw [← hsun j i hji]; exact Finset.inter_subset_right
  have hRA : ∀ i, ↑(E i \ F) ⊆ A := by
    intro i x hx
    rw [Finset.coe_sdiff, Set.mem_sdiff] at hx
    exact hEA i hx.1
  have hRcard : ∀ i, (E i \ F).card = r - F.card := by
    intro i
    have hcd := Finset.card_sdiff_add_card_eq_card (hFsub i)
    rw [hEcard i] at hcd; omega
  have hRsum : ∀ i, ∑ a ∈ E i \ F, a = n - ∑ a ∈ F, a := by
    intro i
    have hsd : ∑ a ∈ E i \ F, a + ∑ a ∈ F, a = ∑ a ∈ E i, a := Finset.sum_sdiff (hFsub i)
    rw [hEsum i] at hsd; omega
  have hRdisj : ∀ (i j : Fin (h + 1)), i ≠ j → Disjoint (E i \ F : Finset ℕ) (E j \ F) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro a ha haj
    rw [Finset.mem_sdiff] at ha haj
    have hin : a ∈ E i ∩ E j := Finset.mem_inter.mpr ⟨ha.1, haj.1⟩
    rw [hsun i j hij] at hin
    exact ha.2 hin
  exact Delta_restrictedSumset_le_of_disjoint_reps hA hh (fun i => E i \ F) hRA hRcard hRsum hRdisj

/-- **HHP07 Theorem 9, consuming a sunflower in `IsSunflower` form.** If `𝓖` is a family of `h + 1`
subsets of `A`, each of card `r` and sum `n`, forming a sunflower with core `Y`, then
`Δ((h + (r − |Y|)) × A) ≤ Δ(h × A)`. This is the exact shape produced by the Erdős–Rado lemma
(`∃ 𝓖 ⊆ 𝓕, ∃ Y, 𝓖.card = h+1 ∧ IsSunflower 𝓖 Y`), so it plugs Aristotle's `sunflower_exists` straight
into the Theorem 9 engine. -/
theorem Delta_restrictedSumset_le_of_isSunflower {A : Set ℕ} {h r n : ℕ} {Y : Finset ℕ}
    {𝓖 : Finset (Finset ℕ)} (hA : A.Infinite) (hh : 1 ≤ h) (hcard : 𝓖.card = h + 1)
    (hmem : ∀ s ∈ 𝓖, ↑s ⊆ A ∧ s.card = r ∧ ∑ a ∈ s, a = n) (hsun : IsSunflower 𝓖 Y) :
    Delta (restrictedSumset A (h + (r - Y.card))) ≤ Delta (restrictedSumset A h) := by
  -- enumerate the `h+1` petals as `E : Fin (h+1) → Finset ℕ`
  have hcard' : Fintype.card ↥𝓖 = h + 1 := by rw [Fintype.card_coe]; exact hcard
  set e := (Fintype.equivFinOfCardEq hcard').symm with he
  set E : Fin (h + 1) → Finset ℕ := fun i => (e i).val with hE
  have hEmem : ∀ i, E i ∈ 𝓖 := fun i => (e i).property
  have hEne : ∀ i j : Fin (h + 1), i ≠ j → E i ≠ E j := by
    intro i j hij hEij
    exact hij (e.injective (Subtype.ext hEij))
  refine Delta_restrictedSumset_le_of_sunflower hA hh E (fun i => (hmem _ (hEmem i)).1)
    (fun i => (hmem _ (hEmem i)).2.1) (fun i => (hmem _ (hEmem i)).2.2) ?_
  intro i j hij
  exact hsun (E i) (hEmem i) (E j) (hEmem j) (hEne i j hij)

/-! ### Toward producing the sunflower: the equal-sum subfamily

The Erdős–Rado lemma needs `> r! q^{r+1}` sets, all `(h+1)`-subsets of `A ∩ [1,x]` summing to one
common value `n`. This subsection supplies the pigeonhole producing such an equal-sum subfamily from a
sufficiently large supply of `(h+1)`-subsets (the supply count `binom(|S|, h+1)` is where the density
estimate `A(x) ≫ x^{1/h}` enters — still to be formalized). -/

/-- **Equal-sum pigeonhole.** Among a family `𝒮` of finsets each with sum `< bound`, if
`bound * K < |𝒮|`, then some value `n` is the common sum of more than `K` of them. -/
lemma exists_many_equal_sum {𝒮 : Finset (Finset ℕ)} {bound K : ℕ}
    (hbound : ∀ s ∈ 𝒮, ∑ a ∈ s, a < bound) (hK : bound * K < 𝒮.card) :
    ∃ n, K < (𝒮.filter (fun s => ∑ a ∈ s, a = n)).card := by
  obtain ⟨n, -, hn⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := 𝒮) (t := Finset.range bound) (f := fun s => ∑ a ∈ s, a)
    (fun s hs => Finset.mem_range.mpr (hbound s hs)) (by rwa [Finset.card_range])
  exact ⟨n, hn⟩

/-- **Counting + equal-sum pigeonhole.** If every element of a finset `S` is `< bnd`, then among the
`binom(|S|, h+1)` many `(h+1)`-subsets of `S`, provided `(h+1) * bnd * K < binom(|S|, h+1)`, some
value `n` is the common sum of more than `K` of them: there is a subfamily of `S.powersetCard (h+1)`,
of size `> K`, all summing to `n`. Together with the (still-to-formalize) density estimate this
furnishes the `> r! q^{r+1}` equal-sum `(h+1)`-subsets fed to the Erdős–Rado lemma. -/
lemma exists_many_equal_sum_subsets {S : Finset ℕ} {h bnd K : ℕ}
    (hbnd : ∀ a ∈ S, a < bnd) (hK : (h + 1) * bnd * K < (S.card).choose (h + 1)) :
    ∃ n, K < ((S.powersetCard (h + 1)).filter (fun T => ∑ a ∈ T, a = n)).card := by
  apply exists_many_equal_sum (bound := (h + 1) * bnd)
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTS, hTcard⟩ := hT
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hlt : ∑ a ∈ T, a < ∑ _a ∈ T, bnd :=
      Finset.sum_lt_sum_of_nonempty hTne (fun a ha => hbnd a (hTS ha))
    rwa [Finset.sum_const, hTcard, smul_eq_mul] at hlt
  · rwa [Finset.card_powersetCard]

/-! ### Theorem 9, one step — reduced to the density estimate

Combining the Erdős–Rado lemma (`sunflower_exists`), the sunflower bridge, and the equal-sum
pigeonhole, the entire one-step inequality of Theorem 9 follows from a single remaining input: a finset
`S ⊆ A` (think `A ∩ [1,x]`) large enough that `> (h+1)!·(h+1)^{h+1}` of its `(h+1)`-subsets share a
common sum. That supply count is exactly what the density estimate `A(x) ≫ x^{1/h}` (still to be
formalized) provides. The result is the genuine Theorem 9 step `Δ(h'×A) ≤ Δ(h×A)` with `h < h' ≤ 2h+1`. -/

/-- **HHP07 Theorem 9, one step, reduced to a large equal-sum subfamily.** Let `A` be infinite, `h ≥ 1`,
and `S ⊆ A` a finset. If more than `(h+1)!·(h+1)^{h+1}` of the `(h+1)`-subsets of `S` share a common
sum `n`, then there is a fold `h'` with `h < h' ≤ 2h+1` and `Δ(h'×A) ≤ Δ(h×A)`. (The Erdős–Rado lemma
extracts an `(h+1)`-petal sunflower from the equal-sum family; its core `Y` has `|Y| ≤ h` because two
distinct equal-sum `(h+1)`-sets cannot share all `h+1` elements, giving `h' = 2h+1−|Y| > h`.) The only
missing input for full Theorem 9 is the density estimate furnishing such an `S`, `n`. -/
theorem exists_fold_Delta_le_of_equal_sum_family {A : Set ℕ} {h n : ℕ} {S : Finset ℕ}
    (hA : A.Infinite) (hh : 1 ≤ h) (hSA : ↑S ⊆ A)
    {𝓕 : Finset (Finset ℕ)} (h𝓕sub : 𝓕 ⊆ S.powersetCard (h + 1))
    (h𝓕sum : ∀ T ∈ 𝓕, ∑ a ∈ T, a = n)
    (h𝓕card : Nat.factorial (h + 1) * (h + 1) ^ (h + 1) < 𝓕.card) :
    ∃ h', h < h' ∧ h' ≤ 2 * h + 1 ∧ Delta (restrictedSumset A h') ≤ Delta (restrictedSumset A h) := by
  -- Erdős–Rado with `r = k = h+1`
  obtain ⟨𝓖, h𝓖sub, Y, h𝓖card, h𝓖sun⟩ := sunflower_exists (h + 1) (h + 1) (by omega) 𝓕
    (fun s hs => le_of_eq (Finset.mem_powersetCard.mp (h𝓕sub hs)).2) h𝓕card
  -- every petal is an `(h+1)`-subset of `A` summing to `n`
  have hmem : ∀ s ∈ 𝓖, ↑s ⊆ A ∧ s.card = h + 1 ∧ ∑ a ∈ s, a = n := by
    intro s hs
    have hs𝓕 : s ∈ 𝓕 := h𝓖sub hs
    have hps := Finset.mem_powersetCard.mp (h𝓕sub hs𝓕)
    refine ⟨fun x hx => hSA (Finset.mem_coe.mpr (hps.1 (Finset.mem_coe.mp hx))), hps.2,
      h𝓕sum s hs𝓕⟩
  -- the core is properly contained in any petal, so `|Y| ≤ h`
  have hYcard : Y.card ≤ h := by
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp (by rw [h𝓖card]; omega)
    by_contra hcon
    push Not at hcon
    have hYs : Y ⊆ s := (h𝓖sun s hs t ht hst) ▸ Finset.inter_subset_left
    have hYt : Y ⊆ t := (h𝓖sun t ht s hs (Ne.symm hst)) ▸ Finset.inter_subset_left
    have hYeqs : Y = s := Finset.eq_of_subset_of_card_le hYs (by rw [(hmem s hs).2.1]; omega)
    have hYeqt : Y = t := Finset.eq_of_subset_of_card_le hYt (by rw [(hmem t ht).2.1]; omega)
    exact hst (hYeqs.symm.trans hYeqt)
  have hstep := Delta_restrictedSumset_le_of_isSunflower hA hh h𝓖card hmem h𝓖sun
  exact ⟨h + ((h + 1) - Y.card), by omega, by omega, hstep⟩

/-! ### Theorem 8: the monotone subsequence, from the one-step inequality

Given the per-step inequality of Theorem 9 (`∀ h ≥ h₀ with `Δ(h×A)` finite, some `h' > h` has
`Δ(h'×A) ≤ Δ(h×A)`), Theorem 8's increasing sequence `(hⱼ)` with `Δ(hⱼ×A)` non-increasing is built by
iteration (finiteness is preserved since `Δ(h'×A) ≤ Δ(h×A) < ⊤`). This isolates the full Theorem 8 as
`thm8_iteration ∘ (per-step)`, the per-step being `exists_fold_Delta_le_of_equal_sum_family` modulo the
density estimate. -/

/-- **HHP07 Theorem 8, reduced to the one-step inequality.** If `Δ(h₀×A)` is finite and every fold
`h ≥ h₀` with finite `Δ` admits a strictly larger fold `h'` with `Δ(h'×A) ≤ Δ(h×A)`, then there is a
*strictly increasing* sequence `(seq j)` starting at `h₀` along which `Δ(seq j × A)` is non-increasing —
exactly the conclusion of Theorem 8. -/
theorem thm8_iteration {A : Set ℕ} {h₀ : ℕ}
    (h₀fin : Delta (restrictedSumset A h₀) < ⊤)
    (step : ∀ h, h₀ ≤ h → Delta (restrictedSumset A h) < ⊤ →
      ∃ h', h < h' ∧ Delta (restrictedSumset A h') ≤ Delta (restrictedSumset A h)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ seq 0 = h₀ ∧
      ∀ j, Delta (restrictedSumset A (seq (j + 1))) ≤ Delta (restrictedSumset A (seq j)) := by
  classical
  -- carry the invariant `h₀ ≤ h ∧ Δ(h×A) < ⊤` along the recursion
  let T := {h : ℕ // h₀ ≤ h ∧ Delta (restrictedSumset A h) < ⊤}
  let next : T → T := fun p =>
    ⟨(step p.1 p.2.1 p.2.2).choose,
      le_of_lt (lt_of_le_of_lt p.2.1 (step p.1 p.2.1 p.2.2).choose_spec.1),
      lt_of_le_of_lt (step p.1 p.2.1 p.2.2).choose_spec.2 p.2.2⟩
  let f : ℕ → T := fun j => Nat.rec (⟨h₀, le_refl _, h₀fin⟩ : T) (fun _ p => next p) j
  refine ⟨fun j => (f j).1, strictMono_nat_of_lt_succ (fun j => ?_), rfl, fun j => ?_⟩
  · show (f j).1 < (step (f j).1 (f j).2.1 (f j).2.2).choose
    exact (step (f j).1 (f j).2.1 (f j).2.2).choose_spec.1
  · show Delta (restrictedSumset A (step (f j).1 (f j).2.1 (f j).2.2).choose) ≤ _
    exact (step (f j).1 (f j).2.1 (f j).2.2).choose_spec.2

/-! ### Density estimate, piece D1: the syndetic counting lower bound

`Δ(h×A) = d < ∞` makes `h×A` syndetic (gaps eventually `≤ d`), so its counting function grows at least
linearly. This lower bound, combined with the counting upper bound D2 (`|h×A∩[1,x]| ≤ binom(A(x),h)`,
Aristotle `38d8fe02`) and a growth step D3, yields the density estimate that furnishes the equal-sum
`(h+1)`-subset family for `exists_fold_Delta_le_of_equal_sum_family`. -/

/-- **Syndetic counting lower bound (D1).** If `X` is infinite with eventual gaps `≤ d` (`d ≥ 1`), then
from a starting point `p₀ ∈ X` the count of `X` below `x` grows linearly: whenever `p₀ + k·d ≤ x`,
there are at least `k + 1` points of `X` in `[0, x]`. (Iterating the `EvGapLe` successor `k` times stays
`≤ p₀ + k·d ≤ x`, producing `k + 1` distinct points.) -/
lemma evGapLe_count_lower {X : Set ℕ} {d : ℕ} (_hd : 1 ≤ d) (hX : X.Infinite) (h : EvGapLe X d) :
    ∃ p₀ ∈ X, ∀ k x, p₀ + k * d ≤ x → k + 1 ≤ (X ∩ Set.Iic x).ncard := by
  classical
  obtain ⟨N, hN⟩ := h
  obtain ⟨p₀, hp₀X, hp₀N⟩ := hX.exists_gt N
  -- iterate the successor, carrying membership in `X` and the threshold `N ≤ ·`
  let Q := {y : ℕ // y ∈ X ∧ N ≤ y}
  let step : Q → Q := fun q =>
    ⟨(hN q.1 q.2.1 q.2.2).choose, (hN q.1 q.2.1 q.2.2).choose_spec.1,
      le_trans q.2.2 (le_of_lt (hN q.1 q.2.1 q.2.2).choose_spec.2.1)⟩
  let p : ℕ → Q := fun k => Nat.rec (⟨p₀, hp₀X, le_of_lt hp₀N⟩ : Q) (fun _ q => step q) k
  let seq : ℕ → ℕ := fun k => (p k).1
  have hseqX : ∀ k, seq k ∈ X := fun k => (p k).2.1
  have hseqlt : ∀ k, seq k < seq (k + 1) := fun k =>
    (hN (p k).1 (p k).2.1 (p k).2.2).choose_spec.2.1
  have hseqmono : StrictMono seq := strictMono_nat_of_lt_succ hseqlt
  have hseqbound : ∀ k, seq k ≤ p₀ + k * d := by
    intro k
    induction k with
    | zero => show p₀ ≤ p₀ + 0 * d; omega
    | succ k ih =>
      have hstep : seq (k + 1) ≤ seq k + d := (hN (p k).1 (p k).2.1 (p k).2.2).choose_spec.2.2
      calc seq (k + 1) ≤ seq k + d := hstep
        _ ≤ p₀ + k * d + d := by omega
        _ = p₀ + (k + 1) * d := by ring
  refine ⟨p₀, hp₀X, fun k x hx => ?_⟩
  have hsubset : ↑((Finset.range (k + 1)).image seq) ⊆ X ∩ Set.Iic x := by
    intro y hy
    rw [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.coe_range, Set.mem_Iio] at hi
    refine ⟨hseqX i, Set.mem_Iic.mpr ?_⟩
    have hik : i ≤ k := by omega
    calc seq i ≤ p₀ + i * d := hseqbound i
      _ ≤ p₀ + k * d := by have := mul_le_mul_left hik d; omega
      _ ≤ x := hx
  have hcard : ((Finset.range (k + 1)).image seq).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hseqmono.injective, Finset.card_range]
  have hfin : (X ∩ Set.Iic x).Finite := (Set.finite_Iic x).subset Set.inter_subset_right
  calc k + 1 = ((Finset.range (k + 1)).image seq).card := hcard.symm
    _ = (↑((Finset.range (k + 1)).image seq) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (X ∩ Set.Iic x).ncard := Set.ncard_le_ncard hsubset hfin

/-- **Counting upper bound (D2).** The number of restricted `h`-sums that are `≤ x` is at most
`binom(A(x), h)`, where `A(x) = |A ∩ [0,x]|`: every such sum is `∑ T` for an `h`-subset `T ⊆ A`, and
each element of `T` is `≤ ∑ T ≤ x` (automatic in ℕ), so `T ⊆ A ∩ [0,x]` and the sum-value lies in the
image of `(A ∩ [0,x]).powersetCard h` under summation, whose image has card `≤ binom(A(x), h)`. -/
lemma restrictedSumset_count_le {A : Set ℕ} (h x : ℕ) :
    (restrictedSumset A h ∩ Set.Iic x).ncard ≤ ((A ∩ Set.Iic x).ncard).choose h := by
  classical
  have hAfin : (A ∩ Set.Iic x).Finite := (Set.finite_Iic x).subset Set.inter_subset_right
  set Afin := hAfin.toFinset with hAfindef
  set img := (Afin.powersetCard h).image (fun T => ∑ a ∈ T, a) with himg
  have hsub : restrictedSumset A h ∩ Set.Iic x ⊆ ↑img := by
    rintro m ⟨⟨T, hTA, hTcard, hTsum⟩, hmx⟩
    rw [Set.mem_Iic] at hmx
    rw [himg, Finset.coe_image, Set.mem_image]
    refine ⟨T, ?_, hTsum⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨fun a haT => ?_, hTcard⟩
    rw [hAfindef, Set.Finite.mem_toFinset]
    refine ⟨hTA (Finset.mem_coe.mpr haT), Set.mem_Iic.mpr ?_⟩
    calc a ≤ ∑ b ∈ T, b := Finset.single_le_sum (fun i _ => Nat.zero_le i) haT
      _ = m := hTsum
      _ ≤ x := hmx
  have hcard_eq : Afin.card = (A ∩ Set.Iic x).ncard := by
    rw [hAfindef]; exact (Set.ncard_eq_toFinset_card _ hAfin).symm
  calc (restrictedSumset A h ∩ Set.Iic x).ncard
      ≤ (↑img : Set ℕ).ncard := Set.ncard_le_ncard hsub img.finite_toSet
    _ = img.card := Set.ncard_coe_finset _
    _ ≤ (Afin.powersetCard h).card := Finset.card_image_le
    _ = (Afin.card).choose h := Finset.card_powersetCard _ _
    _ = ((A ∩ Set.Iic x).ncard).choose h := by rw [hcard_eq]

/-! ### Assembling the density estimate into the Theorem 9 one step

D1 (`evGapLe_count_lower`) + D2 (`restrictedSumset_count_le`) give the counting bound `H1`; feeding it
to the growth step D3 (`hgrowth`, the content of Aristotle leaf `ad7dd3f4` / `aristotle/density`)
yields a finset `S = A ∩ [0,x]` with `> (h+1)!·(h+1)^{h+1}` of its `(h+1)`-subsets sharing a sum, which
the capstone turns into the Theorem 9 one step. The whole HHP07 Theorem 8/9 then follows by
`thm8_iteration`, with `hgrowth` (pure ℕ-arithmetic) the single remaining input. -/

/-- **HHP07 Theorem 9, one step — assembled from the density bounds.** For infinite positive `A` and
`h ≥ 1` with `Δ(h×A)` finite, *given* the growth fact `hgrowth` (D3: the counting bound `H1` forces
`binom(A(x),h+1)` past the linear threshold `(h+1)(x+1)·(h+1)!(h+1)^{h+1}` for some `x`), there is a
fold `h'` with `h < h' ≤ 2h+1` and `Δ(h'×A) ≤ Δ(h×A)`. (`hgrowth` is `density_growth` of
`aristotle/density`, pure ℕ-arithmetic — the only piece not yet machine-checked locally.) -/
theorem exists_fold_Delta_le_of_density_growth {A : Set ℕ} {h : ℕ}
    (hA : A.Infinite) (_hpos : ∀ a ∈ A, 0 < a) (hh : 1 ≤ h)
    (hfin : Delta (restrictedSumset A h) < ⊤)
    (hgrowth : ∀ (d p₀ : ℕ), 1 ≤ d →
      (∀ x k, p₀ + k * d ≤ x → k + 1 ≤ ((A ∩ Set.Iic x).ncard).choose h) →
      ∃ x, (h + 1) * (x + 1) * (Nat.factorial (h + 1) * (h + 1) ^ (h + 1))
        < ((A ∩ Set.Iic x).ncard).choose (h + 1)) :
    ∃ h', h < h' ∧ h' ≤ 2 * h + 1 ∧ Delta (restrictedSumset A h') ≤ Delta (restrictedSumset A h) := by
  classical
  -- a gap bound `d₁ ≥ 1` for `h × A`
  obtain ⟨d, hd⟩ := (Delta_lt_top_iff _).mp hfin
  have hd₁ : EvGapLe (restrictedSumset A h) (d + 1) := hd.mono (Nat.le_succ d)
  -- D1: linear count lower bound from a starting point `p₀`
  obtain ⟨p₀, -, hcount⟩ := evGapLe_count_lower (Nat.le_add_left 1 d)
    (restrictedSumset_infinite hh hA) hd₁
  -- D1 + D2 ⟹ the counting hypothesis `H1`
  have H1 : ∀ x k, p₀ + k * (d + 1) ≤ x → k + 1 ≤ ((A ∩ Set.Iic x).ncard).choose h :=
    fun x k hx => le_trans (hcount k x hx) (restrictedSumset_count_le h x)
  -- D3: the growth step furnishes a large `x`
  obtain ⟨x, hx⟩ := hgrowth (d + 1) p₀ (Nat.le_add_left 1 d) H1
  -- equal-sum subfamily of `(h+1)`-subsets of `S = A ∩ [0,x]`
  have hAfin : (A ∩ Set.Iic x).Finite := (Set.finite_Iic x).subset Set.inter_subset_right
  set S := hAfin.toFinset with hSdef
  have hScard : S.card = (A ∩ Set.Iic x).ncard := by
    rw [hSdef]; exact (Set.ncard_eq_toFinset_card _ hAfin).symm
  have hbnd : ∀ a ∈ S, a < x + 1 := by
    intro a ha
    rw [hSdef, Set.Finite.mem_toFinset] at ha
    have := ha.2; rw [Set.mem_Iic] at this; omega
  have hK : (h + 1) * (x + 1) * (Nat.factorial (h + 1) * (h + 1) ^ (h + 1)) < (S.card).choose (h + 1) := by
    rw [hScard]; exact hx
  obtain ⟨n, hn⟩ := exists_many_equal_sum_subsets (h := h) hbnd hK
  -- feed the equal-sum family to the capstone
  have hSA : ↑S ⊆ A := by
    rw [hSdef, Set.Finite.coe_toFinset]; exact Set.inter_subset_left
  refine exists_fold_Delta_le_of_equal_sum_family hA hh hSA
    (Finset.filter_subset _ _) (fun T hT => (Finset.mem_filter.mp hT).2) hn

/-- **HHP07 Theorem 8, conditional on the density growth step.** For infinite positive `A` with
`Δ(h₀×A)` finite, *given* the ℕ-arithmetic growth fact for every fold (the content of
`aristotle/density`), there is a strictly increasing sequence from `h₀` along which `Δ(·×A)` is
non-increasing — the full conclusion of HHP07 Theorem 8. The sole hypothesis `hgrowth` is
`density_growth` (pure ℕ-arithmetic, Aristotle `ad7dd3f4`); discharging it makes Theorem 8
unconditional and kernel-pure. -/
theorem thm8_of_density_growth {A : Set ℕ} {h₀ : ℕ}
    (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) (hh₀ : 1 ≤ h₀)
    (hfin : Delta (restrictedSumset A h₀) < ⊤)
    (hgrowth : ∀ (h : ℕ), 1 ≤ h → ∀ (d p₀ : ℕ), 1 ≤ d →
      (∀ x k, p₀ + k * d ≤ x → k + 1 ≤ ((A ∩ Set.Iic x).ncard).choose h) →
      ∃ x, (h + 1) * (x + 1) * (Nat.factorial (h + 1) * (h + 1) ^ (h + 1))
        < ((A ∩ Set.Iic x).ncard).choose (h + 1)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ seq 0 = h₀ ∧
      ∀ j, Delta (restrictedSumset A (seq (j + 1))) ≤ Delta (restrictedSumset A (seq j)) := by
  refine thm8_iteration hfin (fun h hh₀h hhfin => ?_)
  obtain ⟨h', hlt, _, hle⟩ := exists_fold_Delta_le_of_density_growth hA hpos
    (le_trans hh₀ hh₀h) hhfin (hgrowth h (le_trans hh₀ hh₀h))
  exact ⟨h', hlt, hle⟩

/-! ### The growth step D3, proved (pure ℕ-arithmetic)

The single remaining input `density_growth` — proved here directly, dodging real powers via
`f x ≤ T ⟹ x ≤ p₀ + d·T^h` (a *constant* power `T^h`). With it, HHP07 Theorem 8 is unconditional. -/

/-- **Growth step D3.** If `f` (think `A(x) = |A∩[0,x]|`) satisfies `k + 1 ≤ binom(f x, h)` whenever
`p₀ + k·d ≤ x` (the combined counting bounds D1+D2), then for some `x` the count of `(h+1)`-subsets
`binom(f x, h+1)` exceeds the linear threshold `(h+1)·(x+1)·K`. Pure ℕ-arithmetic via
`Nat.choose_succ_right_eq` and `Nat.choose_le_pow`, with the constants `C = 2d(h+1)²K+1`, `T = C+h`,
`x = p₀ + d·T^h + 2p₀ + 2`. -/
theorem density_growth (h d K p₀ : ℕ) (hh : 1 ≤ h) (hd : 1 ≤ d) (hK : 1 ≤ K) (f : ℕ → ℕ)
    (H1 : ∀ x k, p₀ + k * d ≤ x → k + 1 ≤ (f x).choose h) :
    ∃ x, (h + 1) * (x + 1) * K < (f x).choose (h + 1) := by
  set C : ℕ := 2 * d * (h + 1) ^ 2 * K + 1 with hC
  set T : ℕ := C + h with hT
  refine ⟨p₀ + d * T ^ h + 2 * p₀ + 2, ?_⟩
  set x : ℕ := p₀ + d * T ^ h + 2 * p₀ + 2 with hx
  set k : ℕ := (x - p₀) / d with hk
  have hkd : p₀ + k * d ≤ x := by
    have := Nat.div_mul_le_self (x - p₀) d
    rw [← hk] at this; omega
  have hH : k + 1 ≤ (f x).choose h := H1 x k hkd
  have hfT : T ≤ f x := by
    by_contra hlt
    rw [not_le] at hlt
    have hbpow : (f x).choose h ≤ T ^ h :=
      le_trans (Nat.choose_le_pow (f x) h) (Nat.pow_le_pow_left (le_of_lt hlt) h)
    have hk1 : k + 1 ≤ T ^ h := le_trans hH hbpow
    have hkge : T ^ h ≤ k := by
      rw [hk, Nat.le_div_iff_mul_le hd]
      have hDeq : d * T ^ h = T ^ h * d := Nat.mul_comm _ _
      omega
    omega
  have hidentity : (f x).choose (h + 1) * (h + 1) = (f x).choose h * (f x - h) :=
    Nat.choose_succ_right_eq (f x) h
  have hlt_dk1 : x - p₀ < d * (k + 1) := by
    have hmod : d * k + (x - p₀) % d = x - p₀ := by rw [hk]; exact Nat.div_add_mod (x - p₀) d
    have hr : (x - p₀) % d < d := Nat.mod_lt _ hd
    have hexp : d * (k + 1) = d * k + d := by ring
    omega
  have hdB : x - p₀ < d * (f x).choose h := by
    have h1 : d * (k + 1) ≤ d * (f x).choose h := Nat.mul_le_mul_left _ hH
    omega
  have h2P : x + 2 ≤ 2 * (d * (f x).choose h) := by omega
  have hfxh : C ≤ f x - h := by omega
  rw [← Nat.mul_lt_mul_right (show 0 < h + 1 by omega), hidentity]
  have step1 : (f x).choose h * C ≤ (f x).choose h * (f x - h) := Nat.mul_le_mul_left _ hfxh
  have step2 : (f x).choose h * (2 * d * (h + 1) ^ 2 * K) ≤ (f x).choose h * C := by
    apply Nat.mul_le_mul_left; omega
  have step3 : (f x).choose h * (2 * d * (h + 1) ^ 2 * K)
      = (h + 1) ^ 2 * K * (2 * (d * (f x).choose h)) := by ring
  have step4 : (h + 1) ^ 2 * K * (x + 2) ≤ (h + 1) ^ 2 * K * (2 * (d * (f x).choose h)) :=
    Nat.mul_le_mul_left _ h2P
  have hM : 0 < (h + 1) ^ 2 * K := Nat.mul_pos (by positivity) (by omega)
  have step5 : (h + 1) * (x + 1) * K * (h + 1) < (h + 1) ^ 2 * K * (x + 2) := by
    have hLHS : (h + 1) * (x + 1) * K * (h + 1) = (h + 1) ^ 2 * K * (x + 1) := by ring
    rw [hLHS]; exact mul_lt_mul_of_pos_left (by omega) hM
  calc (h + 1) * (x + 1) * K * (h + 1)
      < (h + 1) ^ 2 * K * (x + 2) := step5
    _ ≤ (h + 1) ^ 2 * K * (2 * (d * (f x).choose h)) := step4
    _ = (f x).choose h * (2 * d * (h + 1) ^ 2 * K) := step3.symm
    _ ≤ (f x).choose h * C := step2
    _ ≤ (f x).choose h * (f x - h) := step1

/-- **HHP07 Theorem 8 (unconditional).** For every infinite set `A` of positive integers such that
`Δ(h₀ × A)` is finite for some `h₀ ≥ 1`, there is a strictly increasing sequence `(seq j)` from `h₀`
along which `Δ(seq j × A)` is non-increasing. This is the genuine HHP07 Theorem 8, now fully
machine-checked: the Erdős–Rado sunflower lemma (`Sunflower.lean`) supplies the sunflower, the density
estimate (D1 `evGapLe_count_lower` + D2 `restrictedSumset_count_le` + D3 `density_growth`) supplies the
configuration, and `thm8_iteration` assembles the sequence. -/
theorem erdos_880_thm8 {A : Set ℕ} {h₀ : ℕ}
    (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) (hh₀ : 1 ≤ h₀)
    (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ seq 0 = h₀ ∧
      ∀ j, Delta (restrictedSumset A (seq (j + 1))) ≤ Delta (restrictedSumset A (seq j)) :=
  thm8_of_density_growth hA hpos hh₀ hfin (fun h hh _ p₀ hd H1 =>
    density_growth h _ (Nat.factorial (h + 1) * (h + 1) ^ (h + 1)) p₀ hh hd
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) _ H1)

/-! ### HHP07 Theorem 9, the precise increment bounds

The paper's Theorem 9 sharpens Theorem 8 with `hⱼ + 2 ≤ hⱼ₊₁ ≤ hⱼ + h₀ + 1`. The trick: at the step for
`hⱼ`, use a sunflower of `hⱼ + 1` petals of sets of the *fixed* size `h₀ + 1` (not `hⱼ + 1`). The petal
count `hⱼ + 1` guarantees one avoids the `hⱼ`-set; the fixed object size `h₀ + 1` caps the increment at
`h₀ + 1`. The core's `|Y| ≤ h₀ - 1` (two distinct equal-sum `(h₀+1)`-sets can't share `h₀` elements)
forces the increment `≥ 2`. The supply of fixed-size subsets comes from the density for `h₀`. -/

/-- **HHP07 Theorem 9, precise one step.** With object size fixed at `h₀ + 1`: given a large equal-sum
family of `(h₀+1)`-subsets of `S ⊆ A` (`(h₀+1)!·(h+1)^{h₀+1} < |𝓕|`), there is a fold `h'` with
`h + 2 ≤ h' ≤ h + h₀ + 1` and `Δ(h'×A) ≤ Δ(h×A)`. -/
theorem exists_fold_Delta_le_precise {A : Set ℕ} {h₀ h n : ℕ} {S : Finset ℕ}
    (hA : A.Infinite) (hh₀ : 1 ≤ h₀) (hh : 1 ≤ h) (hSA : ↑S ⊆ A)
    {𝓕 : Finset (Finset ℕ)} (h𝓕sub : 𝓕 ⊆ S.powersetCard (h₀ + 1))
    (h𝓕sum : ∀ T ∈ 𝓕, ∑ a ∈ T, a = n)
    (h𝓕card : Nat.factorial (h₀ + 1) * (h + 1) ^ (h₀ + 1) < 𝓕.card) :
    ∃ h', h + 2 ≤ h' ∧ h' ≤ h + h₀ + 1 ∧
      Delta (restrictedSumset A h') ≤ Delta (restrictedSumset A h) := by
  obtain ⟨𝓖, h𝓖sub, Y, h𝓖card, h𝓖sun⟩ := sunflower_exists (h₀ + 1) (h + 1) (by omega) 𝓕
    (fun s hs => le_of_eq (Finset.mem_powersetCard.mp (h𝓕sub hs)).2) h𝓕card
  have hmem : ∀ s ∈ 𝓖, ↑s ⊆ A ∧ s.card = h₀ + 1 ∧ ∑ a ∈ s, a = n := by
    intro s hs
    have hps := Finset.mem_powersetCard.mp (h𝓕sub (h𝓖sub hs))
    exact ⟨fun x hx => hSA (Finset.mem_coe.mpr (hps.1 (Finset.mem_coe.mp hx))), hps.2,
      h𝓕sum s (h𝓖sub hs)⟩
  -- `|Y| ≤ h₀ - 1`: two distinct equal-sum `(h₀+1)`-petals cannot share `h₀` elements
  have hYcard : Y.card ≤ h₀ - 1 := by
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp (by rw [h𝓖card]; omega)
    have hsub_s : Y ⊆ s := (h𝓖sun s hs t ht hst) ▸ Finset.inter_subset_left
    have hsub_t : Y ⊆ t := (h𝓖sun t ht s hs (Ne.symm hst)) ▸ Finset.inter_subset_left
    by_contra hcon
    push Not at hcon
    set c := (h₀ + 1) - Y.card with hc
    have hsY_card : (s \ Y).card = c := by
      have := Finset.card_sdiff_add_card_eq_card hsub_s; rw [(hmem s hs).2.1] at this; omega
    have htY_card : (t \ Y).card = c := by
      have := Finset.card_sdiff_add_card_eq_card hsub_t; rw [(hmem t ht).2.1] at this; omega
    have hc_le : c ≤ 1 := by rw [hc]; omega
    have hne : s \ Y ≠ t \ Y := by
      intro heq
      exact hst (by rw [← Finset.sdiff_union_of_subset hsub_s,
        ← Finset.sdiff_union_of_subset hsub_t, heq])
    have hdisj : Disjoint (s \ Y) (t \ Y) := by
      rw [Finset.disjoint_left]; intro a ha hat
      rw [Finset.mem_sdiff] at ha hat
      have hin : a ∈ s ∩ t := Finset.mem_inter.mpr ⟨ha.1, hat.1⟩
      rw [h𝓖sun s hs t ht hst] at hin; exact ha.2 hin
    have hsumeq : ∑ a ∈ s \ Y, a = ∑ a ∈ t \ Y, a := by
      have hs1 : ∑ a ∈ s \ Y, a + ∑ a ∈ Y, a = ∑ a ∈ s, a := Finset.sum_sdiff hsub_s
      have ht1 : ∑ a ∈ t \ Y, a + ∑ a ∈ Y, a = ∑ a ∈ t, a := Finset.sum_sdiff hsub_t
      rw [(hmem s hs).2.2] at hs1; rw [(hmem t ht).2.2] at ht1; omega
    rcases (show c = 0 ∨ c = 1 by omega) with hc0 | hc1
    · rw [hc0] at hsY_card htY_card
      exact hne (by rw [Finset.card_eq_zero.mp hsY_card, Finset.card_eq_zero.mp htY_card])
    · rw [hc1] at hsY_card htY_card
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsY_card
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp htY_card
      rw [ha, hb, Finset.sum_singleton, Finset.sum_singleton] at hsumeq
      rw [ha, hb, Finset.disjoint_singleton] at hdisj
      exact hdisj hsumeq
  have hstep := Delta_restrictedSumset_le_of_isSunflower hA hh h𝓖card hmem h𝓖sun
  exact ⟨h + ((h₀ + 1) - Y.card), by omega, by omega, hstep⟩

/-- **HHP07 Theorem 9, precise one step, from the density for `h₀`.** For infinite positive `A` with
`Δ(h₀×A)` finite (`h₀ ≥ 1`) and any target `h ≥ 1`, there is `h'` with `h + 2 ≤ h' ≤ h + h₀ + 1` and
`Δ(h'×A) ≤ Δ(h×A)`. The density estimate for `h₀` (D1+D2+D3 with object fold `h₀`, threshold
`(h₀+1)!·(h+1)^{h₀+1}`) furnishes the equal-sum `(h₀+1)`-subset family for `exists_fold_Delta_le_precise`. -/
theorem exists_fold_Delta_le_precise_of_density {A : Set ℕ} {h₀ h : ℕ}
    (hA : A.Infinite) (_hpos : ∀ a ∈ A, 0 < a) (hh₀ : 1 ≤ h₀) (hh : 1 ≤ h)
    (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    ∃ h', h + 2 ≤ h' ∧ h' ≤ h + h₀ + 1 ∧
      Delta (restrictedSumset A h') ≤ Delta (restrictedSumset A h) := by
  classical
  obtain ⟨d, hd⟩ := (Delta_lt_top_iff _).mp hfin
  have hd₁ : EvGapLe (restrictedSumset A h₀) (d + 1) := hd.mono (Nat.le_succ d)
  obtain ⟨p₀, -, hcount⟩ := evGapLe_count_lower (Nat.le_add_left 1 d)
    (restrictedSumset_infinite hh₀ hA) hd₁
  have H1 : ∀ x k, p₀ + k * (d + 1) ≤ x → k + 1 ≤ ((A ∩ Set.Iic x).ncard).choose h₀ :=
    fun x k hx => le_trans (hcount k x hx) (restrictedSumset_count_le h₀ x)
  obtain ⟨x, hx⟩ := density_growth h₀ (d + 1) (Nat.factorial (h₀ + 1) * (h + 1) ^ (h₀ + 1)) p₀
    hh₀ (Nat.le_add_left 1 d) (Nat.one_le_iff_ne_zero.mpr (by positivity))
    (fun x => (A ∩ Set.Iic x).ncard) H1
  have hAfin : (A ∩ Set.Iic x).Finite := (Set.finite_Iic x).subset Set.inter_subset_right
  set S := hAfin.toFinset with hSdef
  have hScard : S.card = (A ∩ Set.Iic x).ncard := by
    rw [hSdef]; exact (Set.ncard_eq_toFinset_card _ hAfin).symm
  have hbnd : ∀ a ∈ S, a < x + 1 := by
    intro a ha
    rw [hSdef, Set.Finite.mem_toFinset] at ha
    have := ha.2; rw [Set.mem_Iic] at this; omega
  have hK : (h₀ + 1) * (x + 1) * (Nat.factorial (h₀ + 1) * (h + 1) ^ (h₀ + 1))
      < (S.card).choose (h₀ + 1) := by rw [hScard]; exact hx
  obtain ⟨n, hn⟩ := exists_many_equal_sum_subsets (h := h₀) hbnd hK
  have hSA : ↑S ⊆ A := by rw [hSdef, Set.Finite.coe_toFinset]; exact Set.inter_subset_left
  exact exists_fold_Delta_le_precise hA hh₀ hh hSA (Finset.filter_subset _ _)
    (fun T hT => (Finset.mem_filter.mp hT).2) hn

/-- **HHP07 Theorem 9 (precise, unconditional).** For every infinite set `A` of positive integers with
`Δ(h₀×A)` finite (`h₀` ≥ 1, e.g. the least such fold), there is a sequence `(seq j)` from `h₀` with
`seq j + 2 ≤ seq (j+1) ≤ seq j + h₀ + 1` and `Δ(seq (j+1) × A) ≤ Δ(seq j × A)` for all `j` — the paper's
precise increment bounds. Strengthens Theorem 8 (`erdos_880_thm8`); fully machine-checked, kernel-pure. -/
theorem erdos_880_thm9 {A : Set ℕ} {h₀ : ℕ}
    (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) (hh₀ : 1 ≤ h₀)
    (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    ∃ seq : ℕ → ℕ, seq 0 = h₀ ∧ ∀ j,
      seq j + 2 ≤ seq (j + 1) ∧ seq (j + 1) ≤ seq j + h₀ + 1 ∧
      Delta (restrictedSumset A (seq (j + 1))) ≤ Delta (restrictedSumset A (seq j)) := by
  classical
  have step : ∀ h, h₀ ≤ h →
      ∃ h', h + 2 ≤ h' ∧ h' ≤ h + h₀ + 1 ∧
        Delta (restrictedSumset A h') ≤ Delta (restrictedSumset A h) :=
    fun h hh₀h => exists_fold_Delta_le_precise_of_density hA hpos hh₀ (le_trans hh₀ hh₀h) hfin
  let T := {h : ℕ // h₀ ≤ h ∧ Delta (restrictedSumset A h) < ⊤}
  let next : T → T := fun p =>
    ⟨(step p.1 p.2.1).choose,
      by have h1 := (step p.1 p.2.1).choose_spec.1; have h2 := p.2.1; omega,
      lt_of_le_of_lt (step p.1 p.2.1).choose_spec.2.2 p.2.2⟩
  let f : ℕ → T := fun j => Nat.rec (⟨h₀, le_refl _, hfin⟩ : T) (fun _ p => next p) j
  refine ⟨fun j => (f j).1, rfl, fun j => ⟨?_, ?_, ?_⟩⟩
  · show (f j).1 + 2 ≤ (step (f j).1 (f j).2.1).choose
    exact (step (f j).1 (f j).2.1).choose_spec.1
  · show (step (f j).1 (f j).2.1).choose ≤ (f j).1 + h₀ + 1
    exact (step (f j).1 (f j).2.1).choose_spec.2.1
  · show Delta (restrictedSumset A (step (f j).1 (f j).2.1).choose) ≤ _
    exact (step (f j).1 (f j).2.1).choose_spec.2.2

end LeanGallery.Combinatorics.Erdos880
