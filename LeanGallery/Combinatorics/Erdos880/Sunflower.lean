/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The Erdős–Rado sunflower lemma

A *sunflower* (Δ-system) with core `Y` is a family of sets whose pairwise intersections all equal `Y`.
The **Erdős–Rado lemma**: any family of more than `r! · k^r` sets, each of cardinality `≤ r`, contains
`k` of them forming a sunflower.

mathlib (as of 2026-06) has **no** sunflower / Erdős–Rado lemma, so it is formalized here. This is the
deep prerequisite for HHP07 Theorems 8/9 (the monotone subsequence `(hⱼ)` with `Δ(hⱼ × A)`
non-increasing); see `Thm9.lean` for the bridge into the `Δ` machinery.

The bound used is `r! · k^r` (a clean, commonly-cited form). The tighter `r! · (k-1)^r` is correct for
*r-uniform* families; for families of sets of size *at most* `r` the standard induction loses one slot
to a possible empty set, so the slightly weaker (still standard) `k^r` constant is used.

Proof: induction on `r`. Base `r = 0`: all sets are `∅`, so `|𝓕| ≤ 1`, contradicting the bound.
Step `r ≥ 1`: take a maximal pairwise-disjoint subfamily `𝓜`. If `|𝓜| ≥ k`, those `k` disjoint sets are
a sunflower with empty core. Otherwise `|𝓜| ≤ k-1`, so `U = ⋃ 𝓜` has `|U| ≤ (k-1)·r`; by maximality
every nonempty set meets `U`, so by pigeonhole some `u ∈ U` lies in `> r!·k^r/(over r)` sets; apply the
induction hypothesis to `{S \ {u}}` and add `u` back to the resulting sunflower.

Harvested from Aristotle leaf `c9a76ac5`, verified in our kernel (`#print axioms` clean:
`[propext, Classical.choice, Quot.sound]`).
-/

namespace LeanGallery.Combinatorics.Erdos880

open Finset

/-- `IsSunflower 𝓖 Y` : every two distinct members of the family `𝓖` meet exactly in the core `Y`. -/
def IsSunflower {α : Type*} [DecidableEq α] (𝓖 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ s ∈ 𝓖, ∀ t ∈ 𝓖, s ≠ t → s ∩ t = Y

/-- A pairwise-disjoint family is a sunflower with empty core. -/
lemma isSunflower_empty_core {α : Type*} [DecidableEq α] (𝓖 : Finset (Finset α))
    (h : ∀ s ∈ 𝓖, ∀ t ∈ 𝓖, s ≠ t → Disjoint s t) : IsSunflower 𝓖 ∅ := by
  exact fun s hs t ht hst => Finset.disjoint_iff_inter_eq_empty.mp ( h s hs t ht hst )

/-- From a pairwise-disjoint subfamily of size `≥ k`, extract a `k`-sunflower (core `∅`). -/
lemma exists_disjoint_sunflower {α : Type*} [DecidableEq α] {𝓕 𝓜 : Finset (Finset α)} {k : ℕ}
    (hsub : 𝓜 ⊆ 𝓕) (hdisj : ∀ s ∈ 𝓜, ∀ t ∈ 𝓜, s ≠ t → Disjoint s t) (hk : k ≤ 𝓜.card) :
    ∃ 𝓖 ⊆ 𝓕, ∃ Y, 𝓖.card = k ∧ IsSunflower 𝓖 Y := by
  obtain ⟨𝓖, hG_sub, hG_card⟩ : ∃ (𝓖 : Finset (Finset α)), 𝓖 ⊆ 𝓜 ∧ #𝓖 = k :=
    le_card_iff_exists_subset_card.mp hk
  exact ⟨ 𝓖, Finset.Subset.trans hG_sub hsub, ∅, hG_card, by exact isSunflower_empty_core _ ( fun s hs t ht hst ↦ hdisj s ( hG_sub hs ) t ( hG_sub ht ) hst ) ⟩

/-- Adding a fresh element `u` back to every set of a sunflower yields a sunflower with core
`insert u Y`, preserving cardinality. -/
lemma isSunflower_insert_image {α : Type*} [DecidableEq α] {𝓖' : Finset (Finset α)} {Y' : Finset α}
    {u : α} (h : IsSunflower 𝓖' Y') (hu : ∀ s ∈ 𝓖', u ∉ s) :
    IsSunflower (𝓖'.image (insert u)) (insert u Y') ∧
      (𝓖'.image (insert u)).card = 𝓖'.card := by
  refine' ⟨ _, Finset.card_image_of_injOn fun s hs t ht hst => _ ⟩;
  · intro s hs t ht hst; obtain ⟨ s', hs', rfl ⟩ := Finset.mem_image.mp hs; obtain ⟨ t', ht', rfl ⟩ := Finset.mem_image.mp ht; simp_all +decide [ Finset.ext_iff, IsSunflower ] ;
    grind +ring;
  · ext x; replace hst := Finset.ext_iff.mp hst x; aesop;

/-- Existence of a maximal pairwise-disjoint subfamily: it is pairwise disjoint and every member of
`𝓕` outside it meets some member of it. -/
lemma exists_maximal_disjoint {α : Type*} [DecidableEq α] (𝓕 : Finset (Finset α)) :
    ∃ 𝓜 ⊆ 𝓕, (∀ s ∈ 𝓜, ∀ t ∈ 𝓜, s ≠ t → Disjoint s t) ∧
      (∀ S ∈ 𝓕, S ∉ 𝓜 → ∃ t ∈ 𝓜, ¬ Disjoint S t) := by
  obtain ⟨𝓜, h𝓜⟩ : ∃ 𝓜 ⊆ 𝓕, (∀ s ∈ 𝓜, ∀ t ∈ 𝓜, s ≠ t → Disjoint s t) ∧ ∀ M ⊆ 𝓕, (∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint s t) → M.card ≤ 𝓜.card := by
    have h_max : ∃ M ∈ Finset.filter (fun M => ∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint s t) (Finset.powerset 𝓕), ∀ N ∈ Finset.filter (fun M => ∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint s t) (Finset.powerset 𝓕), M.card ≥ N.card := by
      exact Finset.exists_max_image _ _ ⟨ ∅, by simp +decide ⟩;
    grind;
  refine' ⟨ 𝓜, h𝓜.1, h𝓜.2.1, fun S hS hS' => _ ⟩;
  contrapose! h𝓜;
  refine' fun h₁ h₂ => ⟨ Insert.insert S 𝓜, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  exact fun t ht hts => Disjoint.symm ( h𝓜 t ht )

/-- Pigeonhole: if every nonempty set of `𝓕` meets `U` and `𝓕` is large enough relative to
`U.card * m`, then some element of `U` lies in more than `m` sets of `𝓕`. -/
lemma exists_heavy_element {α : Type*} [DecidableEq α] (𝓕 : Finset (Finset α)) (U : Finset α)
    (m : ℕ) (hcover : ∀ S ∈ 𝓕, S ≠ ∅ → ¬ Disjoint S U)
    (hbig : U.card * m + 1 < 𝓕.card) :
    ∃ u ∈ U, m < (𝓕.filter (fun S => u ∈ S)).card := by
  contrapose! hbig;
  set D := 𝓕.filter (fun S => Disjoint S U) with hD;
  have hD_card : D.card ≤ 1 := by
    exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => hcover x ( Finset.filter_subset _ _ hx ) ( by aesop ) ( Finset.mem_filter.mp hx |>.2 );
  have h_filter_card : (𝓕.filter (fun S => ¬Disjoint S U)).card ≤ ∑ u ∈ U, (𝓕.filter (fun S => u ∈ S)).card := by
    have h_filter_card : (𝓕.filter (fun S => ¬Disjoint S U)) ⊆ Finset.biUnion U (fun u => 𝓕.filter (fun S => u ∈ S)) := by
      simp +contextual [ Finset.subset_iff, Finset.disjoint_left ];
      grind +extAll
    exact le_trans ( Finset.card_le_card h_filter_card ) ( Finset.card_biUnion_le );
  rw [ show 𝓕 = D ∪ { S ∈ 𝓕 | ¬Disjoint S U } by ext; by_cases h : Disjoint ‹_› U <;> aesop ] ; rw [ Finset.card_union_of_disjoint ( Finset.disjoint_filter_filter_not _ _ _ ) ] ; nlinarith [ show ∑ u ∈ U, # ( { S ∈ 𝓕 | u ∈ S } ) ≤ U.card * m by exact le_trans ( Finset.sum_le_sum hbig ) ( by simp +decide ) ] ;

/-- **The Erdős–Rado sunflower lemma.** Any family `𝓕` of more than `r! · k^r` finsets, each of
cardinality `≤ r`, contains `k` members forming a sunflower (with some core `Y`). -/
theorem sunflower_exists {α : Type*} [DecidableEq α]
    (r k : ℕ) (hk : 1 ≤ k) (𝓕 : Finset (Finset α))
    (hsize : ∀ s ∈ 𝓕, s.card ≤ r)
    (hcard : Nat.factorial r * k ^ r < 𝓕.card) :
    ∃ 𝓖 ⊆ 𝓕, ∃ Y, 𝓖.card = k ∧ IsSunflower 𝓖 Y := by
  induction' r with r ih generalizing k 𝓕;
  · have := Finset.one_lt_card.1 hcard; obtain ⟨ s, hs, t, ht, hst ⟩ := this; have := hsize s hs; have := hsize t ht; aesop;
  · obtain ⟨𝓜, h𝓜sub, hdisj, hmax⟩ := exists_maximal_disjoint 𝓕;
    by_cases h : k ≤ 𝓜.card;
    · exact exists_disjoint_sunflower h𝓜sub hdisj h;
    · obtain ⟨u, huU, hu_count⟩ : ∃ u ∈ 𝓜.biUnion id, r.factorial * k^r < (𝓕.filter (fun S => u ∈ S)).card := by
        apply exists_heavy_element;
        · intro S hS hS' hS''; simp_all +decide [ Finset.disjoint_left ] ;
          exact absurd ( hmax S hS ( by rintro h; exact hS' ( Finset.eq_empty_of_forall_notMem fun x hx => hS'' hx _ h ( by aesop ) ) ) ) ( by tauto );
        · have hUcard : (𝓜.biUnion id).card ≤ (k - 1) * (r + 1) := by
            rw [ Finset.card_biUnion ];
            · exact le_trans ( Finset.sum_le_sum fun x hx => hsize x ( h𝓜sub hx ) ) ( by simpa using by nlinarith [ Nat.sub_add_cancel hk ] );
            · exact fun x hx y hy hxy => hdisj x hx y hy hxy;
          rcases k with ( _ | k ) <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ];
          nlinarith [ show 0 < r.factorial * ( k + 1 ) ^ r by positivity ];
      set F1 := 𝓕.filter (fun S => u ∈ S)
      set 𝓕' := F1.image (fun S => S.erase u);
      obtain ⟨𝓖', hG'sub, Y', hG'card, hG'sun⟩ := ih k hk 𝓕' (by
      grind +locals) (by
      rwa [ Finset.card_image_of_injOn ];
      intro S hS T hT h_eq; simp_all +decide [ Finset.ext_iff ] ;
      grind);
      refine' ⟨ 𝓖'.image ( insert u ), _, insert u Y', _, _ ⟩;
      · intro s hs;
        rw [ Finset.mem_image ] at hs; obtain ⟨ t, ht, rfl ⟩ := hs; specialize hG'sub ht; aesop;
      · rw [ Finset.card_image_of_injOn, hG'card ];
        intro x hx y hy; have := hG'sub hx; have := hG'sub hy; aesop;
      · convert isSunflower_insert_image hG'sun _ |>.1 using 1;
        intro s hs; have := hG'sub hs; aesop;

end LeanGallery.Combinatorics.Erdos880
