/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Statement
import LeanGallery.Combinatorics.Erdos880.Kneser

/-!
# Axiom guard (regression test)

`#print axioms` only emits an `info` message — a `sorry`/`axiom` regression would still *build*. The
`#guard_msgs` wrappers below pin the **exact** axiom list of every load-bearing theorem, so if anyone
ever reintroduces `sorryAx` (or any new axiom) the build **fails** here. This is the permanent,
build-enforced statement of "the whole resolution is kernel-pure".

Expected axioms for every headline: `[propext, Classical.choice, Quot.sound]` — the three mathlib
foundations, nothing else (no `sorryAx`, no `native_decide`/`ofReduceBool`, no cited `axiom`).
-/

namespace LeanGallery.Combinatorics.Erdos880

-- k ≥ 3 negative answer (the headline).
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880

-- k = 2 bounded-gaps case.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_order_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_order_two

-- Strengthening: basis of order exactly h.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_exact_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_exact_order

-- Quantitative companion: HHP07 Theorem 3, k(h) ≥ 2^{h-2}+h-1 (witness form).
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm3_kh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm3_kh

-- HHP07 Theorem 4, f(h) ≥ 2^{h-2}+h-1 (restricted order exactly 2^{h-2}+h-1, witness form).
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm4_fh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm4_fh

-- HHP07 Theorem 4 sharp: ord_r(constA h) = 2^{h-2}+h-1 exactly.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm4_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm4_exact

-- Faithful Δ form (k ≥ 3): Δ(restrictedSums (constA h) h) = +∞ (HHP07 Theorem 1(ii), the actual limsup).
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_delta

-- Faithful Δ form (k = 2): Δ(restrictedSums A 2) ≤ 2 (HHP07 Theorem 1(i)).
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_order_two_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms erdos_880_order_two_delta

-- Faithfulness certificate: EvGapLe = textbook Nat.nth gap-sequence bound (so Delta = limsup).
/-- info: 'LeanGallery.Combinatorics.Erdos880.evGapLe_iff_nth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evGapLe_iff_nth

-- Non-construction frontier: Δ(restrictedSums A k) is antitone in k (toward HHP07 Conjecture 6).
/-- info: 'LeanGallery.Combinatorics.Erdos880.Delta_restrictedSums_anti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Delta_restrictedSums_anti

-- HHP07 Proposition 7 (+1 form): Δ(3×A) ≤ Δ(2×A) + 1 for every infinite set of positive integers.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_prop7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_prop7

-- HHP07 Proposition 5 (exact-fold): Δ(h₀×A) finite ⟹ Δ(h×A) finite for h ≥ h₀.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_prop5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_prop5

-- HHP07 Theorem 9 (one-step structural core): pairwise-disjoint (h+1)-rep family ⟹ Δ((h+g)×A) ≤ Δ(h×A).
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm9_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm9_step

-- The Erdős–Rado sunflower lemma (mathlib has none): > r!·k^r sets of card ≤ r contain a k-sunflower.
/-- info: 'LeanGallery.Combinatorics.Erdos880.sunflower_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sunflower_exists

-- HHP07 Theorem 9, one step reduced to the density estimate: a large equal-sum (h+1)-subset family of
-- S ⊆ A yields ∃ h', h < h' ≤ 2h+1 ∧ Δ(h'×A) ≤ Δ(h×A) (via Erdős–Rado + the sunflower bridge).
/-- info: 'LeanGallery.Combinatorics.Erdos880.exists_fold_Delta_le_of_equal_sum_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exists_fold_Delta_le_of_equal_sum_family

-- HHP07 Theorem 8 (UNCONDITIONAL): Δ(h₀×A) finite ⟹ an increasing sequence (hⱼ) with Δ(hⱼ×A)
-- non-increasing. Full chain: Erdős–Rado sunflower + density estimate (D1+D2+D3) + iteration.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm8

-- HHP07 Theorem 9 (UNCONDITIONAL, PRECISE bounds): the sequence with hⱼ+2 ≤ hⱼ₊₁ ≤ hⱼ+h₀+1 and
-- Δ(hⱼ₊₁×A) ≤ Δ(hⱼ×A). Fixed (h₀+1)-sized sunflower objects give the exact paper increment.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm9

-- Faithful Δ form (HHP07 Theorem 3): Δ(l × A) = +∞ for every fold l ≤ 2^{h-2}+h-2.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm3_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm3_delta

-- Faithful Δ-transition (HHP07 Theorem 4): Δ jumps +∞ → finite exactly at the restricted order.
/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_thm4_delta_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms erdos_880_thm4_delta_transition

-- The Dyson e-transform engine of finite Kneser: the two invariants — sumset only shrinks, and
-- |s|+|t| is preserved — proven kernel-pure.
/-- info: 'Erdos880Kneser.etransform_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Erdos880Kneser.etransform_card
/-- info: 'Erdos880Kneser.etransform_sumset_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Erdos880Kneser.etransform_sumset_subset

-- The sumset stabilizer (period) API — the `H` of Kneser, absent from mathlib: a finite AddSubgroup
-- whose elements fix the sumset. Kernel-pure, the keystone for assembling finite Kneser.
-- Iterated Cauchy–Davenport (prime modulus): |jS| ≥ min(p, j|S|−(j−1)). From mathlib's
-- ZMod.cauchy_davenport. Kernel-pure.
/-- info: 'Erdos880Kneser.iterated_cauchy_davenport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Erdos880Kneser.iterated_cauchy_davenport

/-- info: 'Erdos880Kneser.addStab_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Erdos880Kneser.addStab_finite
/-- info: 'Erdos880Kneser.vadd_mem_of_mem_addStab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Erdos880Kneser.vadd_mem_of_mem_addStab

-- The non-representability crux.
/-- info: 'LeanGallery.Combinatorics.Erdos880.constA_not_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms constA_not_repr

-- The number-theoretic core.
/-- info: 'LeanGallery.Combinatorics.Erdos880.binary_min_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms binary_min_rep

-- Its general form (minimal-weight rep = binary digits).
/-- info: 'LeanGallery.Combinatorics.Erdos880.binary_rep_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms binary_rep_unique

end LeanGallery.Combinatorics.Erdos880
