/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The Dyson e-transform — the inductive engine of Kneser's theorem (finite form)

The two **Kneser theorems** (the density form on `ℤ` and the finite-group stabilizer form) are absent
from mathlib. This file makes a *proven, kernel-pure* down-payment toward the finite-group form of
Kneser's theorem:

> **Kneser (finite form).** For finite nonempty `s, t` in an abelian group, with `H` the stabilizer
> (period) of `s + t`, one has `|s + H| + |t + H| ≤ |s + t| + |H|`.

The standard proof (Nathanson, *Additive Number Theory: Inverse Problems*, Ch. 4; Tao–Vu) is induction
on `|t|`, driven by the **Dyson e-transform** `(s, t) ↦ (s ∪ (t + e), t ∩ (s − e))`. This file proves the
two facts that make that induction go — the e-transform **preserves the sumset** (`s + t` only shrinks)
and **preserves `|s| + |t|`** — plus the bookkeeping lemmas (`eR ⊆ t`, strict-decrease criterion,
`eL` nonempty, a nonempty-`eR` witness). The remaining work is the induction itself + the stabilizer
extraction, which is the in-flight Aristotle leaf `aristotle/kneser` (`21d6f349`); these lemmas are the
verified foundation onto which that result (or a future-lap hand proof) will land.

**No axioms are introduced here** — every lemma is `[propext, Classical.choice, Quot.sound]`.

## ⚠️ mathlib ALREADY HAS this e-transform (lap-7 finding)

`Mathlib.Combinatorics.Additive.ETransform` provides `Finset.addDysonETransform` with `.card`
(card invariant), `.subset` (`s_e + t_e ⊆ s + t`), `.vadd_finset_snd_subset_fst`, idempotency, etc. —
i.e. the `eL/eR`/`etransform_card`/`etransform_sumset_subset` below **duplicate mathlib**. Moreover
`Mathlib.Combinatorics.Additive.CauchyDavenport` proves Cauchy–Davenport via the DeVos e-transform
induction: `cauchy_davenport_minOrder_mul` (`|s+t| ≥ min (minOrder G) (|s|+|t|−1)`, general group) and
`ZMod.cauchy_davenport` (prime modulus). **Implication for the prime-modulus residue clause:** for a
PRIME modulus `g`, `ZMod.cauchy_davenport` already forces `|Ā| = 1`
(`g ≥ |gĀ| ≥ g(|Ā|−1)+1` with `|gĀ| ≥ min(g, …)` and `g` prime ⟹ `minOrder = g`). The composite-`g`
case still needs full **Kneser** (stabilizer form), which mathlib LACKS (`mulStab`/`addStab` absent,
confirmed lap 7) — that is the in-flight Aristotle leaf. Future laps: prefer mathlib's
`addDysonETransform` over the local `eL/eR` here, and build full Kneser as `addStab` (sumset stabilizer
subgroup) + the DeVos/ETransform induction tracking the stabilizer.
-/

namespace Erdos880Kneser

open Finset Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Dyson e-transform, first component: `s_e = s ∪ (t + e)`. -/
def eL (s t : Finset G) (e : G) : Finset G := s ∪ t.image (· + e)

/-- Dyson e-transform, second component: `t_e = t ∩ (s − e)`. -/
def eR (s t : Finset G) (e : G) : Finset G := t ∩ s.image (· + (-e))

/-- `t_e ⊆ t`: the transform never enlarges the second component (the induction variable). -/
lemma eR_subset (s t : Finset G) (e : G) : eR s t e ⊆ t := Finset.inter_subset_left

/-- `s_e` is nonempty whenever `s` is (since `s ⊆ s_e`). -/
lemma eL_nonempty {s : Finset G} (t : Finset G) (e : G) (hs : s.Nonempty) :
    (eL s t e).Nonempty := hs.mono Finset.subset_union_left

/-- Choosing `e = a − b` with `a ∈ s`, `b ∈ t` keeps `t_e` nonempty (it contains `b`). This is how the
induction guarantees both components stay nonempty. -/
lemma mem_eR_of {s t : Finset G} {a b : G} (ha : a ∈ s) (hb : b ∈ t) :
    b ∈ eR s t (a - b) := by
  rw [eR, Finset.mem_inter, Finset.mem_image]
  exact ⟨hb, a, ha, by abel⟩

/-- `t_e ⊊ t` whenever some `b ∈ t` has `b + e ∉ s` — i.e. the e-transform makes genuine progress. The
induction on `|t|` recurses exactly when such a `b` exists. -/
lemma eR_ssubset {s t : Finset G} {e : G} {b : G} (hb : b ∈ t) (hbs : b + e ∉ s) :
    eR s t e ⊂ t := by
  rw [Finset.ssubset_iff_of_subset (eR_subset s t e)]
  refine ⟨b, hb, ?_⟩
  rw [eR, Finset.mem_inter, Finset.mem_image]
  rintro ⟨_, a, ha, hab⟩
  apply hbs
  have hba : b + e = a := by rw [← hab]; abel
  rw [hba]; exact ha

/-- **The e-transform preserves `|s| + |t|`.** `|s_e| + |t_e| = |s| + |t|`. (`|t_e| = |s ∩ (t+e)|`, and
`|s_e| + |s ∩ (t+e)| = |s| + |t+e| = |s| + |t|` by inclusion–exclusion.) The cardinality invariant of
Kneser's induction. -/
lemma etransform_card (s t : Finset G) (e : G) :
    (eL s t e).card + (eR s t e).card = s.card + t.card := by
  classical
  have hinjE : Function.Injective (fun x : G => x + e) := add_left_injective e
  set T := t.image (· + e) with hT
  have hTcard : T.card = t.card := Finset.card_image_of_injective _ hinjE
  have himg : (eR s t e).image (fun x => x + e) = s ∩ T := by
    unfold eR
    rw [Finset.image_inter _ _ hinjE, Finset.image_image]
    have hcomp : ((fun x : G => x + e) ∘ (fun x => x + -e)) = id := by
      funext x; simp
    rw [hcomp, Finset.image_id, Finset.inter_comm]
  have hkey : (eR s t e).card = (s ∩ T).card := by
    rw [← himg, Finset.card_image_of_injective _ hinjE]
  have hu : (s ∪ T).card + (s ∩ T).card = s.card + T.card := Finset.card_union_add_card_inter s T
  calc (eL s t e).card + (eR s t e).card
      = (s ∪ T).card + (s ∩ T).card := by rw [eL, hkey]
    _ = s.card + T.card := hu
    _ = s.card + t.card := by rw [hTcard]

/-- **The e-transform never enlarges the sumset.** `s_e + t_e ⊆ s + t`. With the card invariant above,
this lets the induction replace `(s, t)` by `(s_e, t_e)` while controlling `|s + t|` from below. -/
lemma etransform_sumset_subset (s t : Finset G) (e : G) :
    eL s t e + eR s t e ⊆ s + t := by
  classical
  intro z hz
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [eR, Finset.mem_inter, Finset.mem_image] at hy
  obtain ⟨hyt, a, ha, hae⟩ := hy
  have hya : y + e = a := by rw [← hae]; abel
  rw [eL, Finset.mem_union, Finset.mem_image] at hx
  rw [Finset.mem_add]
  rcases hx with hxs | ⟨b, hbt, hbe⟩
  · exact ⟨x, hxs, y, hyt, rfl⟩
  · refine ⟨a, ha, b, hbt, ?_⟩
    rw [← hbe, ← hya]; abel

/-! ### The sumset stabilizer (period) `addStab` — the `H` of Kneser's theorem.

mathlib has **no** sumset-stabilizer API (`mulStab`/`addStab` absent, confirmed 2026-06; only
`MulAction.stabilizer` on `Set`s and a comment in `VerySmallDoubling`). The period `H` in Kneser's
theorem is the stabilizer of the sumset `C = s + t` under translation: `H = {x | (x + ·) '' C = C}`.
These lemmas provide that API: `H` is a finite `AddSubgroup` (`zero/add/neg_mem`, `addStab_finite`) and
its elements stabilize `C` (`vadd_mem_of_mem_addStab`). This is the keystone for assembling Kneser
(`|s+H|+|t+H| ≤ |s+t|+|H|`) from the e-transform engine above — needed whether the in-flight Aristotle
leaf lands (to interface its raw-`Finset` `H`) or a local hand-proof is required. Kernel-pure. -/

/-- The **sumset stabilizer / period** of a finset `C`: translations `x` fixing `C` setwise. For
`C = s + t` this is Kneser's subgroup `H`. -/
def addStab (C : Finset G) : Set G := {x : G | C.image (x + ·) = C}

@[simp] lemma mem_addStab {C : Finset G} {x : G} : x ∈ addStab C ↔ C.image (x + ·) = C := Iff.rfl

/-- Elements of the period stabilize `C`: `x ∈ addStab C → c ∈ C → x + c ∈ C`. -/
lemma vadd_mem_of_mem_addStab {C : Finset G} {x : G} (hx : x ∈ addStab C) {c : G} (hc : c ∈ C) :
    x + c ∈ C := by
  rw [mem_addStab] at hx; rw [← hx]; exact Finset.mem_image_of_mem _ hc

lemma zero_mem_addStab (C : Finset G) : (0 : G) ∈ addStab C := by
  rw [mem_addStab]; simp

lemma add_mem_addStab {C : Finset G} {x y : G} (hx : x ∈ addStab C) (hy : y ∈ addStab C) :
    x + y ∈ addStab C := by
  rw [mem_addStab] at *
  have hfun : (fun c => x + y + c) = (fun c => x + c) ∘ (fun c => y + c) := by
    funext c; simp [add_assoc]
  rw [hfun, ← Finset.image_image, hy, hx]

lemma neg_mem_addStab {C : Finset G} {x : G} (hx : x ∈ addStab C) : -x ∈ addStab C := by
  rw [mem_addStab] at *
  have hcomp : (fun c => -x + c) ∘ (fun c => x + c) = id := by funext c; simp
  have h := congrArg (Finset.image (fun c => -x + c)) hx
  rwa [Finset.image_image, hcomp, Finset.image_id, eq_comm] at h

/-- **The period is finite** (for nonempty `C`): `x ∈ addStab C ⟹ x + c₀ ∈ C ⟹ x ∈ C − c₀`, a finite
set. So `H` is a *finite* subgroup, as Kneser requires. -/
lemma addStab_finite {C : Finset G} (hC : C.Nonempty) : (addStab C).Finite := by
  obtain ⟨c₀, hc₀⟩ := hC
  refine Set.Finite.subset (C.image (· - c₀)).finite_toSet ?_
  intro x hx
  have hxc : x + c₀ ∈ C := vadd_mem_of_mem_addStab hx hc₀
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨x + c₀, hxc, by abel⟩

/-- The period bundled as an `AddSubgroup` — so mathlib's coset/Lagrange machinery applies (finite
Kneser writes `|s + H|` as a union of `H`-cosets and uses `|H| ∣ |s + H|`). -/
def addStabSubgroup (C : Finset G) : AddSubgroup G where
  carrier := addStab C
  zero_mem' := zero_mem_addStab C
  add_mem' := add_mem_addStab
  neg_mem' := neg_mem_addStab

@[simp] lemma mem_addStabSubgroup {C : Finset G} {x : G} :
    x ∈ addStabSubgroup C ↔ C.image (x + ·) = C := Iff.rfl

/-! ### Iterated Cauchy–Davenport (prime modulus) — the finite content of clause (a) for prime `g`.

mathlib's `ZMod.cauchy_davenport` gives `|s+t| ≥ min(p, |s|+|t|−1)` for prime `p`. Iterating it (here)
yields the `j`-fold bound `|jS| ≥ min(p, j·|S| − (j−1))`. Combined with the periodic-set density, this
is exactly the density-Kneser clause `|res(jB)| ≥ j·|res B| − (j−1)` in the **prime-modulus** case;
composite moduli need full Kneser (the in-flight Aristotle leaf / the `addStab` stabilizer machinery
above). Kernel-pure. -/

/-- The `j`-fold pointwise sumset `S + S + ⋯ + S` of a finset (`iterAdd S 0 = {0}`, the pointwise
identity). Written explicitly rather than as `j • S`, which under `open Pointwise` would be the
`SMul ℕ (Finset _)` pointwise-scaling action — a different operation. -/
def iterAdd (S : Finset G) : ℕ → Finset G
  | 0 => {0}
  | (j + 1) => iterAdd S j + S

@[simp] lemma iterAdd_zero (S : Finset G) : iterAdd S 0 = {0} := rfl

lemma iterAdd_succ (S : Finset G) (j : ℕ) : iterAdd S (j + 1) = iterAdd S j + S := rfl

lemma iterAdd_one (S : Finset G) : iterAdd S 1 = S := by
  rw [iterAdd_succ, iterAdd_zero]
  ext x
  simp [Finset.mem_add]

lemma iterAdd_nonempty {S : Finset G} (hS : S.Nonempty) : ∀ j, (iterAdd S j).Nonempty
  | 0 => ⟨0, by simp⟩
  | (j + 1) => by rw [iterAdd_succ]; exact (iterAdd_nonempty hS j).add hS

/-- **Iterated Cauchy–Davenport (prime modulus).** For a nonempty `S ⊆ ℤ/pℤ` (`p` prime) and `j ≥ 1`,
the `j`-fold sumset satisfies `|jS| ≥ min(p, j·|S| − (j−1))`. Standard induction on `j` from mathlib's
`ZMod.cauchy_davenport`. This is the prime-modulus finite content of the density-Kneser clause
`|res(jB)| ≥ j·|res B| − (j−1)` (the non-saturating case `j·|S|−(j−1) ≤ p`); composite moduli need the
full Kneser (stabilizer) theorem. -/
lemma iterated_cauchy_davenport {p : ℕ} (hp : p.Prime) {S : Finset (ZMod p)} (hS : S.Nonempty) :
    ∀ j, 1 ≤ j → min p (j * S.card - (j - 1)) ≤ (iterAdd S j).card := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ k ih =>
    intro _hj
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      rw [iterAdd_one]
      simp
    · have hk : 1 ≤ k := hk1
      have IH := ih hk
      have hSc : 1 ≤ S.card := Finset.Nonempty.card_pos hS
      have hne : (iterAdd S k).Nonempty := iterAdd_nonempty hS k
      have hCD : min p ((iterAdd S k).card + S.card - 1) ≤ (iterAdd S k + S).card :=
        ZMod.cauchy_davenport hp hne hS
      rw [iterAdd_succ]
      refine le_trans ?_ hCD
      apply le_min (min_le_left _ _)
      have hexp : (k + 1) * S.card = k * S.card + S.card := by ring
      by_cases hc : p ≤ k * S.card - (k - 1)
      · rw [min_eq_left hc] at IH
        calc min p ((k + 1) * S.card - (k + 1 - 1)) ≤ p := min_le_left _ _
          _ ≤ (iterAdd S k).card + S.card - 1 := by omega
      · rw [Nat.not_le] at hc
        rw [min_eq_right (le_of_lt hc)] at IH
        have hle : min p ((k + 1) * S.card - (k + 1 - 1)) ≤ (k + 1) * S.card - (k + 1 - 1) :=
          min_le_right _ _
        omega

end Erdos880Kneser
