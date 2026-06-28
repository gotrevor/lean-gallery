/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos880.Basic

/-!
# The asymptotic gap functional `Δ` (HHP07) and the non-construction frontier

This file introduces a **faithful** formalization of the asymptotic gap functional `Δ` of
Hegyvári–Hennecart–Plagne (HHP07). For an increasing sequence `a₁ < a₂ < ⋯` the paper sets

  `Δ(𝒜) = limsup_{i → ∞} (a_{i+1} − a_i)`  (a value in `ℕ ∪ {+∞}`).

Rather than build the increasing enumeration (`Nat.nth`) and a `limsup`, we use the elementary
identity `limsup g = inf { d | eventually gₙ ≤ d }`: for the consecutive-gap sequence of an
(infinite) set `X`, "eventually `gₙ ≤ d`" says exactly that, far enough out, **every element of `X`
has a successor in `X` within distance `d`** (`EvGapLe X d`). We therefore *define*

  `Δ(X) = sInf { d : ℕ | EvGapLe X d }  (= ⊤ if no finite `d` works)`,

a value in `ℕ∞`. This is definitionally the paper's `limsup` of consecutive gaps (no enumeration
needed), and `Δ(X) < ⊤` is exactly "the gaps of `X` are bounded", i.e. `X` has bounded gaps.

This is the infrastructure the *non-construction* results of HHP07 need (Prop 5, Prop 7, Thm 8/9):
they all concern `Δ(h × A)` for a **general** set `A`, not the explicit construction. The
construction core (`#880`, Thms 1, 3, 4) is complete elsewhere; this file opens the related frontier.

Source: HHP07, *Combin. Probab. Comput.* **16** (2007) 747–756, §1 (definition of `Δ`), §2.
-/

namespace LeanGallery.Combinatorics.Erdos880

open scoped BigOperators
open Finset

/-- `EvGapLe X d` : **eventually**, every element of `X` has a successor in `X` within distance `d`.
For an infinite `X` with increasing enumeration `a₁ < a₂ < ⋯`, this says exactly that
`a_{i+1} − a_i ≤ d` for all large `i` — i.e. `d` is an eventual upper bound for the gap sequence. -/
def EvGapLe (X : Set ℕ) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∀ x ∈ X, N ≤ x → ∃ y ∈ X, x < y ∧ y ≤ x + d

/-- An eventual gap bound `d` is also an eventual gap bound for any larger `d'`. -/
lemma EvGapLe.mono {X : Set ℕ} {d d' : ℕ} (hdd : d ≤ d') (h : EvGapLe X d) : EvGapLe X d' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun x hx hxN => ?_⟩
  obtain ⟨y, hy, hxy, hyd⟩ := hN x hx hxN
  exact ⟨y, hy, hxy, le_trans hyd (by omega)⟩

open Classical in
/-- The **asymptotic gap functional** `Δ(X) ∈ ℕ∞` of HHP07: the least `d` that eventually bounds the
consecutive gaps of `X`, or `⊤ (= +∞)` if the gaps are unbounded. Faithful to `limsup(a_{i+1}−a_i)`
via `limsup g = inf { d | eventually gₙ ≤ d }`. -/
noncomputable def Delta (X : Set ℕ) : ℕ∞ :=
  if _h : ∃ d, EvGapLe X d then ((sInf {d : ℕ | EvGapLe X d} : ℕ) : ℕ∞) else ⊤

/-- The workhorse characterization: `Δ(X) ≤ m` iff `m` is an eventual gap bound for `X`. -/
lemma Delta_le_nat_iff (X : Set ℕ) (m : ℕ) :
    Delta X ≤ (m : ℕ∞) ↔ EvGapLe X m := by
  unfold Delta
  split_ifs with h
  · constructor
    · intro hle
      have hmem : sInf {d | EvGapLe X d} ∈ {d | EvGapLe X d} := Nat.sInf_mem h
      have hle' : sInf {d | EvGapLe X d} ≤ m := by exact_mod_cast hle
      exact EvGapLe.mono hle' hmem
    · intro hgap
      have : sInf {d | EvGapLe X d} ≤ m := Nat.sInf_le hgap
      exact_mod_cast this
  · constructor
    · intro hle; simp at hle
    · intro hgap; exact absurd ⟨m, hgap⟩ h

/-- `Δ(X) < ⊤` (gaps bounded) iff some finite `d` eventually bounds the gaps. -/
lemma Delta_lt_top_iff (X : Set ℕ) : Delta X < ⊤ ↔ ∃ d, EvGapLe X d := by
  constructor
  · intro hlt
    by_contra hcon
    have : Delta X = ⊤ := by unfold Delta; rw [dif_neg hcon]
    rw [this] at hlt; exact lt_irrefl _ hlt
  · rintro ⟨d, hd⟩
    have : Delta X ≤ (d : ℕ∞) := (Delta_le_nat_iff X d).mpr hd
    exact lt_of_le_of_lt this (by exact_mod_cast ENat.coe_lt_top d)

/-- `Δ(X) = ⊤` (unbounded gaps) iff no finite `d` eventually bounds the gaps. -/
lemma Delta_eq_top_iff (X : Set ℕ) : Delta X = ⊤ ↔ ¬ ∃ d, EvGapLe X d := by
  rw [← not_iff_not, ← Ne, ← lt_top_iff_ne_top, Delta_lt_top_iff, not_not]

/-- `Δ` depends only on the family of eventual gap bounds: sets with the same `EvGapLe` predicate have
the same `Δ`. -/
lemma Delta_congr {X Y : Set ℕ} (h : ∀ d, EvGapLe X d ↔ EvGapLe Y d) : Delta X = Delta Y := by
  unfold Delta
  have hset : {d : ℕ | EvGapLe X d} = {d | EvGapLe Y d} := by ext d; exact h d
  have hcond : (∃ d, EvGapLe X d) ↔ ∃ d, EvGapLe Y d :=
    ⟨fun ⟨d, hd⟩ => ⟨d, (h d).mp hd⟩, fun ⟨d, hd⟩ => ⟨d, (h d).mpr hd⟩⟩
  by_cases hc : ∃ d, EvGapLe X d
  · rw [dif_pos hc, dif_pos (hcond.mp hc), hset]
  · rw [dif_neg hc, dif_neg (fun hh => hc (hcond.mpr hh))]

/-! ### Monotonicity: `Δ` is antitone under `⊆`

A **bigger** set has **smaller** gaps: adding points can only subdivide gaps, never enlarge them. So
`S ⊆ X ⟹ Δ(X) ≤ Δ(S)` (sharp, no slack). This is the structural backbone of the `Δ((h+1)×A) ≤ Δ(h×A)`
monotonicity questions (Conjecture 6, Thm 8) and gives `Δ(restrictedSums A k)` antitone in `k`. -/

/-- An eventual gap bound transfers from a set to any **superset** (sharp): if `S ⊆ X`, `S` infinite,
and `S` has gaps eventually `≤ d`, then so does `X` (each `X`-point's `S`-successor is within `d`). -/
lemma evGapLe_superset {S X : Set ℕ} {d : ℕ} (hsub : S ⊆ X) (hS : S.Infinite) (h : EvGapLe S d) :
    EvGapLe X d := by
  classical
  obtain ⟨N, hN⟩ := h
  obtain ⟨e₀, he₀S, hNe₀⟩ := hS.exists_gt N
  refine ⟨e₀, fun x _ hxe₀ => ?_⟩
  set P : ℕ → Prop := fun a => a ∈ S ∧ N ≤ a with hP
  set w := Nat.findGreatest P x with hw
  have hPe₀ : P e₀ := ⟨he₀S, le_of_lt hNe₀⟩
  have hwe₀ : e₀ ≤ w := Nat.le_findGreatest hxe₀ hPe₀
  have hPw : P w := Nat.findGreatest_spec hxe₀ hPe₀
  have hwx : w ≤ x := Nat.findGreatest_le x
  obtain ⟨y, hyS, hwy, hyd⟩ := hN w hPw.1 hPw.2
  have hyx : x < y := by
    by_contra hle
    rw [not_lt] at hle
    have hPy : P y := ⟨hyS, le_trans hPw.2 (le_of_lt hwy)⟩
    have : y ≤ w := Nat.le_findGreatest hle hPy
    omega
  exact ⟨y, hsub hyS, hyx, by omega⟩

/-- If every eventual gap bound of `S` is one of `X`, then `Δ(X) ≤ Δ(S)`. -/
lemma Delta_le_of_evGapLe_imp {S X : Set ℕ} (himp : ∀ d, EvGapLe S d → EvGapLe X d) :
    Delta X ≤ Delta S := by
  unfold Delta
  by_cases hS : ∃ d, EvGapLe S d
  · rw [dif_pos hS, dif_pos (hS.imp himp)]
    exact Nat.cast_le.mpr (Nat.sInf_le (himp _ (Nat.sInf_mem hS)))
  · rw [dif_neg hS]; exact le_top

/-- **`Δ` is antitone under `⊆`.** A subset has gaps at least as large: `S ⊆ X ⟹ Δ(X) ≤ Δ(S)`. -/
theorem Delta_anti {S X : Set ℕ} (hsub : S ⊆ X) (hS : S.Infinite) : Delta X ≤ Delta S :=
  Delta_le_of_evGapLe_imp (fun _d hd => evGapLe_superset hsub hS hd)

/-- If every eventual gap bound `d` of `X` yields the bound `d + 1` for `Y`, then
`Δ(Y) ≤ Δ(X) + 1`. (The `+1` companion of `Delta_le_of_evGapLe_imp`, for one-sided coverings.) -/
lemma Delta_le_succ_of_evGapLe_imp {X Y : Set ℕ}
    (himp : ∀ d, EvGapLe X d → EvGapLe Y (d + 1)) : Delta Y ≤ Delta X + 1 := by
  unfold Delta
  by_cases hX : ∃ d, EvGapLe X d
  · rw [dif_pos hX, dif_pos (⟨_, himp _ (Nat.sInf_mem hX)⟩ : ∃ d, EvGapLe Y d)]
    have hle : sInf {d | EvGapLe Y d} ≤ sInf {d | EvGapLe X d} + 1 :=
      Nat.sInf_le (himp _ (Nat.sInf_mem hX))
    calc (↑(sInf {d | EvGapLe Y d}) : ℕ∞)
        ≤ ↑(sInf {d | EvGapLe X d} + 1) := Nat.cast_le.mpr hle
      _ = ↑(sInf {d | EvGapLe X d}) + 1 := by push_cast; ring
  · rw [dif_neg hX]; exact le_top

/-- If every eventual gap bound `d` of `X` yields the bound `d + c` for `Y`, then `Δ(Y) ≤ Δ(X) + c`.
(The general `+c` companion of `Delta_le_of_evGapLe_imp`, used for the Prop 5 covering.) -/
lemma Delta_le_add_of_evGapLe_imp {X Y : Set ℕ} (c : ℕ)
    (himp : ∀ d, EvGapLe X d → EvGapLe Y (d + c)) : Delta Y ≤ Delta X + c := by
  unfold Delta
  by_cases hX : ∃ d, EvGapLe X d
  · rw [dif_pos hX, dif_pos (⟨_, himp _ (Nat.sInf_mem hX)⟩ : ∃ d, EvGapLe Y d)]
    have hle : sInf {d | EvGapLe Y d} ≤ sInf {d | EvGapLe X d} + c :=
      Nat.sInf_le (himp _ (Nat.sInf_mem hX))
    calc (↑(sInf {d | EvGapLe Y d}) : ℕ∞) ≤ ↑(sInf {d | EvGapLe X d} + c) := Nat.cast_le.mpr hle
      _ = ↑(sInf {d | EvGapLe X d}) + c := by push_cast; ring
  · rw [dif_neg hX]; exact le_top

/-! ### `Δ` ignores finite modifications

Removing (or adding) finitely many points leaves the *eventual* gap behaviour unchanged, so `Δ` is
invariant: `Δ(X \ F) = Δ(X)` for finite `F`. This is what licenses every "for large enough" / "beyond
the finite set `i₀`" step in the HHP07 frontier proofs. -/

/-- Eventual gap bounds are unaffected by deleting a finite set (the two sets agree past `sup F`). -/
lemma EvGapLe_diff_finite_iff {X : Set ℕ} {d : ℕ} {F : Set ℕ} (hF : F.Finite) :
    EvGapLe (X \ F) d ↔ EvGapLe X d := by
  obtain ⟨M, hM⟩ := hF.bddAbove
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨max N (M + 1), fun x hx hxN => ?_⟩
    have hxF : x ∉ F := fun hf => by have := hM hf; have : M + 1 ≤ x := le_trans (le_max_right _ _) hxN; omega
    obtain ⟨y, hy, hxy, hyd⟩ := hN x ⟨hx, hxF⟩ (le_trans (le_max_left _ _) hxN)
    exact ⟨y, hy.1, hxy, hyd⟩
  · rintro ⟨N, hN⟩
    refine ⟨max N (M + 1), fun x hx hxN => ?_⟩
    obtain ⟨y, hy, hxy, hyd⟩ := hN x hx.1 (le_trans (le_max_left _ _) hxN)
    have hyF : y ∉ F := fun hf => by
      have := hM hf; have : M + 1 ≤ x := le_trans (le_max_right _ _) hxN; omega
    exact ⟨y, ⟨hy, hyF⟩, hxy, hyd⟩

/-- **`Δ` ignores finite deletions.** `Δ(X \ F) = Δ(X)` whenever `F` is finite. -/
theorem Delta_diff_finite {X : Set ℕ} {F : Set ℕ} (hF : F.Finite) :
    Delta (X \ F) = Delta X :=
  Delta_congr (fun _d => EvGapLe_diff_finite_iff hF)

/-! ### Faithfulness certificate: `EvGapLe` is the textbook enumeration gap bound

The whole point of defining `Delta` via `EvGapLe` (no enumeration) is to avoid `Nat.nth`. The lemma
below certifies that this loses nothing: `EvGapLe X d` is *equivalent* to "the consecutive-gap
sequence `e(i+1) − e(i)` of the increasing enumeration `e = Nat.nth (· ∈ X)` is eventually `≤ d`".
Combined with `Delta = sInf {d | EvGapLe X d}` and `limsup g = inf {d | ∀ᶠ n, gₙ ≤ d}`, this says
`Delta X` is exactly the paper's `limsup_{i→∞}(a_{i+1} − a_i)`. (Aristotle-assisted, job `cba66ae5`;
verified in-kernel, `#print axioms` clean.) -/
theorem evGapLe_iff_nth (X : Set ℕ) (hX : X.Infinite) (d : ℕ) :
    EvGapLe X d ↔ ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
        Nat.nth (· ∈ X) (i + 1) - Nat.nth (· ∈ X) i ≤ d := by
  unfold EvGapLe
  constructor
  · intro hN
    obtain ⟨N, hN⟩ := hN
    obtain ⟨I, hI⟩ : ∃ I, N ≤ Nat.nth (fun x => x ∈ X) I := by
      refine ⟨N, Nat.le_nth (fun h => False.elim <| hX <| h.subset fun x hx => hx)⟩
    refine ⟨I, fun i hi => ?_⟩
    obtain ⟨y, hyX, hy_gt, hy_le⟩ := hN (Nat.nth (fun x => x ∈ X) i)
      (Nat.nth_mem_of_infinite hX i)
      (le_trans hI (Nat.nth_monotone (show {x | x ∈ X}.Infinite from hX) hi))
    refine Nat.sub_le_of_le_add ?_
    rw [add_comm, Nat.nth_eq_sInf]
    exact le_trans (Nat.sInf_le ⟨hyX, fun k hk => by
      linarith [Nat.nth_monotone (show {x | x ∈ X}.Infinite from hX) (show k ≤ i by linarith)]⟩)
      (by linarith)
  · simp +zetaDelta at *
    intro x hx
    refine ⟨Nat.nth (fun x => x ∈ X) x + 1, fun y hy hyx => ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, Nat.nth (fun x => x ∈ X) i ≤ y ∧ y < Nat.nth (fun x => x ∈ X) (i + 1) := by
      have h_unbounded : ∀ M : ℕ, ∃ i, Nat.nth (fun x => x ∈ X) i > M := fun M =>
        ⟨M + 1, Nat.le_nth (fun h => False.elim <| hX <| h.subset fun x hx => hx)⟩
      contrapose! h_unbounded
      refine ⟨y, fun i => ?_⟩
      induction' i with i ih <;> simp_all +decide [Nat.nth_zero]
      exact Nat.sInf_le hy
    have hi_ge_x : x ≤ i := by
      contrapose! hyx
      exact Nat.lt_succ_of_le (le_trans hi.2.le
        (Nat.nth_monotone (show {n | n ∈ X}.Infinite from hX) (by linarith)))
    exact ⟨Nat.nth (fun x => x ∈ X) (i + 1), Nat.nth_mem_of_infinite hX _, hi.2,
      by linarith [hx i hi_ge_x]⟩

/-! ### `EvGapLe ↔ BoundedGapsBy` toolkit

`BoundedGapsBy X C` (every window `[x, x+C]` eventually meets `X`, from `Basic.lean`) and `EvGapLe`
are two faces of "bounded gaps". Key for the non-construction frontier: `BoundedGapsBy` is **monotone
in the set** (a syndetic subset forces its superset to have bounded gaps), which is exactly how Prop 7
will bound `Δ(3 × A)` from a covered subset of `3 × A`. -/

/-- An eventual gap bound on an **infinite** set is a covering bound: beyond some point every window
`[z, z+d]` meets `X`. (The "`d`-density" half of bounded gaps; uses `Nat.findGreatest` to locate the
greatest `X`-point `≤ z`, whose successor lands in `[z, z+d]`.) -/
theorem EvGapLe.boundedGapsBy {X : Set ℕ} {d : ℕ} (hinf : X.Infinite) (h : EvGapLe X d) :
    BoundedGapsBy X d := by
  classical
  obtain ⟨N, hN⟩ := h
  obtain ⟨e₀, he₀X, hNe₀⟩ := hinf.exists_gt N
  have hNe₀' : N ≤ e₀ := le_of_lt hNe₀
  refine ⟨e₀, fun z hz => ?_⟩
  set P : ℕ → Prop := fun a => a ∈ X ∧ N ≤ a with hP
  set w := Nat.findGreatest P z with hw
  have hPe₀ : P e₀ := ⟨he₀X, hNe₀'⟩
  have hwe₀ : e₀ ≤ w := Nat.le_findGreatest hz hPe₀
  have hPw : P w := Nat.findGreatest_spec hz hPe₀
  have hwz : w ≤ z := Nat.findGreatest_le z
  obtain ⟨y, hyX, hwy, hyd⟩ := hN w hPw.1 hPw.2
  have hyz : z < y := by
    by_contra hle
    rw [not_lt] at hle
    have hPy : P y := ⟨hyX, le_trans hPw.2 (le_of_lt hwy)⟩
    have : y ≤ w := Nat.le_findGreatest hle hPy
    omega
  exact ⟨y, hyX, le_of_lt hyz, by omega⟩

/-- Covering bound ⟹ eventual gap bound (with one extra slack: a window `[x+1, x+1+C]` puts the next
`X`-point within `C+1` of `x`). -/
theorem BoundedGapsBy.evGapLe {X : Set ℕ} {C : ℕ} (h : BoundedGapsBy X C) :
    EvGapLe X (C + 1) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun x _ hxN => ?_⟩
  obtain ⟨y, hyX, hxy, hyC⟩ := hN (x + 1) (by omega)
  exact ⟨y, hyX, by omega, by omega⟩

/-- **Set-monotonicity of bounded gaps.** A syndetic subset forces its superset to have bounded gaps:
if `S ⊆ X` and every large window meets `S`, then every large window meets `X`. -/
theorem BoundedGapsBy.mono_set {S X : Set ℕ} {C : ℕ} (hsub : S ⊆ X) (h : BoundedGapsBy S C) :
    BoundedGapsBy X C := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun x hxN => ?_⟩
  obtain ⟨y, hyS, hxy, hyC⟩ := hN x hxN
  exact ⟨y, hsub hyS, hxy, hyC⟩

/-- A covering bound pins `Δ`: `BoundedGapsBy X C ⟹ Δ(X) ≤ C + 1`. Combined with `mono_set`, this is
the workhorse for bounding `Δ` of a set that contains a syndetic (covered) subset. -/
theorem BoundedGapsBy.delta_le {X : Set ℕ} {C : ℕ} (h : BoundedGapsBy X C) :
    Delta X ≤ (C + 1 : ℕ) :=
  (Delta_le_nat_iff X (C + 1)).mpr h.evGapLe

/-! ### Translation invariance of `Δ`

`Δ` only sees gaps, so it is invariant under translating the set. This is a fundamental property and
the precise tool the Prop 7 frontier needs (its covering of `3 × A` is built from translates
`aᵢ + (subset of 2 × A)`). -/

/-- Eventual gap bounds are invariant under translating the set by a constant. -/
lemma EvGapLe_image_add_iff {X : Set ℕ} {d : ℕ} (t : ℕ) :
    EvGapLe ((fun x => x + t) '' X) d ↔ EvGapLe X d := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun x hx hxN => ?_⟩
    obtain ⟨y, hy, hxy, hyd⟩ := hN (x + t) ⟨x, hx, rfl⟩ (by omega)
    obtain ⟨x', hx', hxe⟩ := hy
    have hxe' : x' + t = y := hxe
    exact ⟨x', hx', by omega, by omega⟩
  · rintro ⟨N, hN⟩
    refine ⟨N + t, ?_⟩
    rintro z ⟨x, hx, hxe⟩ hzN
    have hxe' : x + t = z := hxe
    obtain ⟨y, hy, hxy, hyd⟩ := hN x hx (by omega)
    exact ⟨y + t, ⟨y, hy, rfl⟩, by omega, by omega⟩

/-- **`Δ` is translation invariant.** `Δ(t + X) = Δ(X)` — translating a set leaves all its gaps,
hence its asymptotic gap functional, unchanged. -/
theorem Delta_image_add {X : Set ℕ} (t : ℕ) : Delta ((fun x => x + t) '' X) = Delta X :=
  Delta_congr (fun _d => EvGapLe_image_add_iff t)

/-! ### Bridge to the construction: `UnboundedGaps ⟹ Δ = ⊤`

This ties the faithful `Δ` to the construction core. The repo proves `UnboundedGaps (restrictedSums …)`
(arbitrarily long missing runs) for the `k ≥ 3` example; this lemma upgrades that to the faithful
statement `Δ(…) = +∞`. The argument is elementary: if some finite `d` eventually bounded the gaps,
then by `EvGapLe.boundedGapsBy` the set `X` would be `d`-dense beyond some point, so every missing run
would have bounded length — contradicting "arbitrarily long runs". -/

/-- **Faithful unbounded-gaps bridge.** An infinite set with arbitrarily long missing runs has
asymptotic gap functional `+∞`. -/
theorem Delta_eq_top_of_unboundedGaps {X : Set ℕ} (hinf : X.Infinite) (hub : UnboundedGaps X) :
    Delta X = ⊤ := by
  rw [Delta_eq_top_iff]
  rintro ⟨d, hd⟩
  obtain ⟨N, hN⟩ := hd.boundedGapsBy hinf
  -- beyond `N`, every window `[z, z+d]` meets `X`; contradict a missing run of length `N + d`
  obtain ⟨m, hm⟩ := hub (N + d)
  set z := max m N with hz
  obtain ⟨y, hyX, hzy, hyd⟩ := hN z (le_max_right m N)
  have hmy : m ≤ y := le_trans (le_max_left m N) hzy
  have hzmN : z ≤ m + N := by simp [hz]
  exact (hm y hmy (by omega)) hyX

/-- An infinite set `A` has an infinite restricted-sum set (every element of `A` is an order-1
restricted sum), so its `Δ` is a non-degenerate gap functional. -/
lemma restrictedSums_infinite {A : Set ℕ} {k : ℕ} (hk : 1 ≤ k) (hA : A.Infinite) :
    (restrictedSums A k).Infinite :=
  hA.mono (fun _a ha => mem_restrictedSums_single hk ha)

/-- Explicit membership in the 2-fold restricted sumset: a sum of two distinct elements of `A`. -/
lemma mem_restrictedSumset_two_iff {A : Set ℕ} {n : ℕ} :
    n ∈ restrictedSumset A 2 ↔ ∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ b + c = n := by
  constructor
  · rintro ⟨T, hTA, hcard, hsum⟩
    obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp hcard
    exact ⟨b, hTA (by simp), c, hTA (by simp), hbc, by rw [← hsum, Finset.sum_pair hbc]⟩
  · rintro ⟨b, hb, c, hc, hbc, rfl⟩
    refine ⟨{b, c}, ?_, Finset.card_pair hbc, Finset.sum_pair hbc⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨hb, hc⟩

/-- Explicit membership in the 3-fold restricted sumset: a sum of three pairwise-distinct elements. -/
lemma mem_restrictedSumset_three_iff {A : Set ℕ} {n : ℕ} :
    n ∈ restrictedSumset A 3 ↔
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c = n := by
  constructor
  · rintro ⟨T, hTA, hcard, hsum⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    refine ⟨a, hTA (by simp), b, hTA (by simp), c, hTA (by simp), hab, hac, hbc, ?_⟩
    rw [← hsum, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]; ring
  · rintro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, rfl⟩
    refine ⟨{a, b, c}, ?_, ?_, ?_⟩
    · simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨ha, hb, hc⟩
    · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    · rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton]; ring

/-- **Bounded extension (key step of HHP07 Proposition 5).** Any `h`-fold restricted sum extends to an
`(h+1)`-fold one by adding a *bounded* element: for any `(h+1)`-element subset `S ⊆ A`, the `h`-element
representation of `n` misses some `a ∈ S` (pigeonhole), so `n + a ∈ (h+1) × A` with `a ∈ S`. Taking `S`
the `h+1` smallest elements bounds the added amount by `max S − min S`, which is what makes
`Δ((h+1)×A) ≤ Δ(h×A) + (a_{h+1} − a₁)`. -/
lemma exists_extend {A : Set ℕ} {h : ℕ} {n : ℕ} (hn : n ∈ restrictedSumset A h)
    {S : Finset ℕ} (hSA : ↑S ⊆ A) (hScard : h < S.card) :
    ∃ a ∈ S, n + a ∈ restrictedSumset A (h + 1) := by
  obtain ⟨T, hTA, hTcard, hTsum⟩ := hn
  have hpos : 0 < (S \ T).card := by have := Finset.le_card_sdiff T S; omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff] at ha
  obtain ⟨haS, haT⟩ := ha
  refine ⟨a, haS, insert a T, ?_, ?_, ?_⟩
  · rw [Finset.coe_insert]; exact Set.insert_subset (hSA haS) hTA
  · rw [Finset.card_insert_of_notMem haT, hTcard]
  · rw [Finset.sum_insert haT, hTsum]; ring

/-- For infinite `A` the **exact** `l`-fold restricted sumset (`l ≥ 1`) is infinite: there are
arbitrarily large sums of `l` distinct elements (pick `l` distinct elements all above any bound). -/
lemma restrictedSumset_infinite {A : Set ℕ} {l : ℕ} (hl : 1 ≤ l) (hA : A.Infinite) :
    (restrictedSumset A l).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro M
  have hAinf : (A \ Set.Iic M).Infinite := hA.sdiff (Set.finite_Iic M)
  obtain ⟨T, hTsub, hTcard⟩ := hAinf.exists_subset_card_eq l
  obtain ⟨a, haT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have haM : M < a := by
    have := (hTsub haT).2; simp only [Set.mem_Iic, not_le] at this; exact this
  exact ⟨∑ x ∈ T, x, ⟨T, fun x hx => (hTsub hx).1, hTcard, rfl⟩,
    lt_of_lt_of_le haM (Finset.single_le_sum (fun i _ => Nat.zero_le i) haT)⟩

/-- A **cofinite** set has `Δ ≤ 1`: beyond the (finite) complement every two consecutive integers lie
in `X`, so gaps are `≤ 1`. (Turns a restricted-basis / basis cofiniteness fact into `Δ < ⊤`.) -/
lemma Delta_le_one_of_cofinite {X : Set ℕ} (h : {n | n ∉ X}.Finite) : Delta X ≤ 1 := by
  obtain ⟨M, hM⟩ := h.bddAbove
  refine (Delta_le_nat_iff X 1).mpr ⟨M + 1, fun x _ hx => ⟨x + 1, ?_, by omega, by omega⟩⟩
  by_contra hmem
  exact absurd (hM (show x + 1 ∈ {n | n ∉ X} from hmem)) (by omega)

/-! ### Faithful Theorem 1(i): `Δ(2 × A) ≤ 2` for a basis of order 2

The repo proves the `BoundedGapsBy` form (`erdos_880_k2`); here we record the same fact through the
faithful `Δ`, i.e. `Δ(restrictedSums A 2) ≤ 2`. The mechanism is the parity argument
(`odd_mem_restrictedSums_two`): far enough out, the odd member of `{x+1, x+2}` is a sum of two
distinct elements, giving every `x` a restricted-sum successor within `2`. -/

/-- **HHP07 Theorem 1(i), faithful form.** If `A` is an additive basis of order `2` then the gap
functional of its restricted-sum set is `≤ 2`: `Δ(restrictedSums A 2) ≤ 2`. -/
theorem Delta_restrictedSums_two_le (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    Delta (restrictedSums A 2) ≤ 2 := by
  obtain ⟨M, hM⟩ := hbasis.bddAbove
  have hbig : ∀ y, M < y → y ∈ sumsetLE A 2 := by
    intro y hy
    by_contra hmem
    exact absurd (hM hmem) (by omega)
  -- It suffices to exhibit `2` as an eventual gap bound.
  have : EvGapLe (restrictedSums A 2) 2 := by
    refine ⟨M + 1, fun x _ hxN => ?_⟩
    rcases Nat.even_or_odd x with he | ho
    · -- `x` even ⟹ `x + 1` odd, a sum of `≤ 2` distinct elements, within `2`
      exact ⟨x + 1, odd_mem_restrictedSums_two he.add_one (hbig _ (by omega)), by omega, by omega⟩
    · -- `x` odd ⟹ `x + 2` odd, a sum of `≤ 2` distinct elements, within `2`
      refine ⟨x + 2, odd_mem_restrictedSums_two ?_ (hbig _ (by omega)), by omega, by omega⟩
      rcases ho with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  exact (Delta_le_nat_iff _ 2).mpr this

/-! ### HHP07 Proposition 7 (non-construction), SHARP form: `Δ(3 × A) ≤ Δ(2 × A)`

The first genuinely-new HHP07 result about a *general* set `A` (not the construction), in the paper's
sharp form (no `+1`). The earlier one-sided `BoundedGapsBy` route lost a `+1` because it only gives a
member of `S` in `[z, z+d]` (possibly `= z`); the sharp bound needs a *strict-successor* cover
(`EvGapLe.cover`: beyond some `N`, every `w` has an `S`-point **strictly** above it within `d`), which
keeps the same `d`. With `m :=` the greatest `A`-element `≤ z − x₀` (`exists_greatest_mem_le`), two
cases on `z` vs `2m`: shift a sub-`m` 2-sum up by `m` (Case A), or shift a high 2-sum up by a *medium*
`A`-element probed near `2(d+x₀)`, with both its summands forced into `(a, m]` by the maximality of `m`
(Case B). The `2b ≥ m`/maximality doubling argument dodges ℕ division entirely. Aristotle-assisted
(job `aff5aa07`); verified in-kernel (`#print axioms` clean) then ported onto `restrictedSumset`. -/

/-- A nonempty subset `{a ∈ A | a ≤ b}` has a greatest element (`Nat.findGreatest`). The maximality
`∀ a ∈ A, a ≤ b → a ≤ m` replaces "the next enumerated element" with no `Nat.nth`. -/
lemma exists_greatest_mem_le {A : Set ℕ} (b : ℕ) (h : ∃ a ∈ A, a ≤ b) :
    ∃ m ∈ A, m ≤ b ∧ ∀ a ∈ A, a ≤ b → a ≤ m := by
  classical
  obtain ⟨a₀, ha₀A, ha₀b⟩ := h
  exact ⟨Nat.findGreatest (· ∈ A) b, Nat.findGreatest_spec ha₀b ha₀A,
    Nat.findGreatest_le b, fun a haA hab => Nat.le_findGreatest hab haA⟩

/-- **Strict-successor cover form of `EvGapLe`.** On an infinite `X`, an eventual gap bound `d` gives a
threshold `N` beyond which *every* integer `w` (not only members of `X`) has an `X`-point **strictly**
above it within `d`. The strict `<` (vs `BoundedGapsBy`'s `≤`) is exactly what keeps Prop 7's bound at
`d` with no `+1`. -/
lemma EvGapLe.cover {X : Set ℕ} {d : ℕ} (hX : X.Infinite) (h : EvGapLe X d) :
    ∃ N : ℕ, ∀ w, N ≤ w → ∃ s ∈ X, w < s ∧ s ≤ w + d := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨t, htX, htge⟩ := hX.exists_gt N
  obtain ⟨s₀, hs₀X, hs₀⟩ : ∃ s₀ ∈ X, N ≤ s₀ := ⟨t, htX, le_of_lt htge⟩
  refine ⟨s₀, fun w hw => ?_⟩
  induction' hw with w hw ih
  · obtain ⟨y, hyX, hy1, hy2⟩ := hN s₀ hs₀X hs₀
    exact ⟨y, hyX, hy1, hy2⟩
  · obtain ⟨s, hsX, hs1, hs2⟩ := ih
    rcases Nat.lt_or_ge (w + 1) s with hlt | hge
    · exact ⟨s, hsX, hlt, by omega⟩
    · -- `w < s ≤ w + 1` forces `s = w + 1`; its successor lands in `(w+1, w+1+d]`
      have hsN : N ≤ s := le_trans hs₀ (le_trans hw (le_of_lt hs1))
      obtain ⟨y, hyX, hy1, hy2⟩ := hN s hsX hsN
      exact ⟨y, hyX, by omega, by omega⟩

/-- Case A of the sharp covering: when `z + d ≤ 2m`, anchor the new 3-sum at the large element `m`.
A strict-cover 2-sum `s ∈ (z−m, z−m+d]` has `s ≤ m`, so both its summands are `< m`, distinct from
`m`; thus `m + s ∈ 3 × A` lands in `(z, z+d]`. -/
lemma prop7_caseA {A : Set ℕ} (hpos : ∀ a ∈ A, 0 < a) {d x₀ z m : ℕ}
    (hcov : ∀ w, x₀ ≤ w → ∃ s ∈ restrictedSumset A 2, w < s ∧ s ≤ w + d)
    (hmA : m ∈ A) (hmle : m + x₀ ≤ z) (hcase : z + d ≤ 2 * m) :
    ∃ t ∈ restrictedSumset A 3, z < t ∧ t ≤ z + d := by
  obtain ⟨s, hsD2, hs1, hs2⟩ := hcov (z - m) (by omega)
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_restrictedSumset_two_iff.mp hsD2
  have ha0 : 0 < a := hpos a ha
  have hb0 : 0 < b := hpos b hb
  -- `a + b ≤ (z − m) + d ≤ m` (from `z + d ≤ 2m`), so each summand `< m`
  refine ⟨m + a + b, mem_restrictedSumset_three_iff.mpr
    ⟨m, hmA, a, ha, b, hb, by omega, by omega, hab, by ring⟩, by omega, by omega⟩

/-- Case B of the sharp covering: when `2m < z + d` (a large gap above `m`), anchor at a *medium*
element `a` (`d + x₀ ≤ a < 3d + 2x₀`, with `2a + m ≤ z`) probed near `2(d+x₀)`. A strict-cover 2-sum
`s = p + q` near `z − a` has both summands in `(a, m]` — `≤ m` by maximality of `m`, `> a` from
`s > z − a` and `2a + m ≤ z` — so `a + p + q ∈ 3 × A` lands in `(z, z+d]`. -/
lemma prop7_caseB {A : Set ℕ} (hpos : ∀ a ∈ A, 0 < a) {d x₀ z m : ℕ}
    (hcov : ∀ w, x₀ ≤ w → ∃ s ∈ restrictedSumset A 2, w < s ∧ s ≤ w + d)
    (_hmA : m ∈ A) (hmle : m + x₀ ≤ z)
    (hmmax : ∀ a ∈ A, a + x₀ ≤ z → a ≤ m)
    (hmL : 7 * d + 4 * x₀ ≤ m)
    (hcase : 2 * m < z + d) :
    ∃ t ∈ restrictedSumset A 3, z < t ∧ t ≤ z + d := by
  -- the medium element `a`, taken as `max` of a 2-sum probed near `2(d+x₀)`
  obtain ⟨a, haA, hda, h2a, hau⟩ : ∃ a ∈ A, d + x₀ ≤ a ∧ 2 * a + m ≤ z ∧ a < 3 * d + 2 * x₀ := by
    obtain ⟨s, hsD2, hs⟩ := hcov (2 * (d + x₀)) (by omega)
    obtain ⟨b, hbA, c, hcA, hbc, rfl⟩ := mem_restrictedSumset_two_iff.mp hsD2
    have hb0 : 0 < b := hpos b hbA
    have hc0 : 0 < c := hpos c hcA
    rcases le_total b c with hle | hle
    · exact ⟨c, hcA, by omega, by omega, by omega⟩
    · exact ⟨b, hbA, by omega, by omega, by omega⟩
  obtain ⟨s, hsD2, hs1, hs2⟩ := hcov (z - a) (by omega)
  obtain ⟨p, hpA, q, hqA, hpq, rfl⟩ := mem_restrictedSumset_two_iff.mp hsD2
  -- both summands `≤ m` by maximality (each `≤ z − x₀`), and `> a` from the lower cover bound
  have hple : p ≤ m := hmmax p hpA (by omega)
  have hqle : q ≤ m := hmmax q hqA (by omega)
  refine ⟨a + p + q, mem_restrictedSumset_three_iff.mpr
    ⟨a, haA, p, hpA, q, hqA, by omega, by omega, hpq, by ring⟩, by omega, by omega⟩

/-- **HHP07 Proposition 7, sharp form.** For every infinite set of positive integers `A`,
`Δ(3 × A) ≤ Δ(2 × A)`. The strict-successor cover `EvGapLe.cover` transfers an eventual gap bound `d`
of the 2-distinct-sumset to the 3-distinct-sumset with the *same* `d`, via Cases A/B above. -/
theorem Delta_restrictedSumset_three_le (A : Set ℕ) (hA : A.Infinite) (hpos : ∀ a ∈ A, 0 < a) :
    Delta (restrictedSumset A 3) ≤ Delta (restrictedSumset A 2) := by
  apply Delta_le_of_evGapLe_imp
  intro d h2
  have hD2inf : (restrictedSumset A 2).Infinite := restrictedSumset_infinite (by norm_num) hA
  obtain ⟨x₀, hcov⟩ := h2.cover hD2inf
  obtain ⟨aL, haLA, haL⟩ := hA.exists_gt (7 * d + 4 * x₀)
  -- `EvGapLe (3 × A) d` via the uniform strict cover beyond `aL + x₀`
  refine ⟨aL + x₀, fun z _ hz => ?_⟩
  obtain ⟨m, hmA, hmle', hmmax'⟩ := exists_greatest_mem_le (z - x₀) ⟨aL, haLA, by omega⟩
  have hmle : m + x₀ ≤ z := by omega
  have hmmax : ∀ a ∈ A, a + x₀ ≤ z → a ≤ m := fun a haA ha => hmmax' a haA (by omega)
  have hmL : 7 * d + 4 * x₀ ≤ m := le_trans (le_of_lt haL) (hmmax aL haLA (by omega))
  by_cases hcase : z + d ≤ 2 * m
  · exact prop7_caseA hpos hcov hmA hmle hcase
  · exact prop7_caseB hpos hcov hmA hmle hmmax hmL (by omega)

/-! ### HHP07 Proposition 5 (non-construction): gap-finiteness propagates upward in the fold count

The exact-fold form of Prop 5 (and the general-`h` generalization of Prop 7). The covering
`BoundedGapsBy (h×A) d → BoundedGapsBy ((h+1)×A) (d+M)` comes from `exists_extend`: a `h×A` point `n`
near `z` extends to `n + a ∈ (h+1)×A` with `a ∈ S` bounded by `M` (`S` any `(h+1)`-subset of `A`), and
`n + a ∈ [z, z+d+M]`. Hence `Δ((h+1)×A) ≤ Δ(h×A) + (M+1)`, so finiteness of `Δ(h₀×A)` propagates to all
`h ≥ h₀`. -/

/-- The Prop 5 covering step: `EvGapLe (h×A) d ⟹ EvGapLe ((h+1)×A) (d + M + 1)`, where `M` bounds an
`(h+1)`-element subset `S ⊆ A`. -/
lemma evGapLe_restrictedSumset_succ {A : Set ℕ} {h M d : ℕ} (hA : A.Infinite) (hh : 1 ≤ h)
    {S : Finset ℕ} (hSA : ↑S ⊆ A) (hScard : h < S.card) (hSM : ∀ a ∈ S, a ≤ M)
    (hd : EvGapLe (restrictedSumset A h) d) :
    EvGapLe (restrictedSumset A (h + 1)) (d + M + 1) := by
  have hbg : BoundedGapsBy (restrictedSumset A h) d :=
    hd.boundedGapsBy (restrictedSumset_infinite hh hA)
  have hbg' : BoundedGapsBy (restrictedSumset A (h + 1)) (d + M) := by
    obtain ⟨N, hN⟩ := hbg
    refine ⟨N, fun z hz => ?_⟩
    obtain ⟨n, hnDh, hzn, hnd⟩ := hN z hz
    obtain ⟨a, haS, hext⟩ := exists_extend hnDh hSA hScard
    have ha : a ≤ M := hSM a haS
    exact ⟨n + a, hext, by omega, by omega⟩
  exact hbg'.evGapLe

/-- **HHP07 Proposition 5, quantitative.** `Δ((h+1) × A) ≤ Δ(h × A) + (M + 1)` for any `(h+1)`-element
subset `S ⊆ A` bounded by `M` (taking `S` the `h+1` smallest elements gives the paper's `a_{h+1}−a₁`). -/
theorem Delta_restrictedSumset_succ_le {A : Set ℕ} {h M : ℕ} (hA : A.Infinite) (hh : 1 ≤ h)
    {S : Finset ℕ} (hSA : ↑S ⊆ A) (hScard : h < S.card) (hSM : ∀ a ∈ S, a ≤ M) :
    Delta (restrictedSumset A (h + 1)) ≤ Delta (restrictedSumset A h) + (M + 1) :=
  Delta_le_add_of_evGapLe_imp (M + 1)
    (fun _d hd => evGapLe_restrictedSumset_succ hA hh hSA hScard hSM hd)

/-- One-step finiteness propagation: `Δ(h × A) < +∞ ⟹ Δ((h+1) × A) < +∞`. -/
theorem Delta_restrictedSumset_lt_top_succ {A : Set ℕ} {h : ℕ} (hA : A.Infinite) (hh : 1 ≤ h)
    (hfin : Delta (restrictedSumset A h) < ⊤) :
    Delta (restrictedSumset A (h + 1)) < ⊤ := by
  obtain ⟨S, hSA, hScard⟩ := hA.exists_subset_card_eq (h + 1)
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hScard]; omega
  rw [Delta_lt_top_iff] at hfin ⊢
  obtain ⟨d, hd⟩ := hfin
  exact ⟨_, evGapLe_restrictedSumset_succ (M := S.max' hSne) hA hh hSA (by omega)
    (fun a ha => Finset.le_max' S a ha) hd⟩

/-- **HHP07 Proposition 5 (exact-fold form).** For any infinite set of positive integers `A`, if
`Δ(h₀ × A)` is finite then `Δ(h × A)` is finite for every `h ≥ h₀` (with `1 ≤ h₀`). This is the genuine
paper statement (allowing more pairwise-distinct summands cannot make the gaps unbounded once they are
bounded), and the general-`h` generalization of Proposition 7. -/
theorem Delta_restrictedSumset_lt_top_of_le {A : Set ℕ} {h₀ h : ℕ} (hA : A.Infinite) (hh₀ : 1 ≤ h₀)
    (hle : h₀ ≤ h) (hfin : Delta (restrictedSumset A h₀) < ⊤) :
    Delta (restrictedSumset A h) < ⊤ := by
  induction h with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge h₀ (k + 1) with hlt | hge
    · exact Delta_restrictedSumset_lt_top_succ hA (by omega) (ih (by omega))
    · have : h₀ = k + 1 := by omega
      rwa [← this]

end LeanGallery.Combinatorics.Erdos880
