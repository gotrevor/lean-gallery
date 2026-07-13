/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import LeanGallery.Logic.Goodstein.Statement

/-!
# Goodstein's theorem — comparator SOLUTION

Discharges the `sorry` in `Challenge.lean` by delegating to the real development. The three
definitions (`base`, `bump`, `goodsteinSeq`) are repeated **verbatim** from the challenge
(comparator requires that every declaration appearing in a statement be identical in both
environments), and the headline is closed by `LeanGallery.Logic.Goodstein.goodstein_terminates`.

This file is *not* part of the audit surface — `Challenge.lean` is. Comparator's job is to prove
that whatever happens in here really did establish the challenge's statement.

## Why the delegation is not a one-liner 🔧

`bump` is defined by well-founded recursion, and Lean marks such definitions **irreducible**. So the
challenge's `Goodstein.bump` and the gallery's `LeanGallery.Logic.Goodstein.bump` — same body,
different constants — are not interchangeable by `rfl`/unification at default transparency, and a
bare `exact LeanGallery.Logic.Goodstein.goodstein_terminates m` cannot be expected to elaborate.
Instead the two copies are bridged **propositionally**: `bump_eq` proves them equal pointwise (by
strong induction on `n`, unfolding both through their equation lemmas), `goodsteinSeq_eq` lifts that
along the sequence recursion, and the headline transports across it. Nothing here is defeq-fragile.

`import Mathlib` is deliberate: it makes this environment a superset of the challenge's, so the
repeated definitions elaborate against the same instances and simp set (the gallery's own
`@[simp]` lemmas — `toOrdinal_zero`, `LeanGallery.Logic.Goodstein.bump_zero` — mention constants
that do not occur in the termination goals below, so they cannot perturb them).
-/

namespace Goodstein

/-! ### The definitions, verbatim from `Challenge.lean`

Comparator checks that these are the *same declarations* in both environments. -/

/-- Verbatim from `Challenge.lean`. -/
def base (k : ℕ) : ℕ := k + 2

/-- Verbatim from `Challenge.lean`. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- Verbatim from `Challenge.lean`. -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => bump (base k) (goodsteinSeq m k) - 1

/-! ### Transfer to the gallery's definitions

The challenge's copies are distinct constants from the gallery's, so they are related
propositionally rather than by unification (see the module doc). -/

/-- The challenge's `base` is the gallery's (both are `k + 2`; a plain definition, so `rfl`). -/
private theorem base_eq (k : ℕ) : base k = LeanGallery.Logic.Goodstein.base k := rfl

/-- The challenge's `bump` agrees with the gallery's, pointwise.

Proved by strong induction on `n`, run as ordinary induction on a bound `N` so the proof does not
depend on the case tags of any strong-recursion principle. Both sides are unfolded once through
their equation lemmas; the recursive arguments (`Nat.log b n` and `n % b ^ Nat.log b n`) are below
`n` by exactly the two facts that justified the original well-founded recursion. -/
private theorem bump_eq (b n : ℕ) : bump b n = LeanGallery.Logic.Goodstein.bump b n := by
  have H : ∀ N n, n < N → bump b n = LeanGallery.Logic.Goodstein.bump b n := by
    intro N
    induction N with
    | zero => intro n hn; exact absurd hn (by omega)
    | succ N ih =>
      intro n hn
      rw [bump.eq_def, LeanGallery.Logic.Goodstein.bump.eq_def]
      by_cases h : n = 0
      · subst h; simp
      · have hb : 0 < b ^ Nat.log b n := by
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · subst hb0; simp [Nat.log_zero_left]
          · exact Nat.pow_pos hbpos
        have hlog : Nat.log b n < n := Nat.log_lt_self b h
        have hmod : n % b ^ Nat.log b n < n :=
          lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)
        have hnN : n ≤ N := by omega
        -- `simp only` re-instantiates per occurrence, so one `dif_neg h` discharges the `dite`
        -- on *both* sides; the two `ih`s then align the recursive calls and close by `rfl`.
        simp only [dif_neg h, ih _ (lt_of_lt_of_le hlog hnN),
          ih _ (lt_of_lt_of_le hmod hnN)]
  exact H (n + 1) n (by omega)

/-- The challenge's Goodstein sequence agrees with the gallery's, term by term. -/
private theorem goodsteinSeq_eq (m k : ℕ) :
    goodsteinSeq m k = LeanGallery.Logic.Goodstein.goodsteinSeq m k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show bump (base k) (goodsteinSeq m k) - 1
        = LeanGallery.Logic.Goodstein.bump (LeanGallery.Logic.Goodstein.base k)
            (LeanGallery.Logic.Goodstein.goodsteinSeq m k) - 1
    rw [ih, bump_eq, base_eq]

/-! ### The headline -/

theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0 := by
  obtain ⟨N, hN⟩ := LeanGallery.Logic.Goodstein.goodstein_terminates m
  exact ⟨N, (goodsteinSeq_eq m N).trans hN⟩

end Goodstein
