/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos1050

/-!
# Erdős #1050 — comparator SOLUTION

Discharges every `sorry` in `Challenge.lean` by delegating to the real development. The one
definition (`S`) is repeated **verbatim** from the challenge (comparator requires that every
declaration appearing in a statement be identical in both environments), and each theorem is closed
by the corresponding gallery result.

This file is *not* part of the audit surface — `Challenge.lean` is. Comparator's job is to prove
that whatever happens in here really did establish the challenge's statements.

Note the gallery module imported here also carries the **open** [Er88c] conjecture
`erdos_1050.variants.transcendental` (a deliberate `sorry`, pinned by `#guard_msgs`). It is not in
the challenge and no statement below depends on it — the only theorem that mentions it takes it as
a hypothesis (`…implies_erdos_1050`), so every proof here stays axiom-clean.
-/

namespace Erdos1050

/-- Verbatim from `Challenge.lean` — comparator checks the two are the same declaration. -/
noncomputable def S : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)

theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050

theorem erdos_1050_irrational : Irrational S :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050_irrational

theorem borwein_thm1_abs (q : ℤ) (hq : 2 ≤ |q|) (c : ℚ) (hc0 : c ≠ 0)
    (hcn : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) :=
  LeanGallery.NumberTheory.Erdos1050.borwein_thm1_abs q hq c hc0 hcn

theorem erdos_1050_borwein_general (q : ℤ) (hq : 2 ≤ |q|) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (r : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050_borwein_general q hq r hr hne

theorem erdos_1050.variants.two_pow_sub_one :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one

theorem erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) =
      ∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series

theorem erdos_1050.variants.two_pow_sub_one.divisor_count_series_irrational :
    Irrational (∑' n : ℕ, ((n + 1).divisors.card : ℝ) / (2 : ℝ) ^ (n + 1)) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one.divisor_count_series_irrational

theorem erdos_1050.variants.borwein (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0)
    (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ))) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.borwein q hq r hr hne

theorem erdos_1050.variants.transcendental.implies_erdos_1050
    (h : ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, 1 ≤ n → t ≠ -(2 : ℤ) ^ n) →
      Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + (t : ℝ)))) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) :=
  LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.transcendental.implies_erdos_1050 h

end Erdos1050
