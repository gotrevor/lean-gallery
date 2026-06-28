/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.NumberTheory.Erdos482.Main
import LeanGallery.NumberTheory.Erdos482.Stoll
import LeanGallery.NumberTheory.Erdos482.General.Erdos482General
import LeanGallery.NumberTheory.Erdos482.General.St06Example
import LeanGallery.NumberTheory.Erdos482.General.St06Thm31
import LeanGallery.NumberTheory.Erdos482.General.St06Thm33
import LeanGallery.NumberTheory.Erdos482.General.St06Thm34
import LeanGallery.NumberTheory.Erdos482.General.St06Cor35
import LeanGallery.NumberTheory.Erdos482.General.GeneralTorusFinish
import LeanGallery.NumberTheory.Erdos482.General.BaseGFinish

/-!
# `Statement.lean` — the single auditable trust surface

For a formalization the **statements** are the silent-failure axis: `#print axioms` certifies that a
*proof* uses only the trust base, but it says nothing about whether the *theorem statement* says what the
paper says. This file collects every headline of the development in one place as `alias`es, each carrying:

* a **citation** (which paper / which self-generated result), and
* a **plain-English claim** of what the proposition asserts,

sitting directly next to the machine-checked re-export. A referee can audit the entire trust surface here
— the `alias` re-exports the *exact* type of the underlying theorem (no transcription), and the build
**fails** if any headline is renamed, removed, or has its statement changed. Every headline below is
`#print axioms`-clean: it depends only on `[propext, Classical.choice, Quot.sound]` (0 math axioms,
re-verified on the 2026-06-14 deep-reflection lap; see `REFLECTION.md`).

Hover any `statement_*` name to read its full Lean proposition.
-/

namespace LeanGallery.NumberTheory.Erdos482.Statement

/-! ## I. The headline — Graham–Pollak / Erdős #482 (digits of √2) -/

/-- **Erdős #482 / Graham–Pollak (the headline).** For `u 0 = 1`, `u (n+1) = ⌊√2·(u n + ½)⌋`, the
difference `u(2n+1) − 2·u(2n−1)` equals the `n`-th binary digit of `√2` (`binDigit`, the standard
floor-formula bit). The whole Graham–Pollak sequence reads off the binary expansion of `√2`. -/
alias statement_graham_pollak := LeanGallery.NumberTheory.Erdos482.graham_pollak

/-- **Canonical form** of the headline against mathlib's `Real.digits`: the Graham–Pollak difference is
literally the `(n−1)`-th base-2 digit of `Int.fract √2`. This is the bridge that anchors `binDigit` to the
standard library notion of a digit. -/
alias statement_graham_pollak_digits := LeanGallery.NumberTheory.Erdos482.graham_pollak_digits

/-- **Stoll arXiv:0902.4168, Cor 3.3 (the showcase constant).** The same recurrence, run with
`ε = 1 − π²/e³`, reads off the binary digits of `759250125·√2` — Stoll's headline numerical example. -/
alias statement_cor33_unconditional := LeanGallery.NumberTheory.Erdos482.cor33_unconditional

/-! ## II. Erdős #482 resolved in full generality — Stoll [St05] -/

/-- **Stoll [St05], the general resolution.** For every real `w > 0` and every base `g ≥ 2` there is an
explicit Graham–Pollak-type recurrence whose even-index Graham–Pollak differences read off the base-`g`
digits of `w`. This is the elementary resolution of Erdős #482 in full generality. -/
alias statement_erdos482_resolution := LeanGallery.NumberTheory.Erdos482.General.erdos482_resolution

/-! ## III. The sister paper — Stoll, *Acta Arith.* 125 (2006), 89–100 (St06) -/

/-- **St06, Example 1.1.** A negative-coefficient `π`/`e` recurrence whose Graham–Pollak difference
`su(2n) − 3·su(2n−2)` reads off the base-3 digits of `e` (`Real.digits e 3 (n−1)`). The
transcendental-in-odd-base showcase the sequence is OEIS-tagged to. -/
alias statement_st06_example11 := LeanGallery.NumberTheory.Erdos482.General.st06_example11_ternary_e

/-- **St06, Theorem 3.1 (the 3-parameter family; representative cone 𝒟₂).** For the `(m,l,k)` family with
`m ≥ 1`, an explicit recurrence's Graham–Pollak difference equals the base-`g` digit of `w`, over the full
corrected offset interval `1 + γ ≤ ε < δ`. (All 12 sub-subcones are formalized in `St06Thm31.lean`; this
is the cone containing Example 1.1.) -/
alias statement_st06_thm31 := LeanGallery.NumberTheory.Erdos482.General.st06_thm31_d2m_digits

/-- **St06, Theorem 3.3 (binary family 1).** Over the full symmetric ε-interval
`½ ± (2l+1)/(2(2m+1))`, the recurrence reads off the binary digits of `w`. -/
alias statement_st06_thm33 := LeanGallery.NumberTheory.Erdos482.General.st06_thm33_digits

/-- **St06, Theorem 3.4 (binary family 2), genuine full symmetric interval.** Over every
`ε ∈ ½ ± (m−l+½)/D₁` (`ε` on the a-step — uniform over all `t`, NOT the swapped b-step variant), the
recurrence reads off the binary digits of `w`. This is the corrected faithful statement (the prior
"only ε=½ obstruction" was a swapped-recurrence artifact; see STATUS / 2026-06-13 findings). -/
alias statement_st06_thm34 := LeanGallery.NumberTheory.Erdos482.General.st06_thm34_digits_eps

/-- **St06, Corollary 3.5 (Beatty unification).** The Graham–Pollak recurrence `su √2 √2 ½ ½ n` started at
any `n > 0` reads off the binary digits of `r·√2` for the unique `r ≥ 1` fixed by which Beatty sequence
contains `n` — unifying the Borwein–Bailey examples. -/
alias statement_st06_cor35 := LeanGallery.NumberTheory.Erdos482.General.st06_cor35

/-! ## IV. The self-generated impossibility frontier (complete & axiom-clean; not from a paper)

The precise sense in which the Graham–Pollak / Stoll digit-extraction recurrence is **special to degree 2**:
for `α = g^{1/d}` with `d ≥ 3`, *no* floor recurrence `v_{k+1} = ⌊α(v_k + c_k)⌋` (arbitrary real schedule
`c`) can read a real `W`'s base-`g` digits, for **almost every** `W`. The fixed-`W` version is a famous
**open problem** (Mahler's 3/2 / lacunary equidistribution at a fixed seed) and is *not* claimed. -/

/-- **Uniform degree-`d` impossibility (base 2), every `d ≥ 3`.** For almost every real `W`, no
degree-`d` schedule `c` makes the `d`-step floor map read `W`'s base-2 digits: for every `c` there is a
step `n` whose extracted digit leaves `{0,1}`. (`d = 2` is exactly the *solvable* Graham–Pollak case; the
obstruction begins at `d = 3`.) -/
alias statement_ae_no_dStep_reads_base_two := LeanGallery.NumberTheory.Erdos482.General.ae_no_dStep_schedule_reads_base_two

/-- **Uniform impossibility for every base `g ≥ 2` (prime degree `d`, perfect powers included).** For
almost every `W`, no degree-`d` schedule reads `W`'s base-`g` digits, whenever `d` is prime, `g` is not a
perfect `d`-th power, and the window-escape bound `g^{1/d} < 2g/(g+1)` holds (always achievable by taking
`d` a large enough prime). Covers perfect-power bases (`g = 4, 8, 9, …`) via the Kummer route. -/
alias statement_ae_no_dStep_reads_base_g := LeanGallery.NumberTheory.Erdos482.General.ae_no_dStep_schedule_reads_base_g_all

/-- **Fully unconditional concrete instance** (`g = 3`, `d = 3`, `α = 3^{1/3}`): for almost every `W`, no
degree-3 schedule reads `W`'s base-3 digits — every hypothesis discharged. -/
alias statement_ae_no_dStep_reads_base_three := LeanGallery.NumberTheory.Erdos482.General.ae_no_dStep_schedule_reads_base_three

end LeanGallery.NumberTheory.Erdos482.Statement
