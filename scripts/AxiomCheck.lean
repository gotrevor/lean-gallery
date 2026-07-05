/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Logic.Goodstein.Statement
import LeanGallery.Logic.Hydra.Statement
import LeanGallery.NumberTheory.Erdos403.Statement
import LeanGallery.Combinatorics.Erdos1213.Statement
import LeanGallery.NumberTheory.Erdos1050
import LeanGallery.Combinatorics.Erdos880.Statement
import LeanGallery.NumberTheory.Erdos482.Statement

/-!
# Axiom audit — the reference point of truth

`#print axioms` for every headline theorem in the gallery, each wrapped in `#guard_msgs`
asserting the exact expected axiom set: the standard mathlib triple
`[propext, Classical.choice, Quot.sound]` — i.e. no `sorry` (`sorryAx`), no custom/cheat
axioms. This is the authoritative "does the repo prove the right thing, honestly" check.

Because each `#print axioms` is guarded, any drift — a new axiom, a `sorry`, or a
renamed/removed theorem — makes THIS FILE fail to elaborate. On success the guards
consume their messages, so a clean run is silent:

    lake env lean scripts/AxiomCheck.lean   # no output + exit 0 = all clean

CI (`.github/workflows/ci.yml`, job `axioms`) runs exactly that and gates everything
downstream on the exit code. To add a headline theorem: add its `Statement` import above
and a guarded `#print axioms` block below (copy the printed triple into the expected
`info:` line). This file is the single source of truth for the headline set — the workflow
only checks it is well-formed (one guard per print), so there is no count to bump. The guards use
`whitespace := lax` so a long qualified name that the pretty-printer wraps across lines
still matches the single-line expected triple.
-/

-- Logic
/-- info: 'LeanGallery.Logic.Goodstein.goodstein_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.Logic.Goodstein.goodstein_terminates

/-- info: 'LeanGallery.Logic.Hydra.hydra_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.Logic.Hydra.hydra_terminates

-- Erdős — number theory & combinatorics
/-- info: 'LeanGallery.NumberTheory.Erdos403.erdos_403_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos403.erdos_403_finite

/-- info: 'LeanGallery.NumberTheory.Erdos403.erdos_403_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos403.erdos_403_sharp

/-- info: 'LeanGallery.Combinatorics.Erdos1213.erdos_1213' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.Combinatorics.Erdos1213.erdos_1213

/-- info: 'LeanGallery.Combinatorics.Erdos1213.erdos_1213_f_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.Combinatorics.Erdos1213.erdos_1213_f_finite

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050_irrational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050_irrational

/-- info: 'LeanGallery.NumberTheory.Erdos1050.borwein_thm1_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.borwein_thm1_abs

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one.eq_divisor_count_series

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one.divisor_count_series_irrational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.two_pow_sub_one.divisor_count_series_irrational

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050_borwein_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050_borwein_general

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.borwein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.borwein

/-- info: 'LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.transcendental.implies_erdos_1050' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050.variants.transcendental.implies_erdos_1050

/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.Combinatorics.Erdos880.erdos_880

/-- info: 'LeanGallery.Combinatorics.Erdos880.erdos_880_order_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.Combinatorics.Erdos880.erdos_880_order_two

/-- info: 'LeanGallery.NumberTheory.Erdos482.graham_pollak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos482.graham_pollak

/-- info: 'LeanGallery.NumberTheory.Erdos482.cor33_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos482.cor33_unconditional

/-- info: 'LeanGallery.NumberTheory.Erdos482.General.erdos482_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanGallery.NumberTheory.Erdos482.General.erdos482_resolution
