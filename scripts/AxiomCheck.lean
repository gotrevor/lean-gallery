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

`#print axioms` for every headline theorem in the gallery. Each must report exactly the
standard mathlib triple `[propext, Classical.choice, Quot.sound]` — i.e. no `sorry`, no
custom/cheat axioms. This is the authoritative "does the repo prove the right thing,
honestly" check.

Run it locally exactly as CI does:

    lake env lean scripts/AxiomCheck.lean

CI (`.github/workflows/ci.yml`, job `axioms`) runs this file and fails unless all 13 lines
print that triple. To add a headline theorem: add its `Statement` import above, add a
`#print axioms` line below, and bump the expected count in the workflow's gate.
-/

-- Logic
#print axioms LeanGallery.Logic.Goodstein.goodstein_terminates
#print axioms LeanGallery.Logic.Hydra.hydra_terminates

-- Erdős — number theory & combinatorics
#print axioms LeanGallery.NumberTheory.Erdos403.erdos_403_finite
#print axioms LeanGallery.NumberTheory.Erdos403.erdos_403_sharp
#print axioms LeanGallery.Combinatorics.Erdos1213.erdos_1213
#print axioms LeanGallery.Combinatorics.Erdos1213.erdos_1213_f_finite
#print axioms LeanGallery.NumberTheory.Erdos1050.erdos_1050_irrational
#print axioms LeanGallery.NumberTheory.Erdos1050.borwein_thm1_abs
#print axioms LeanGallery.Combinatorics.Erdos880.erdos_880
#print axioms LeanGallery.Combinatorics.Erdos880.erdos_880_order_two
#print axioms LeanGallery.NumberTheory.Erdos482.graham_pollak
#print axioms LeanGallery.NumberTheory.Erdos482.cor33_unconditional
#print axioms LeanGallery.NumberTheory.Erdos482.General.erdos482_resolution
