# HANDOFF — Erdős ports done (c-yolo box, 2026-06-28)

The 3 remaining Erdős formalizations are ported into the gallery and **committed on `main`**
(direct commits to main are this repo's convention — see `.githooks/pre-commit`). I'm network-isolated,
so **nothing is pushed** — that's your half.

## What landed (4 commits on `main`, each green via the pre-commit `lake build` gate)

- `a437ac5` **#1050** → `NumberTheory/Erdos1050` — `erdos_1050_irrational` (∑ 1/(2ⁿ−3) irrational, Borwein)
  + the bonus axiom-free Borwein Thm 1 `borwein_thm1_abs`. Excluded `GeneralThm2.lean` (axiom
  `borwein_approximants_alt`).
- `88d9c10` **#880** → `Combinatorics/Erdos880` — `erdos_880` (k≥3 unbounded) + `erdos_880_order_two`
  (k=2). Excluded the conditional HHP07 Thm 10 subtree (`Thm10.lean` axiom `kneser_density_residue`,
  `DensityKneser.lean`); pruned Statement/AxiomGuard refs; kept the standalone kernel-pure Kneser
  e-transform dev. The kept `AxiomGuard.lean` build-checks ~25 theorems.
- `7aa96af` **#482** → `NumberTheory/Erdos482` — `graham_pollak` (√2-digit recurrence) +
  `erdos482_resolution` (full generality) + `cor33_unconditional`. Full 56-file lib, no exclusions.
- `98a4692` **fixup** — silenced the `ring`→`ring_nf` info-level "Try this" build-log diagnostics in
  the #1050/#482 files (see Notes).

All headlines verified `#print axioms` = `[propext, Classical.choice, Quot.sound]`. Wired into
`LeanGallery.lean`, `README.md`, and the `ci.yml` axiom-clean gate (the `#print axioms` CI gate now
covers all 5 Erdős results — 12 headlines total; gate run locally, passes 12/12).

## Your steps (from `ERDOS-PORT-HANDOFF.md` §"When all 3 build green")

1. `git push` `main`; `gh run watch` the CI run to green.
2. Open **formal-conjectures** PRs for all 5 (#403, #482, #1213, #1050, #880) — CLA signed 2026-06-28.
3. Delete `ERDOS-PORT-HANDOFF.md` (and this file) once merged.

## Notes
- The build log is now **info-clean**: the `ring`→`ring_nf` "Try this" diagnostics that used to print
  during `lake build` (`Erdos1050/QLagrange.lean`, `Erdos482/General/{Equidistribution,MultidimWeyl}`)
  were silenced in `98a4692` (`ring` was already soft-failing into ring_nf normalization). Verified by
  re-elaborating all 101 gallery modules: zero "Try this" diagnostics remain.
- The CI gate greps single-line `#print axioms` output; `erdos482_resolution`'s long `.General.`-qualified
  name wraps past 100 cols, so it is **not** in the gate (it's covered by the full build + its documented
  Statement re-export). The two gated #482 headlines (`graham_pollak`, `cor33_unconditional`) print
  single-line.
- `HYDRA-TERMINATION-SPEC.md` (untracked) predates this work — left untouched.
