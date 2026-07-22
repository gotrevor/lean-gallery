# `tools/aristotle/` — Aristotle job submissions

Provenance artifacts, **not part of the `lake build`**. Each subdirectory is one self-contained problem
that was submitted to **Harmonic's Aristotle** auto-formalization system: a `Problem.lean` stating a
single lemma with the proof left as `sorry`, plus a minimal toolchain/manifest so Aristotle can build it
in isolation.

The workflow: hard, self-contained lemmas were factored out and handed to Aristotle; whatever it
returned was then **re-checked by the Lean kernel** and ported into `src/` only if it verified. Nothing
in the build is trusted on Aristotle's (or any tool's) say-so — the whole development is axiom-clean
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` everywhere).

## What Aristotle closed (kernel-verified, ported into `src/Erdos482/Stoll.lean`)

Mostly the pair-5 Diophantine infrastructure:
- `sqrt2_badly_approximable` — `1/(3q) ≤ |q√2 − p|` (the quadratic-irrational lower bound that keeps the
  pair-5 step margin positive for all `j`).
- `fract_two_mul`, `fract_two_mul_branch` — the doubling-map / fractional-part branch identities.
- `fract_sqrt2_pow_ne_half` — `{√2·2ⁿ} ≠ ½`.
- `pair5_band_branch` — the two-branch band identity feeding `pair5_band_fails_below/above_half`.
- `vv_one_le_and_mono` — `vv ε ≥ 1` and monotonicity.

## What Aristotle could NOT close (proved by hand instead)

- `thm13_closed` — St05 Theorem 1.3's joint closed-form induction. The monolithic job (`e0240fef`)
  stalled at ~9%; it was decomposed into four angles (`eo_floor`, `eo_ineq`, `closed_assembly`,
  `closed_full` — see [`JOBS-thm13closed.md`](JOBS-thm13closed.md)) which also did not land, and the
  result was ultimately proved locally in [`../../src/Erdos482/General/Thm13Closed.lean`](../../src/Erdos482/General/Thm13Closed.lean).
  The raw export of that job is in [`../../archive/aristotle/`](../../archive/aristotle/).

The remaining subdirs (`bandmargin`, `bridge`, `digit_recon`, `mantissa`, `thm12_*`, …) are other jobs
from the same exploration, kept for the record.
