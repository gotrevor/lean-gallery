# Upstream brief — the mathlib-absent equidistribution / Weyl / Borel-normality layer

*Written 2026-06-14 (deep-reflection lap, consolidation item 2). This is a PR-prep inventory, not a
refactor. It crystallizes the most valuable **reusable byproduct** of the erdos-482 development: a
self-contained build of classical metric equidistribution that mathlib currently lacks. The actual
mathlib PR must be driven by Trevor (subject expert) with disclosure + the `LLM-generated` label per
`reference/2026-06-07-mathlib-ai-contribution-policy.md`; this file is the brief that de-risks it.*

## Why this is worth upstreaming

Reference note `reference/2026-06-14-mathlib-equidistribution-geometric-gap.md` (grepped against the
~2026-06 mathlib pin): the **measure-theoretic Weyl/Koksma equidistribution** machinery is **not in
mathlib**. mathlib has only the *ergodic-theory* facts (`AddCircle.ergodic_zsmul`, irrational-rotation
ergodicity in `Dynamics/Ergodic/`) — which give "a.e. starting point" via Birkhoff but **no Weyl
criterion, no Borel normality as an equidistribution statement, no multidim torus criterion, no
Davenport–Erdős–LeVeque L² lemma**. This development built all of it from scratch, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`). These are textbook-classical, general-interest, and
reusable far beyond Erdős #482.

## What we have (declaration · file · statement)

### A. Weyl's equidistribution criterion (1-D, `ℝ/ℤ`)
| decl | file | statement |
|---|---|---|
| `IsEquidistributed` | `General/Equidistribution.lean` | `x : ℕ → ℝ/ℤ` equidistributed ⇔ Cesàro means of every continuous test fn → its integral |
| `integral_fourier_eq` | `Equidistribution.lean` | `∫ fourier k = δ_{k,0}` over Haar `ℝ/ℤ` |
| `norm_cesaro_le` | `Equidistribution.lean` | `‖(1/N)∑_{n<N} f(xₙ)‖ ≤ ‖f‖` (uniform bound; any `CompactSpace` domain) |
| **`weyl_criterion`** | `Equidistribution.lean` | **all nonzero Weyl sums Cesàro→0 ⇒ `IsEquidistributed`** — via `Submodule.span_induction` over the dense Fourier span (Stone–Weierstrass) |
| `cesaro_fill_of_subseq_sq`, `cesaro_fill_aux` | `Equidistribution.lean` | Cesàro along squares `j²` ⇒ full Cesàro (gap-filling, `Nat.sqrt` squeeze) |

### B. Multidim Weyl criterion (torus `Tᵈ = d → ℝ/ℤ`)
| decl | file | statement |
|---|---|---|
| `IsEquidistributedTorus` | `General/MultidimWeyl.lean` | torus analogue of `IsEquidistributed` |
| `integral_mFourier_eq` | `MultidimWeyl.lean` | `∫ mFourier n = δ_{n,0}` (product Haar) |
| **`weyl_criterion_torus`** | `MultidimWeyl.lean` | **all nonzero torus characters Cesàro→0 ⇒ equidistributed on `Tᵈ`** — mirror of the 1-D proof via mathlib `mFourier`/`span_mFourier_closure_eq_top` |

### C. Davenport–Erdős–LeVeque L² engine
| decl | file | statement |
|---|---|---|
| `ae_eventually_normSq_lt_of_sum_ne_top` | `General/DELEngine.lean` | first Borel–Cantelli at a fixed threshold |
| **`ae_tendsto_zero_of_summable_sq`** | `DELEngine.lean` | **`∑_j ∫₀¹‖g_j‖² ≠ ⊤` ⇒ `g_j → 0` a.e.`** (Markov + Borel–Cantelli). ⚠ the faithful hypothesis is the **total `ℝ≥0∞` sum ≠ ⊤**, not `Summable (∫⁻…)` (which is vacuous over `ℝ≥0∞`) — an Aristotle-caught faithfulness fix; keep it. |
| `l2_bridge` | `DELEngine.lean` | Bochner ↔ lower-integral bridge for continuous `g` |
| `ae_comp_mul_left` | `DELEngine.lean` | a.e.-`s` predicate transfers under nonzero scaling `s ↦ cs` |

### D. Borel normality as equidistribution (the lacunary integer base `gⁿ`)
| decl | file | statement |
|---|---|---|
| `two_pow_inj` / `g_pow_inj` | `WeylDoubling.lean` / `BaseGWeyl.lean` | `aⁿ = aᵐ ⇔ n = m` (distinct powers — the only base-specific input) |
| `weyl_double_sum_integral` | `WeylDoubling.lean` | termwise integration of an abstract double exponential sum (base-agnostic core) |
| `doubling_weyl_L2_mean_norm` / `baseG_weyl_L2_mean_norm` | `WeylDoubling`/`BaseGWeyl` | `∫₀¹‖∑_{n<N} e(k·aⁿ·s)‖² ds = N` for `k ≠ 0` (the Weyl mean square) |
| `ae_doubling_weyl_tendsto(_real)` / `ae_baseG_weyl_tendsto(_real)` | `DoublingEquidist`/`BaseGEquidist` | per-frequency a.e. vanishing (DEL engine + L² mean + `cesaro_fill`) |
| **`ae_doubling_orbit_equidistributed(_real)`** | `DoublingEquidist.lean` | **for a.e. `s`, `n ↦ 2ⁿs` equidistributes on `ℝ/ℤ`** = Borel base-2 normality |
| **`ae_baseG_orbit_equidistributed(_real)`** | `BaseGEquidist.lean` | **base-`g` Borel normality, every `g ≥ 2`** |
| `ae_of_ae_restrict_Icc01_of_periodic` | `DoublingEquidist.lean` | a.e.-`[0,1]` ⇒ a.e.-`ℝ` for a unit-periodic predicate |

## Suggested upstream shape (for the eventual PR)

Two cleanly separable contributions, smallest-first:

1. **`Mathlib/Dynamics/Equidistribution/Basic.lean`** — `IsEquidistributed` + `weyl_criterion`
   (1-D), then `IsEquidistributedTorus` + `weyl_criterion_torus`. Self-contained; depends only on
   mathlib `fourier`/`mFourier` + Stone–Weierstrass span lemmas already present. This is the highest-value,
   lowest-risk PR — Weyl's criterion is a named classical result mathlib genuinely lacks.
2. **`…/Equidistribution/Lacunary.lean`** — the DEL L² engine (`ae_tendsto_zero_of_summable_sq`) +
   Borel normality (`ae_baseG_orbit_equidistributed`). Depends on (1). The base-specific input is
   isolated to `g_pow_inj`, so it states cleanly for any integer base `g ≥ 2`.

## What is NOT upstreamable (the honest boundary)

The **fixed-seed** version — `{ξ·θⁿ}` equidistributes for a *given* `ξ` (e.g. the geometric orbit at a
non-integer base `θ = g^{1/d}`) — is a **famous open problem** (Mahler's 3/2; `{(3/2)ⁿ}` not even known
dense; Koksma 1935 gives only the a.e. result). Everything above is the a.e.-seed metric theorem, which
is provable; the fixed-seed statement is not, and is not claimed anywhere in this repo.

## Pre-PR cleanup checklist (when Trevor takes this up)

- Strip project-specific glue (`dXi*`, `dTorusOrbitG`, the `dStep*` wiring) from the modules — the layer
  above is already stated in project-neutral terms but lives in files that also carry erdos-482 specifics.
- Replace the deprecated `push_neg` calls (noise warnings in `Equidistribution`/`MultidimWeyl`/
  `GeneralTorusFinish`) with `push Not` before submission.
- Disclose AI use + add the `LLM-generated` label (policy: `reference/2026-06-07-mathlib-ai-contribution-policy.md`).
