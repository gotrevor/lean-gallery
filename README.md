# LeanGallery 🖼️

A curated, public **showcase** of formalized mathematics in **Lean 4 + Mathlib** — finished,
axiom-clean formalizations of notable results, with a soft spot for *solved-but-unformalized*
theorems and *no-formula / impossibility* meta-theorems.

This is a **publish-only** collection: every result here compiles cleanly with **no `sorry`** and
**no warnings** (warnings are errors), enforced by CI (a build plus a `#print axioms` gate). Active /
work-in-progress development happens in private repositories; only finished, axiom-clean results are
promoted in here.

📖 **[Browse the API docs](https://gotrevor.github.io/lean-gallery/)** (doc-gen4, rebuilt from `main` on every push).

## Contents

| Area | Result | Status |
|------|--------|--------|
| `Logic/Goodstein` | **Goodstein 1944** — every Goodstein sequence terminates (`∀ m, ∃ N, goodsteinSeq m N = 0`). Faithful hereditary-base bump, interpreted into ordinals below ε₀; strict ordinal descent + well-foundedness of `<` on `Ordinal`. | ✅ axiom-clean |
| `Logic/Hydra` | **Kirby–Paris 1982** — Hercules always wins: every hydra dies (`hydra_terminates` — every battle reaches `leaf`). Faithful chop-a-head-regrow-at-the-grandparent move on finite rooted trees; the ε₀ Kirby–Paris ordinal `♯ ωᵒ⁽ᶜ⁾`, realized as a recursive multiset (path) order on `Mathlib/Logic/Hydra.lean`'s `CutExpand`; strict descent + well-foundedness. | ✅ axiom-clean |
| `NumberTheory/Erdos403` | **Erdős #403** (Frankl / Shen Lin 1976, both unpublished) — only finitely many powers of two are sums of distinct factorials (`erdos_403_finite`), and the largest is `2⁷ = 2! + 3! + 5! = 128` (`erdos_403_sharp`, `m ≤ 7`). Reconstruction via the factorial number system: a sum of distinct factorials is a factorial-base numeral with all digits `≤ 1`, and every `2^m` (`m ≥ 8`) carries a digit `≥ 2` — a fixed-modulus `12!` check, kernel-pure (no `native_decide`). | ✅ axiom-clean |
| `Combinatorics/Erdos1213` | **Erdős #1213 / Hegyvári Thm 3** (Hegyvári 1986) — a strictly increasing sequence with consecutive gaps `≤ K` whose consecutive-block sums are all distinct has last term `< (a₁+K/2)·e^(K+1) + K·e^(2K+2)` (`erdos_1213`); hence `f(a,K)` is finite (`erdos_1213_f_finite`). First known formalization. | ✅ axiom-clean |
| `NumberTheory/Erdos1050` | **Erdős #1050** (Borwein 1991/92) — the series `∑ 1/(2ⁿ−3)` is irrational (`erdos_1050_irrational`), via Borwein's irrationality criterion for `∑ 1/(qⁿ+r)` specialized to `q=2, r=−3`. The general engine also proves **Borwein's Theorem 1** fully axiom-free — `∑ 1/(qⁿ+c)` is irrational for any integer base of magnitude `≥ 2` and any nonzero rational `c` (`borwein_thm1_abs`), discharging the `borwein_approximants` axiom. | ✅ axiom-clean |
| `Combinatorics/Erdos880` | **Erdős #880** (Hegyvári–Hennecart–Plagne 2007) — for an additive basis `A` of order `k`, are the gaps of its restricted-sum set (sums of `≤ k` distinct elements) bounded? **Yes for `k = 2`** (`erdos_880_order_two`, gaps eventually `≤ 2`); **no for `k ≥ 3`** (`erdos_880`: an explicit order-`h` basis with arbitrarily long gaps). Includes the faithful `Δ = limsup`-gap restatements and the HHP07 Theorem 3/4/8/9 companions; an in-library `AxiomGuard` build-checks `#print axioms` for ~25 theorems. | ✅ axiom-clean |
| `NumberTheory/Erdos482` | **Erdős #482 / Graham–Pollak** (Stoll) — the recurrence `u(0)=1, u(n+1)=⌊√2·(uₙ+½)⌋` reads off the binary expansion of `√2`: the difference `u(2n+1) − 2·u(2n−1)` is the `n`-th binary digit of `√2` (`graham_pollak`). Resolved in **full generality** (`erdos482_resolution`): for every real `w > 0` and base `g ≥ 2`, an explicit Graham–Pollak-type recurrence reads the base-`g` digits of `w`. Includes Stoll's `759250125·√2` showcase constant (`cor33_unconditional`) and the St06 digit-frontier family. | ✅ axiom-clean |

## What to audit (faithfulness)

The trust surface for each result is small and called out explicitly. For Goodstein:

- `LeanGallery/Logic/Goodstein/Basic.lean` — the **definition** of a Goodstein sequence (the
  hereditary-base bump + subtract-one process), plus `native_decide` anti-vacuity anchors: the
  definition *computes* the genuine trajectories (`m = 0..4`, including `4 = 2²`, the first seed
  that exercises the recursive exponent bump), so a vacuous definition can't pass. Read this
  against Goodstein 1944.
- `LeanGallery/Logic/Goodstein/Statement.lean` — the **headline** `goodstein_terminates`.

For Kirby–Paris:

- `LeanGallery/Logic/Hydra/Basic.lean` — the **datatype** `Hydra` (a finite rooted tree) and the
  legal **move** `Step` (chop a head; if its parent is not the root, regrow `n + 1` copies of the
  cut node at the grandparent), with explicit one-move derivations as anti-vacuity anchors
  (including the regrowth that makes the hydra *bigger*, and the dead hydra being *terminal*). The
  game is on unordered trees — every statement is invariant under permuting children. Read this
  against Kirby–Paris 1982.
- `LeanGallery/Logic/Hydra/Statement.lean` — the **headline** `hydra_terminates` (every battle
  reaches `leaf`, over all head choices and all regrowth schedules).

For Erdős #403:

- `LeanGallery/NumberTheory/Erdos403/Basic.lean` — the **definition** `factSum S = ∑_{a ∈ S} a!`
  (a sum of distinct factorials is exactly `factSum S` for some `S : Finset ℕ`), plus `decide`
  anti-vacuity anchors (`factSum {2,3,5} = 2⁷ = 128`, and the `0! = 1!` collision `{2}` vs `{0,1}`).
  Read this against the problem statement.
- `LeanGallery/NumberTheory/Erdos403/Statement.lean` — the **headlines** `erdos_403_finite`
  (finiteness) and `erdos_403_sharp` (`m ≤ 7`, sharp via `Basic.witness`).

For Erdős #1213:

- `LeanGallery/Combinatorics/Erdos1213/Statement.lean` — the **headlines** `erdos_1213` (the explicit
  last-term bound) and `erdos_1213_f_finite` (finiteness of `f(a,K)`), with the bound written out
  verbatim. To audit, also read `csum`/`AllCSumsDistinct` in `Basic.lean` and `hegyvariF` in
  `Main.lean` (a dozen lines). Read against Hegyvári 1986, Theorem 3.

For Erdős #1050:

- `LeanGallery/NumberTheory/Erdos1050/Statement.lean` — the **headline** `erdos_1050_irrational`
  (`Irrational S`), with the series and the index convention spelled out. To audit, also read the
  one-line `S` in `Basic.lean`. Read against the erdosproblems.com #1050 statement (Borwein 1991/92).

For Erdős #880:

- `LeanGallery/Combinatorics/Erdos880/Statement.lean` — the **headlines** `erdos_880` (the `k ≥ 3`
  negative answer) and `erdos_880_order_two` (the `k = 2` bounded-gaps case), plus the faithful
  `Δ`-functional restatements. To audit, read the ≈10-line `Basic.lean` definitions (`restrictedSums`,
  `IsBasisOfOrder`, `UnboundedGaps`, `BoundedGapsBy`); `AxiomGuard.lean` build-checks the axiom list of
  ~25 theorems. Read against Hegyvári–Hennecart–Plagne 2007.

For Erdős #482:

- `LeanGallery/NumberTheory/Erdos482/Statement.lean` — the single trust surface: every headline as a
  documented `alias` (a citation + plain-English claim sitting next to the machine-checked re-export).
  The primary headlines are `graham_pollak` (the Graham–Pollak difference is the `n`-th binary digit of
  `√2`), `erdos482_resolution` (the full-generality resolution, every `w > 0` and base `g ≥ 2`), and
  `cor33_unconditional` (Stoll's `759250125·√2` constant). Read against Stoll, arXiv:0902.4168.

`Engine.lean` (or, for #1213, the `Counting`/`Analytic`/`Main` proof files) is the proof; `Basic.lean`
+ `Statement.lean` are the audit surface. CI re-checks `#print axioms` so each published claim stays
`[propext, Classical.choice, Quot.sound]`.

## Motivations 🎬

Several results here started as a popular-math video. [`videos/`](videos/README.md) catalogs those
sparks and links each to where the result lives in Lean (or flags it as a not-yet-formalized target).

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Toolchain and Mathlib pin live in `lean-toolchain` / `lake-manifest.json` (Lean v4.31.0).

## References

- R. L. Goodstein, *On the restricted ordinal theorem*, Journal of Symbolic Logic **9** (1944),
  no. 2, 33–41. <https://doi.org/10.2307/2268019>
- L. Kirby and J. Paris, *Accessible independence results for Peano arithmetic*, Bull. London
  Math. Soc. **14** (1982), no. 4, 285–293. <https://doi.org/10.1112/blms/14.4.285>
- P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number theory*,
  Monographies de L'Enseignement Mathématique **28** (1980), p. 79. Erdős problem #403,
  <https://www.erdosproblems.com/403>.
- N. Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar. **48** (1986), 193–200.
  <https://doi.org/10.1007/BF01949064>. Erdős problem #1213, <https://www.erdosproblems.com/1213>.
- P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory **37** (1991), 253–259;
  *On the irrationality of certain series*, Math. Proc. Camb. Phil. Soc. **112** (1992), 141–146.
  Erdős problem #1050, <https://www.erdosproblems.com/1050>.
- N. Hegyvári, F. Hennecart, A. Plagne, *Answer to a question by Burr and Erdős on restricted addition,
  and related results*, Combin. Probab. Comput. **16** (2007), 747–756. Erdős problem #880,
  <https://www.erdosproblems.com/880>.
- The Graham–Pollak `√2`-digit recurrence and its general-base resolution: T. Stoll, arXiv:0902.4168.
  Erdős problem #482, <https://www.erdosproblems.com/482>.

## License

[Apache License 2.0](LICENSE). Copyright 2026 Trevor Morris.
