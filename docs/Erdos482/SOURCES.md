# Sources — Erdős #482

Provenance + verbatim formalization targets for the papers behind this repo. **PDFs are gitignored**
(`papers/**/*.pdf`): this is a public repo and the source papers are copyrighted (not redistributable
here), so only citations + math facts live in this file.

## The three Stoll papers (don't conflate them)

| key | paper | venue | covers |
|---|---|---|---|
| `0902.4168` | *A fancy way to obtain the binary digits of 759250125√2* | arXiv, 2009 | the α√2 trick (Thm 3.2 / Cor 3.3) — **already formalized** (see `src/Erdos482/Stoll.lean`). ⚠️ has errors: see `STOLL-PAIR5-ERRATUM.md`. |
| **[St05]** | *On families of nonlinear recurrences related to digits* | J. Integer Seq. **8** (2005), Art. 05.3.2 (8pp) | **the general resolution** — any real `w>0`, any base `g≥2`. PDF: `papers/St05-stoll-JIS2005.pdf` (open-access, [JIS](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf)). |
| **[St06]** | *On a problem of Erdős and Graham concerning digits* (**solo Thomas Stoll**, Wien) | Acta Arith. **125.1** (2006), 89–100 | The "vast extension": a 3-parameter `(m,l,k)` family of recurrences (Thm 3.1, 6 subcones); striking examples (Ex 1.1: ternary digits of `e` via a π/e recurrence); two extra binary families (Thms 3.3/3.4); a Beatty-theorem unification of Borwein–Bailey `m=1..10` (Cor 3.5). Does NOT supersede St05. DOI [10.4064/aa125-1-8](https://doi.org/10.4064/aa125-1-8). **OBTAINED 2026-06-13** (sent by Stoll). PDF `papers/St06-stoll-ActaArith2006.pdf` (gitignored, copyrighted — do NOT commit). Formalization plan + transcribed statements: [`../notes/ST06-PLAN.md`](../notes/ST06-PLAN.md) (fun extension, branch `st06`). |

The erdosproblems.com #482 page marks the problem **SOLVED** on the strength of [St05]+[St06].
Erdős–Graham [ErGr80, p.96] asked for "similar results for √m and other algebraic numbers" but said
"we have no idea what they are." St05's explicit coefficient formulas (below) ARE "what they are."

## ⚠️ READ THIS BEFORE FORMALIZING: verify, don't trust

The live fleet already proved that **Stoll's printed claims can be wrong** — `0902.4168`'s pair-5
full-interval claim is *false* (the digit identity fails at `n=280` at the stated lower endpoint) and
its closed form has a typo (`STOLL-PAIR5-ERRATUM.md`). So treat every St05 closed form, interval
endpoint, and coefficient as a **conjecture to numerically verify first**, exactly as the pair work did.
Test each target over many `n` for several `w` (e.g. `√2, √3, π`, a random transcendental), at the
**interval endpoints** of `ε`, and for a few `j`/`g`. If a claim fails at an endpoint, scope it down and
write an erratum note (don't formalize a false statement).

## St05 — verbatim targets

Notation: `t = w/g^m`, `m = ⌊log_g w⌋`, so `1 ≤ t < g` (`t` = `w`'s base-`g` mantissa). `⌊·⌋` = floor.

**Proposition 2 (g-ary digit extraction).** For integer `g≥2` and `w=(d₁d₂d₃…)_g` with `d₁≠0`,
`0≤dₙ<g`, and not all of `dₙ,dₙ₊₁,…` equal `g−1`: then `1≤t<g` and
`dₙ = ⌊t·gⁿ⁻¹⌋ − g·⌊t·gⁿ⁻²⌋`.  (= our `digit_bridge`/`digits_eq_floor_sub`, generalized to base `g`.)

**Theorem 1.1 (Rabinowitz–Gilbert 1991; binary, prior work).** `w>0`, `t=w/2^m`.
`a = 2(1 − 1/(t+2))`, `b = 2/a`. Recurrence `u₁=1`; `uₙ₊₁ = ⌊a(uₙ+½)⌋` if `n` odd, `⌊b(uₙ+½)⌋` if `n`
even. Then `u₂ₙ₊₁ − 2u₂ₙ₋₁` = n-th binary digit of `w`. (`w=√2` ⇒ `a=b=√2` = Graham–Pollak.)

**Theorem 1.2 (Stoll; binary, two ∞-families, `j∈ℤ₊`).** Recurrence `u₁=1`;
`uₙ₊₁ = ⌊a(uₙ+½)⌋` if `n` odd, `⌊b(uₙ+ε)⌋` if `n` even. Then `u₂ₙ₊₁ − 2u₂ₙ₋₁` = n-th binary digit of `w`.
- **Case I:** `a = 2(j − 1/(t+2))`, `b = 2/a`, with `1/3 ≤ ε < 2/3`.
  Closed forms: `u₂ₖ = 2^{k−1} + ⌊t·2^{k−1}⌋ + (j−1)(2^k + 2⌊t·2^{k−2}⌋ + 1)`; `u₂ₖ₊₁ = 2^k + ⌊t·2^{k−1}⌋`.
- **Case II:** `a = 2j − t/(t+2)`, `b = 2/a`, with `ε = 1/2` (the paper notes ε=½ is forced here).
  Closed forms: `u₂ₖ = 2^k + ⌊t·2^{k−2}⌋ + (j−1)(2^k + 2⌊t·2^{k−2}⌋ + 1)`; `u₂ₖ₊₁ = 2^k + ⌊t·2^{k−1}⌋`.

**Theorem 1.3 (Stoll; g-ary, any integer `g≥2`).** `t=w/g^m`. `a = g/((g−1)(t+g))`, `b = g/a`.
Recurrence `u₁=1`; `uₙ₊₁ = ⌊a(uₙ+ε)⌋` if `n` odd, `⌊b(uₙ + 1/(g−1))⌋` if `n` even, with
`−1/g ≤ ε < (g+1)(g−2)/g`. Then `u₂ₙ₊₁ − g·u₂ₙ₋₁` = n-th g-ary digit of `w`.
Closed forms: `u₂ₖ = (g^{k−1} − 1)/(g−1)`; `u₂ₖ₊₁ = g^k + ⌊t·g^{k−1}⌋`.

**Corollary 1.1 (w=√2 via Thm 1.2).** `aⱼ = j + (−1)ʲ√2` for `j=0,2,3,…`, `bⱼ=2/aⱼ`; the
`⌊aⱼ(uₙ+½)⌋`/`⌊bⱼ(uₙ+½)⌋` recurrence gives the binary digits of √2. (`j=1` excluded: `a₁=1−√2<0` fails.)

**Corollary 1.2 (ternary √2 via Thm 1.3, g=3).** `a=(9−3√2)/14`, `b=6+2√2`; then `u₂ₙ₊₁ − 3u₂ₙ₋₁`
= n-th ternary digit of √2 = `(1.102011221…)₃`.

## Proof skeleton (all of St05, ~3 pages, elementary)

Every theorem: prove the closed forms for `u₂ₖ`, `u₂ₖ₊₁` by induction from `u₁=1`, then apply Prop 2 to
read off `u₂ₙ₊₁ − g·u₂ₙ₋₁ = dₙ`. Each induction step is a single `⌊real⌋ = integer` claim rewritten as
two inequalities and closed by the fractional-part bound `0 ≤ ⌊x⌋ − x + (stuff) < 1`, using the digit
bound `0 ≤ t·gᵏ − g⌊t·gᵏ⁻¹⌋ = (dₖ₊₁.dₖ₊₂…)_g < g` from Prop 2. **No field theory; no per-√m algebra.**
Note: unlike the `0902.4168` pairs (which needed per-pair script-generated base cases up to `k=l+2`),
these closed forms hold from `k=1` directly — so **no long base-case chains** should be needed.
