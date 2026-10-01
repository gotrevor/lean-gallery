# Notes on T. Stoll, *A fancy way to obtain the binary digits of 759250125√2*

*Amer. Math. Monthly* **117** (2010), no. 7, 611–617 ([arXiv:0902.4168](https://arxiv.org/abs/0902.4168)).
Page/section references below are to the arXiv version (v2, 7 pp.), which anyone can open freely.

Two items in **Theorem 3.2** (p. 2), pair `i = 5` (`t₅ = √2`, `β = 0`), found while formalizing the
result in Lean 4, plus a summary of the formalization itself. Everything numerical below is **exact integer
arithmetic** (`math.isqrt`; no floating point) and is reproducible from the scripts in
[`tools/sandbox/`](tools/sandbox/). The two issues are also recorded as a standalone erratum,
[`STOLL-PAIR5-ERRATUM.md`](STOLL-PAIR5-ERRATUM.md).

Notation follows the paper: `vₙ` is the recurrence of Def. 3.1,
`v₁ = 1`, `v_{n+1} = ⌊√2·(vₙ + ε)⌋` for `n` odd, `v_{n+1} = ⌊√2·(vₙ + ½)⌋` for `n` even, and the
binary digits are read off as `dₙ = v_{2n+1} − 2·v_{2n−1}`.

*Authorship: the Lean formalization, the exact computations, and this note were composed by Trevor
Morris's AI assistant (Claude). Trevor directs, checks, and relays the work; the assertions below are
the assistant's, not claimed as his own hand-derivations.*

---

## 1. Typo in the i=5 closed form (§4, p. 5)

In the proof of Theorem 3.2 (§4), the paragraph treating the case `i = 5` ("Finally, we have to treat
the case `i = 5` … Here we directly show that …", p. 5) prints:

> `v_{2k} = ⌊t₅·2^{k−2}⌋ + 2^{k−2}`,  `v_{2k+1} = ⌊t₅·2^{k−1}⌋ + 2^k`  (k ≥ 1).

The first formula has the wrong exponent: as printed it gives `v₂ = 0.5` (not even an integer) and
`v₄ = 2`, whereas the recurrence gives `v₄ = 4`. The corrected formula is

> **`v_{2k} = ⌊√2·2^{k−1}⌋ + 2^{k−1}`,  `v_{2k+1} = ⌊√2·2^{k−1}⌋ + 2^k`  (k ≥ 1)** —

i.e. `k−2 → k−1` in **both** terms of `v_{2k}`. (The `v_{2k+1}` line is correct as printed.) Note both
share the same floor `⌊√2·2^{k−1}⌋`. The corrected form matches the recurrence for all `k` tested.

| k | actual `v_{2k}` | printed `⌊√2·2^{k−2}⌋+2^{k−2}` | corrected `⌊√2·2^{k−1}⌋+2^{k−1}` |
|---|---|---|---|
| 1 | 2  | 0.5 ✗ (non-integer) | 2 ✓ |
| 2 | 4  | 2 ✗ | 4 ✓ |
| 3 | 9  | 4 ✗ | 9 ✓ |
| 4 | 19 | 9 ✗ | 19 ✓ |

---

## 2. The pair-5 interval claim is too wide (substantive)

Theorem 3.2 (the `i = 5` row, p. 2) and its restatement in remark (b) (p. 3) state the digits of √2 are
obtained for **any** `ε` in

> `ε₅ ∈ [309/2·√2 − 218,  1296121037/2·√2 − 916495974) ≈ [0.495995, 0.501240)`.

As an **"all-n" statement this fails**. Taking `ε` at the **included lower endpoint**
`ξ₁,₅ = 309/2·√2 − 218 ≈ 0.4959954`, the digit identity `dₙ = (n-th binary digit of √2)` **first fails
at n = 280** (exact integer recurrence). For comparison:

| ε | first n with `dₙ ≠` bit of √2 |
|---|---|
| `ε = ½` (interior; original Graham–Pollak) | **none** (holds for all n; tested to 4000) |
| `ξ₁,₅ ≈ 0.4959954` (included lower endpoint) | **n = 280** |
| `ξ₂,₅ ≈ 0.5012401` (excluded upper endpoint) | n = 30 |

**This is not a setup artifact:** all seven non-special pairs (`i = 1, 2, 3, 4, 6, 7, 8`) hold over
their *full* stated intervals — machine-checked in Lean (`stoll_pair1..4,6,7,8`, axiom-clean), and five
of them (`i = 1, 2, 4, 6, 8`) independently re-verified numerically to n = 1500 with zero failures (they
enjoy the uniform eq-(8) bound). Only pair 5 fails.

### The true admissible ε-set contracts toward {½}

Computing the set of `ε` for which the digits are correct up to horizon `H` (i.e. for all `m ≤ H`):

| horizon H | admissible ε-interval | width | binding m (lo, hi) |
|---|---|---|---|
| 50   | [0.4959954, 0.5012401) | 5.2e-3 | (6, 28) |
| 200  | [0.4959954, 0.5012401) | 5.2e-3 | (6, 28) |
| 600  | [0.4995421, 0.5006323) | 1.1e-3 | (451, 333) |
| 2000 | [0.4995969, 0.5001184) | 5.2e-4 | (1300, 1400) |
| 6000 | [0.4998082, 0.5000042) | 2.0e-4 | (5332, 3064) |

**At small horizon (`H ≲ 28`) the admissible interval is exactly the stated interval.** Its endpoints
coincide with the pair-4/pair-6 boundary values (`ξ₁,₅ = ξ₂,₄`, `ξ₂,₅ = ξ₁,₆`), which are fixed by the
*neighbors'* finite eq-(9) computations (`m` up to ~30). As `H` grows, `{√2·2^m}` finds closer
approaches to ½ (the binding `m` climbs 28 → 333 → 1400 → 5332 …) and the interval collapses toward
`{½}`.

### Why — and the tie to remark (d)

For `i ∈ I` the floor arguments of `v_{2k}` and `v_{2k+1}` differ by a factor 2, and the ε-step reduces
to eq (8), `0 ≤ (1−√2){α√2·2^{k−l−1}} + √2ε < 1`, which is **uniform** in `ε`. For pair 5, `v_{2k}` and
`v_{2k+1}` share the *same* floor, so the roles swap and the ε-step becomes the **ε-perturbed crux**

> `0 ≤ {x} − √2·{x/2} + √2·ε < 1`,  with `x = √2·2^k`.

Now `{x} − √2{x/2} ∈ [−√2/2, 1−√2/2)`, with the extremes approached exactly when `{√2·2^m} → ½`. So a
fixed `ε ≠ ½` eventually hits a wall: the step requires `{√2·2^m}` to avoid a band around ½ for **all**
`m`, an infinitary property of √2's binary digits. This is exactly the normality connection of your
remark (d) (p. 3) — there you use it to *enlarge* `ε₁`/`ε₈` under non-normality; the same mechanism *shrinks*
pair 5's interval to `{½}` if √2 is normal in base 2 (believed, unproven). So the full-interval pair-5
claim is, as an all-n theorem, false at the stated endpoints, and the sharp positive version is at best
conditional on an explicit Diophantine hypothesis `{√2·2^m} ∉ (½−δ, ½+δ) ∀m`.

The honest content for pair 5 is therefore: **the digits of √2 are obtained for all n exactly at
`ε = ½`** (the original Graham–Pollak), where the ε-step *is* the universal crux.

---

## 3. Reproduction

Self-contained, stdlib-only, exact integer arithmetic:

- [`tools/sandbox/stoll_pair5_verify.py`](tools/sandbox/stoll_pair5_verify.py) — typo table, interval
  endpoints, first-fail index per ε, the ε-step margin diagnostics.
- [`tools/sandbox/stoll_pair5_digits.py`](tools/sandbox/stoll_pair5_digits.py) — digit-level first-fail
  (n=280 for ξ₁,₅, n=30 for ξ₂,₅, none for ε=½).
- [`tools/sandbox/stoll_pair5_shrink.py`](tools/sandbox/stoll_pair5_shrink.py) — the horizon-vs-interval
  contraction table above.
- [`tools/sandbox/stoll_pairsI_verify.py`](tools/sandbox/stoll_pairsI_verify.py) — control: pairs 1–4,6–8
  over their full intervals.

The floor identities used: `⌊x·√2⌋ = isqrt(2x²)` for integer `x ≥ 0`; `⌊√2·(v+½)⌋ = isqrt(2(2v+1)²)//2`;
and for `ε = (c/2)√2 − d` (`c, d ∈ ℤ`), `⌊√2·(v+ε)⌋ = c + ⌊(v−d)·√2⌋`.

---

## 4. Lean 4 formalization

The complete results of **both** the relevant Stoll papers are machine-checked in Lean 4 and
**axiom-clean** — every theorem's `#print axioms` is exactly the trust base
`[propext, Classical.choice, Quot.sound]`: no `sorry`, no added axioms, no `native_decide`.

**This paper (arXiv:0902.4168)** — `src/Erdos482/`:
- `graham_pollak` — the headline (GP recurrence reads off the binary digits of √2).
- `stoll_pair1..4,6,7,8` (+ `…_t` forms) — Theorem 3.2 for all 7 non-special pairs, over the full
  stated intervals; `stoll_intervals_cover` (the intervals partition the range); `stoll_gp_isBit`.
- `cor33_unconditional` (+ `_t`) — Corollary 3.3, the binary digits of `759250125√2`.
- Pair 5, formalized honestly: `stoll_pair5_closed_form` (typo-corrected §4 form), `pair5_estep_band`
  (exact band characterization of the ε-step), `stoll_pair5_conditional` (the conditional full-interval
  theorem), and `pair5_band_fails_below_half` / `pair5_band_fails_above_half` (the precise two-sided
  obstruction showing no `ε ≠ ½` is uniformly admissible).

**The general resolution ([St05], *J. Integer Seq.* 8 (2005))** — `src/Erdos482/General/`:
Thm 1.1 (Rabinowitz–Gilbert), Thm 1.2 (Case I, `ε ∈ [⅓,⅔)`; Case II, `ε = ½`), **Thm 1.3** (g-ary, any
base `g ≥ 2`), Cor 1.1 (both √2 binary families), Cor 1.2 (ternary √2), Prop 2 (digit extraction). The
top-level `erdos482_resolution` / `erdos482_resolution_general_literal` package it: for any `w > 0` and
any base `g ≥ 2`, an explicit recurrence reads off `w`'s genuine base-`g` digits (bridged to mathlib's
`Real.digits`).

The one thing *not* formalized is the pair-5 full interval — because, per §2, it is not a theorem.
