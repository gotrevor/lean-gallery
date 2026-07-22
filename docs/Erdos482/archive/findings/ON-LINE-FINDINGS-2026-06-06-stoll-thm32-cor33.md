# ON-LINE-FINDINGS — Stoll Thm 3.2 + Cor 3.3 (the BONUS)

**Request:** 2026-06-06 item in `ON-LINE-REQUEST.md` — faithful statements of Stoll's Theorem 3.2
(8-pair table + parametrized recurrence + digit-index eqs) and Corollary 3.3 (the `759250125√2`
example), for replaying the `gp_pair` induction per pair.

**Source read:** T. Stoll, *A fancy way to obtain the binary digits of 759250125√2*,
arXiv:0902.4168 — full HTML via `ar5iv.labs.arxiv.org/html/0902.4168` (the `alttext` LaTeX, so the
formulas below are the author's own LaTeX, transcribed verbatim, not OCR). Section 2 (eqs 1–2),
Section 3 (Def 3.1, Thm 3.2, Cor 3.3), Section 4 (proof: eqs 5–9). Cross-checked every row of the
table numerically (script `tools/sandbox/fetch_stoll.py` on the host + an arithmetic check).

---

## ⚠️ Three faithfulness corrections vs. the request's paraphrase (read these first)

1. **The constant in Cor 3.3 is `1 − π²/e³`, NOT `1 − π²/e⁴`.**
   `1 − π²/e³ = 0.5086213…` lies in the ε₆ interval `[0.5012401…, 0.5103528…)`. (`1 − π²/e⁴ =
   0.8192…`, which is outside *every* εᵢ interval — the `e⁴` in the request header is a typo.)

2. **The recurrence is TWO-case, not a single additive constant.** Def 3.1 varies the offset only on
   **odd** steps: `v_{n+1} = ⌊√2(vₙ + ε)⌋` when `n` is odd, `⌊√2(vₙ + ½)⌋` when `n` is even.
   (The original GP sequence `u` in eq (1) uses `½` at every step; the bonus needs the new `ε`-on-odd
   sequence `v`. Your existing `u`/`gp_pair` is the `ε = ½` special case, = pair `i=5`, `t₅ = √2`.)

3. **Index base.** `v` is **1-indexed**: `v₁ = 1` (Stoll never uses `v₀`). The digit map is
   `dₙ = v_{2n+1} − 2v_{2n−1}` for `n ≥ 1` (eq (2)/Def 3.1), and `t = (d₁.d₂d₃…)₂` — so `d₁` is the
   **integer/units** binary digit and `d₂, d₃, …` are the fractional digits.

---

## Section 2 — the original sequence (eqs 1–2)

> **(1)**  `u₁ = 1,  u_{n+1} = ⌊√2 (uₙ + ½)⌋,  n ≥ 1.`
>
> **(2)**  `dₙ = u_{2n+1} − 2u_{2n−1}`  gives the n-th binary digit of `√2 = (1.011010100…)₂`.

## Definition 3.1 (the parametrized recurrence — this is what the bonus uses)

> Let `ε ∈ ℝ` and define `(vₙ)_{n≥1}` by
>
> `v₁ = 1,   v_{n+1} = ⌊√2 (vₙ + ε)⌋`  if `n` is **odd**;
> `             v_{n+1} = ⌊√2 (vₙ + ½)⌋`  if `n` is **even**.
>
> We call `(ε, t)` a **Graham–Pollak pair** if `dₙ = v_{2n+1} − 2v_{2n−1}` (n ≥ 1) represents the
> binary digits of `t`; i.e. `t = (d₁.d₂d₃…)₂`.
>
> `(½, √2)` is a GP pair (the original result).

---

## Theorem 3.2 — the 8 pairs `{(εᵢ, tᵢ) : 1 ≤ i ≤ 8}`

Verbatim intervals + targets (each `εᵢ` interval is `[ξ₁ᵢ, ξ₂ᵢ)`, half-open):

| i | `ξ₁ᵢ` (lower, ≤ εᵢ) | `ξ₂ᵢ` (upper, > εᵢ) | `tᵢ` |
|---|---|---|---|
| 1 | `1 − √2/2` | `√2 − 1` | `√2 − 1` |
| 2 | `√2 − 1` | `(19/2)√2 − 13` | `(11/8)√2 − 5/8` |
| 3 | `(19/2)√2 − 13` | `(77/2)√2 − 54` | `(45/32)√2 − 19/32` |
| 4 | `(77/2)√2 − 54` | `(309/2)√2 − 218` | `(181/128)√2 − 75/128` |
| 5 | `(309/2)√2 − 218` | `(1296121037/2)√2 − 916495974` | `√2` |
| 6 | `(1296121037/2)√2 − 916495974` | `(79109/2)√2 − 55938` | `(759250125/536870912)√2 − 314491699/536870912` |
| 7 | `(79109/2)√2 − 55938` | `(5/2)√2 − 3` | `(46341/32768)√2 − 19195/32768` |
| 8 | `(5/2)√2 − 3` | `√2/2` | `(3/2)√2 − 1/2` |

The intervals are **disjoint and exactly cover** `[1 − √2/2, √2/2)`.

**Remarks from the paper:**
- (b) The digits of `√2` (pair 5) are obtained for any `ε ∈ [0.4959953…, 0.5012400…)` — this is
  exactly the ε₅ interval; it slightly generalizes Graham–Pollak's `ε = ½`.
- (c) Admissible ε can't extend much: `ε = 0.2928 ⇒ d_{3067} = −1`; `ε = 0.7073 ⇒ d_{2293} = 2`.
  New pairs could only hide in a tiny neighborhood of `1 − √2/2` or `√2/2`.

### The `(αᵢ, βᵢ, lᵢ, γᵢ)` decomposition (Section 4, this is the per-pair induction data)

For `i ∈ I := {1,…,8} \ {5}`, write `tᵢ = (αᵢ√2 − βᵢ)·2^{−lᵢ}` with `αᵢ, βᵢ, lᵢ ∈ ℤ`, `(αᵢ, 2) = 1`.
Then **`αᵢ + βᵢ = 2^{lᵢ+1}`**, and define **`γᵢ = 2αᵢ + βᵢ`**. (Numerically verified, all rows.)

| i | `αᵢ` | `βᵢ` | `lᵢ` | `γᵢ = 2αᵢ+βᵢ` | `αᵢ+βᵢ = 2^{lᵢ+1}` | scaled irrational extracted = `αᵢ·√2` |
|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 3 | 2 = 2¹ | `√2` |
| 2 | 11 | 5 | 3 | 27 | 16 = 2⁴ | `11√2` |
| 3 | 45 | 19 | 5 | 109 | 64 = 2⁶ | `45√2` |
| 4 | 181 | 75 | 7 | 437 | 256 = 2⁸ | `181√2` |
| 5 | (1) | (0) | (0) | — | **N/A** (special case, see below) | `√2` |
| 6 | 759250125 | 314491699 | 29 | 1832991949 | 1073741824 = 2³⁰ | **`759250125√2`** (Cor 3.3) |
| 7 | 46341 | 19195 | 15 | 111877 | 65536 = 2¹⁶ | `46341√2` |
| 8 | 3 | 1 | 1 | 7 | 4 = 2² | `3√2` |

"Extracts `αᵢ√2`" because `2^{lᵢ}·tᵢ + βᵢ = αᵢ√2` (so tᵢ's digits = αᵢ√2's digits, shifted by `lᵢ`
and offset by the integer `βᵢ`). Note `536870912 = 2²⁹`, `314491699 < 2²⁹`, and
`759250125 + 314491699 = 1073741824 = 2³⁰` ✓.

**Pair `i = 5` is special:** `t₅ = √2` has `β = 0`, so `α + β = 1 ≠ 2^{l+1}` — it's excluded from `I`
and proved directly (no init-condition fuss): `v_{2k} = ⌊t₅ 2^{k−2}⌋ + 2^{k−2}` and
`v_{2k+1} = ⌊t₅ 2^{k−1}⌋ + 2^k` for `k ≥ 1`. (This is your already-formalized headline case.)

---

## The digit-index machinery (eqs 5–9, general `(α,β,l,γ)` form)

Claim proved for `i ∈ I`, `ξ₁ᵢ ≤ εᵢ < ξ₂ᵢ`, and `k ≥ lᵢ + 2`:

> **(5)**  `v_{2k}   = ⌊tᵢ 2^{k−2}⌋ + γᵢ 2^{k−lᵢ−2}`
> **(6)**  `v_{2k+1} = ⌊tᵢ 2^{k−1}⌋ + 2^k`

These give, for `k ≥ lᵢ + 3`:

> `v_{2k+1} − 2v_{2k−1} = ⌊tᵢ 2^{k−1}⌋ − 2⌊tᵢ 2^{k−2}⌋ = the k-th binary digit of tᵢ.`

**Induction step `(5) ⇒ (6)` reduces (via `γᵢ − βᵢ = 2αᵢ` and `αᵢ + βᵢ = 2^{lᵢ+1}`) to:**

> **(7)**  `0 ≤ {αᵢ√2·2^{k−lᵢ−1}} − √2·{αᵢ√2·2^{k−lᵢ−2}} + √2/2 < 1`
>
> which holds because the **universal crux** `0 ≤ {x} − √2·{x/2} + √2/2 < 1` is true for all `x ∈ ℝ`.
> *(= your `crux`. Eq (7) is just `crux` instantiated at `x = αᵢ√2·2^{k−lᵢ−1}`.)*

**Induction step `(6) ⇒ next (5)` reduces to:**

> **(8)**  `0 ≤ (1 − √2)·{αᵢ√2·2^{k−lᵢ−1}} + √2·ε < 1`,
>
> which holds **provided `1 − √2/2 ≤ ε < √2/2`** — an interval containing *every* `[ξ₁ᵢ, ξ₂ᵢ)`, so
> ε imposes no extra restriction. *(= your `eq8_general`.)*

**Initial condition (eq 9), the only ε-sensitive part:** there is at most one half-open interval
`[ξ̄₁ᵢ, ξ̄₂ᵢ)` of ε for which (5) holds at `k = lᵢ + 2`, namely where

> **(9)**  `v_{2(lᵢ+2)} = ⌊tᵢ 2^{lᵢ}⌋ + γᵢ = ⌊αᵢ√2 − βᵢ⌋ + 2αᵢ + βᵢ = ⌊αᵢ√2⌋ + 2αᵢ`,

and Stoll shows `[ξ̄₁ᵢ, ξ̄₂ᵢ) = [ξ₁ᵢ, ξ₂ᵢ)` (the table's intervals). He also confirms (6) holds for
`0 ≤ k ≤ lᵢ + 1`, completing the proof. (Worked example `i = 6`: `v₆₂`, target
`⌊α₆√2⌋ + 2α₆ = 2749487923`; `ξ₁,₆ = 1296121037√2/2 − 916495974 = 0.5012400…`.)

> **Practical note for Lean:** eqs (5)–(8) are pure `crux`/`eq8_general` replays per pair (you have
> both). The *only* per-pair labor is eq (9): an `⌊αᵢ√2⌋`-style `norm_num`/interval check at the base
> index `k = lᵢ + 2`, plus checking (6) for `0 ≤ k ≤ lᵢ + 1`. For the tractable pairs (`l` small:
> i=1 l=0, i=8 l=1, i=2 l=3) this is cheap; i=6 (`l=29`) and i=7 (`l=15`) need bigger `2^{…}`
> norm_num but are still finite checks against `⌊αᵢ√2⌋`.

---

## Corollary 3.3 (verbatim)

> Define `(wₙ)_{n≥1}` by
>
> `w₁ = 1,   w_{n+1} = ⌊√2 (wₙ + 1 − π²/e³)⌋`  if `n` is **odd**;
> `             w_{n+1} = ⌊√2 (wₙ + ½)⌋`  if `n` is **even**.
>
> Then **for `n ≥ 31`, `w_{2n+1} − 2w_{2n−1}` is the `(n+1)`-th binary digit of `759250125√2`.**

**Why it follows from Thm 3.2 (pair 6):** the "(rather plain) observation" that
`1 − π²/e³ = 0.5086213…` lies in the ε₆ interval `[1296121037√2/2 − 916495974,  79109√2/2 − 55938)
= [0.5012401…, 0.5103529…)`. So `(1 − π²/e³, t₆)` is a GP pair, and since
`2²⁹·t₆ + 314491699 = 759250125√2`, the digits of `t₆` are the digits of `759250125√2` (shifted by
`l₆ = 29`). The `n ≥ 31` threshold is `n ≥ l₆ + 2`; the index shift to `(n+1)`-th digit is the `2^{29}`
shift bookkeeping.

**To discharge the membership in Lean:** prove `1296121037√2/2 − 916495974 ≤ 1 − π²/e³ < 79109√2/2 −
55938`. The `√2` endpoints are algebraic (`norm_num`-friendly with √2 bounds); the middle term needs
`π` and `e` bounds — mathlib has `Real.pi_gt_*`/`Real.pi_lt_*` and `Real.exp_one_gt_*`/`exp_one_lt_*`
(e.g. `Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`, `Real.pi_gt_3141592`, `Real.pi_lt_3141593`).
Numeric target: `0.5012401 < 0.5086213 < 0.5103529`. You only need ~3-4 decimals of π and e to
separate `0.50124` and `0.51035` from `0.50862`, so coarse interval bounds suffice.

---

## Reference summary (for `papers/SOURCES.md` if you keep one)

- **Stoll, T.** "A fancy way to obtain the binary digits of 759250125√2." *Amer. Math. Monthly* **117**
  (2010), no. 7, 611–617; arXiv:0902.4168 (2009). Self-contained; the headline (§4, `√2`, pair 5) you've
  already formalized. Key reusable lemmas: eq (7) = `crux` (universal), eq (8) = `eq8_general`.
- Primary refs inside: Graham–Pollak, *Math. Mag.* 43 (1970) 143–145 [orig. result];
  Hwang–Lin [8]; Knuth TAOCP vol. 3 §5.3.1; Allouche–Shallit Ex.45 p.116.
- OEIS sequences linked to the GP sequence: A091522–A091525, A100671, A100673, A001521, A004539.
