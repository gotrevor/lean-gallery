# ON-LINE-FINDINGS — St06 Theorem 3.4 exact statement, ε-interval, and proof structure

**Request:** `ON-LINE-REQUEST.md` 2026-06-13 — St06 Thm 3.4 exact hypotheses + exact ε-interval
(both endpoints, open/closed); per-`w` vs t-universal; does the ε-step proof use a Diophantine
property of `t`. (Marked "curiosity, fulfil if convenient" — but the answer overturns the repo's
current Thm 3.4 conclusion, so it's load-bearing.)

**Source read:** the actual PDF, `papers/St06-stoll-ActaArith2006.pdf` (gitignored but present on the
host) — T. Stoll, *On a problem of Erdős and Graham concerning digits*, Acta Arith. **125** (2006)
89–100. Read the Thm 3.4 statement (pp. 93–94) **and its full proof** (§4.2, pp. 98–99). All numbers
below cross-checked two ways: (a) re-derived both interval endpoints from the proof's algebra; (b)
exact high-precision recurrence run on the host (`tools/sandbox/st06_thm34_HOSTCHECK.py`, 220-digit
`Decimal`, w=√2, 6 parameter triples, stable to n=80).

---

## ⚠️ TL;DR — the repo's Thm 3.4 work formalizes the WRONG recurrence (ε and ½ are swapped)

**The headline finding is a bug, not a curiosity.** `notes/ST06-THM34-FINDINGS.md`,
`tools/sandbox/st06_thm34_verify.py`, and `St06Thm34.lean` all use this recurrence:

> `u_{n+1} = ⌊a(uₙ + ½)⌋` if n **odd**,  `⌊b(uₙ + ε)⌋` if n **even**   ← ε on the b-step

That is the shape of **Theorem 3.3**, not 3.4. Stoll's **Theorem 3.4** (verbatim, p. 93–94) is:

> `u_{n+1} = ⌊a(uₙ + ε)⌋` if n **odd**,  `⌊b(uₙ + ½)⌋` if n **even**   ← ε on the a-step

i.e. **ε ↔ ½ are swapped between 3.3 and 3.4.** (Only the `a`-formula was carried over correctly:
3.4 uses `a = 2k+1 + 2l/(t+2m)`, which the repo has right; 3.3 uses `a = 2k+1 + (t+2l)/(t+2m)`.)
The proof confirms the placement: on p. 99 the **`u_{2n−1}→u_{2n}` step (n odd) is the one carrying
ε**; the `u_{2n}→u_{2n+1}` step (n even) carries ½ and is dispatched as "obviously true."

**Consequence:** the repo's central Thm 3.4 conclusion — *"the printed interval is NOT t-universal,
only ε=½ works for all w"* (`st06_thm34_band_fails_below_half` / `_above_half`) — is **an artifact of
the swap**. It is a true statement about the swapped (3.3-placement) recurrence, but **false about
Stoll's actual Theorem 3.4**. Stoll's printed interval is genuine and correct (details below).

**Why the ε=½ formalization is still fine:** at ε=½ both steps use ½, so the swap is invisible. The
repo's `st06_thm34` digit conclusion *at ε=½* is valid as-is. It just isn't "the honest ceiling" — it
sits in the interior of a real, wider interval.

---

## (1) Exact statement + exact ε-interval

**Theorem 3.4.** Let `w ∈ ℝ⁺`, `t = w/2^M = (d₁.d₂d₃…)₂`, `M = ⌊log₂ w⌋`. Let `m, l, k ∈ ℤ` with
`m ∉ {−1, 0}`, `k ≥ 0`, and

- `1 ≤ l ≤ m`        if `m ≥ 1`,
- `m+1 ≤ l ≤ −1`    if `m ≤ −2`.

Define `u₁ = m`, and

> `u_{n+1} = ⌊a(uₙ + ε)⌋`  (n odd),   `u_{n+1} = ⌊b(uₙ + ½)⌋`  (n even),
> `a = 2k+1 + 2l/(t+2m)`,   `b = 2/a`.

ε-interval — **symmetric about ½** (this fills the `(…)` your `notes/ST06-PLAN.md` left blank; the
upper numerator equals the lower one):

- **`m ≥ 1`:**  `½ − (m−l+½)/((2k+1)(2m+1)+2l)  ≤  ε  <  ½ + (m−l+½)/((2k+1)(2m+1)+2l)`
  → **lower endpoint closed `≤`, upper endpoint OPEN `<`.**
- **`m ≤ −2`:** `½ − (m−l+1)/(2(2k+1)(m+1)+2l)  ≤  ε  ≤  ½ + (m−l+1)/(2(2k+1)(m+1)+2l)`
  → **both endpoints closed `≤ … ≤`** (as printed; the m≤−2 branch genuinely prints a closed upper
  bound, unlike m≥1 — flagging in case it matters, but it won't for w=√2 work where m≥1).

Conclusions (both as printed): `u_{2n+1} − 2u_{2n−1} = dₙ` **and** `u_{2n+2} − 2u_{2n} = dₙ + k(2dₙ−1)`.
(The second conclusion's leading term is printed `dₙ` for 3.4, vs `d_{n+1}` for 3.3 — low-confidence
on that subscript from the scan; verify against the PDF if you ever pursue conclusion (2). You noted
(2) "differs from 3.3 / not pursued", so it doesn't affect the headline.)

**Numerical confirmation (w=√2, paper recurrence, to n=80):** the empirically digit-correct ε-range
**contains Stoll's printed interval** in every case tested — Stoll's interval is correct and slightly
conservative:

| (m,l,k) | Stoll printed interval | empirical digit-correct range (n=80) |
|---|---|---|
| (1,1,0) | [0.40000, 0.60000) | [0.36725, 0.63762] |
| (2,1,0) | [0.28571, 0.71429) | [0.26825, 0.73538] |
| (2,2,0) | [0.44444, 0.55556) | [0.42238, 0.58325] |
| (2,1,1) | [0.41176, 0.58824) | [0.40587, 0.59562] |
| (3,2,1) | [0.44000, 0.56000) | [0.43412, 0.56788] |
| (4,3,2) | [0.47059, 0.52941) | [0.46725, 0.53425] |

(For contrast, the **swapped** recurrence collapses every one of these to a ~0.49–0.50 band — that's
the spurious "only ε=½" the repo currently reports.)

## (2) Per-`w` or t-universal? → **t-universal (uniform over all w).**

Stoll states it per-`w` (w/t are fixed at the top), but the **proof bounds the ε-step for all
`1 ≤ t < 2` simultaneously** (he writes "for all `1 ≤ t < 2`"), so the interval is uniform over every
`w`. It is t-universal in your sense. The empirical √2 range is a touch *wider* than Stoll's interval
precisely because √2's particular orbit doesn't realize the absolute worst case — Stoll's interval is
the all-`w` (worst-orbit) interval, hence a correct, conservative, uniform bound.

## (3) Does the ε-step proof use a Diophantine property of `t`? → **No.**

The `u_{2n−1}→u_{2n}` (n-odd, ε) step reduces (p. 99, m≥1) to

> `0 ≤ ((t+2m)(2k+1)+2l)·ε − k(t+2m) + l·ξ″ < t+2m`,  where `ξ″ = 2⌊t·2^{n−2}⌋ − t·2^{n−1} ∈ (−2, 0]`.

Note `ξ″ = −2·{t·2^{n−2}}` (a single fractional part). Stoll then bounds it by worst-casing
**`t ∈ [1,2)` and `ξ″ ∈ (−2,0]` independently** (plain endpoint algebra: `t→1` minimizes the
denominator-bearing terms, `ξ″→−2` / `ξ″=0` give the numerator extremes), yielding exactly the
symmetric interval above. **No equidistribution / normality / Diophantine input.** This works as a
*sufficient* condition because the actual coupled set `{(t, −2{t·2^{n−2}})}` is a subset of the box
`[1,2)×(−2,0]`, so the independent worst case can only over-cover. That's why the bound is uniform and
correct (and a little loose vs any single w).

**This is structurally the "eq-(8) uniform" case, NOT the pair-5 case.** In pair 5
(`ON-LINE-FINDINGS-2026-06-06-pair5.md`, a *different* paper, arXiv:0902.4168 Thm 3.2) the ε-step
bracket is crux-shaped `{x} − √2{x/2} + √2ε` — non-uniform, genuinely Diophantine, interval really
false beyond ε=½. Thm 3.4's ε-step bracket is **linear in one fractional part bounded over its full
range**, like the well-behaved pairs 1,2,4,6,8. **The repo's "mirrors pair 5 exactly" claim is the
swap talking** — the swap moved ε onto the non-uniform step and manufactured a pair-5 look-alike.

---

## What to do in Lean (actionable)

1. **Fix the recurrence** in `St06Thm34.lean` / `notes/ST06-THM34-FINDINGS.md` /
   `tools/sandbox/st06_thm34_verify.py`: ε on the **n-odd (a) step**, ½ on the **n-even (b) step**.
2. **Retire / re-label** `st06_thm34_band_fails_below_half` and `_above_half` and the
   "NOT t-universal" narrative. They are sound Lean about the *3.3-placement* recurrence but are
   **not** statements about Theorem 3.4. (Classic faithful-proof / unfaithful-statement trap — the
   `#print axioms` clean bill says nothing about whether the statement matches the paper.)
3. **You can now formalize the FULL interval as a genuine theorem** (unlike pair 5). The closed forms
   are `u_{2n−1} = m·2^{n−1} + ⌊t·2^{n−2}⌋` (4.10) and
   `u_{2n} = (m+l)·2^{n−1} + ⌊t·2^{n−2}⌋ + k(m·2ⁿ + 2⌊t·2^{n−2}⌋ + 1)` (4.11); the ε-step closes via
   the single bracket `0 ≤ Dε − k(t+2m) + lξ″ < t+2m`, `ξ″ = −2{t·2^{n−2}} ∈ (−2,0]`, `D=(t+2m)(2k+1)+2l`,
   bounded by independent worst-case over `t∈[1,2)` and `ξ″∈(−2,0]`. The ½-step (4.10→4.11 even) is
   the "obviously true" `0 ≤ (t+2m)(2k+1)(1−dₙ) + l(t·2ⁿ − 2⌊t·2^{n−1}⌋) < (t+2m)(2k+1)+2l`. No
   `native_decide`, no Diophantine machinery — this is a clean target.

## Faithfulness flags
- **The swap (ε/½ placement)**: high confidence (98%). Verified against the PDF statement (p. 93–94)
  AND the proof's own step labels (p. 99), AND the controlled numeric A/B test (same harness, only the
  placement differs: paper→wide interval ⊇ Stoll's; swapped→collapses to ~½).
- **Symmetric interval + open/closed endpoints**: high (95%). Transcribed from the PDF and
  independently re-derived from the proof's middle-term identities
  (`(k(1+2m)+2l)/D₁ = ½−(m−l+½)/D₁`, `((k+1)(2m+1))/D₁ = ½+(m−l+½)/D₁`).
- **t-universal / no Diophantine input**: high (95%). The proof literally says "for all 1 ≤ t < 2" and
  uses only interval endpoints of `t` and `ξ″`.
- **Conclusion (2) subscript `dₙ` vs `d_{n+1}`**: low confidence (scan legibility); irrelevant to the
  headline, re-check the PDF if pursuing (2).
