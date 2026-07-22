# ON-LINE-FINDINGS — Stoll Theorem 3.2, pair i=5 (t₅=√2, β=0)

**Request:** 2026-06-06 item in `ON-LINE-REQUEST.md` — the exact (5)/(6) analogue for pair 5,
and how Stoll makes the ε-step land for *all* ε in pair 5's interval.

**Sources read:** T. Stoll, *A fancy way to obtain the binary digits of 759250125√2*,
arXiv:0902.4168 — full HTML via `ar5iv.labs.arxiv.org/html/0902.4168` (the `<math alttext>` =
author's own LaTeX, so the quotes below are verbatim, not OCR). I re-read §3 (Thm 3.2 statement +
remarks a–d), and §4 lines covering eqs (5)–(9) and the `i=5` paragraph. Every claim below is
**verified in exact integer arithmetic** (`math.isqrt`, no float error) — scripts
`tools/sandbox/stoll_pair5_verify.py`, `stoll_pair5_digits.py`, `stoll_pairsI_verify.py`,
`stoll_pair5_shrink.py` on the host.

---

## TL;DR (the two things that unblock you)

1. **Your transcription was faithful; Stoll's formula has a TYPO.** The paper literally prints
   `v_{2k}=⌊t_i 2^{k−2}⌋+2^{k−2}` for i=5 — so the prior findings copied it correctly. But it is
   **wrong** (it gives v₄=2, even v₂=0.5; true v₄=4). The **correct** pair-5 formula is

   > **v_{2k} = ⌊√2·2^{k−1}⌋ + 2^{k−1}**   and   **v_{2k+1} = ⌊√2·2^{k−1}⌋ + 2^k**,  k ≥ 1.

   (Exponent `k−2`→`k−1` in BOTH terms of v_{2k}; the v_{2k+1} formula is correct as printed.)
   Note both share the **same floor** `⌊√2·2^{k−1}⌋`.

2. **Stoll gives NO uniform ε-step argument for pair 5, and the full-interval claim is essentially
   false.** He writes (verbatim): *"the case i=5 … is less involved … we directly show that … for
   k≥1 … (We leave the details to the interested reader.)"* For ε≠½ the pair-5 ε-step is genuinely
   the ε-perturbed crux `{x}−√2{x/2}+√2ε`, which is **not uniform** and **fails at finite n**
   (proven: at ε=ξ₁,₅ it fails at **n=280**). Pair 5 (digits of √2) holds for **all** n **only at
   ε=½** — the original Graham–Pollak, which is exactly your already-formalized headline case.

   **➡ Recommendation: formalize pair 5 at ε=½ only. Do NOT chase the full interval — it is not an
   elementary theorem (it's an open Diophantine/normality statement), and Stoll's stated interval is
   demonstrably too wide.** See "What to do in Lean" at the bottom.

---

## Verbatim: Stoll's §4 treatment of i=5

> "Finally, we have to treat the case `i=5`, which is less involved than the cases `i∈I`. Here we
> directly show that
>
> `  v_{2k} = ⌊t_i 2^{k−2}⌋ + 2^{k−2}   and   v_{2k+1} = ⌊t_i 2^{k−1}⌋ + 2^k`
>
> for `k≥1`, so that we do not have to bother about initial conditions. (We leave the details to the
> interested reader.)"

That is the **entire** pair-5 proof in the paper. The `v_{2k}` formula here is the typo.

### Numerical proof of the typo (ε=½, exact integer arithmetic)

v-sequence at ε=½ (= the GP sequence): `1,2,3,4,6,9,13,19,27,38,54,77,109,154,218,309,…`

| k | actual v_{2k} | printed `⌊√2·2^{k−2}⌋+2^{k−2}` | corrected `⌊√2·2^{k−1}⌋+2^{k−1}` |
|---|---|---|---|
| 1 | 2 | 0.5 ✗ (not even integer!) | 2 ✓ |
| 2 | 4 | 2 ✗ | 4 ✓ |
| 3 | 9 | 4 ✗ | 9 ✓ |
| 4 | 19 | 9 ✗ | 19 ✓ |
| … | … | (always wrong) | (always ✓) |

`v_{2k+1}=⌊√2·2^{k−1}⌋+2^k` is correct as printed (3,6,13,27,54,109,…✓).
Digit extraction `d_n = v_{2n+1}−2v_{2n−1}` = the (n−1)-th binary bit of √2 (d₁ = integer bit 1,
d₂ = first fractional bit 0, …) — verified to n=600 at ε=½.

---

## Why pair 5 doesn't fit your `crux`/`eq8_general` template (the structural swap)

Recall Stoll's recurrence (Def 3.1): the **ε-step** makes the even-index terms
(`v_{2k}=⌊√2(v_{2k−1}+ε)⌋`, since n=2k−1 is odd) and the **½-step** makes the odd-index terms
(`v_{2k+1}=⌊√2(v_{2k}+½)⌋`).

**For i∈I**, the floor arguments of v_{2k} and v_{2k+1} differ by a factor 2 (`t·2^{k−2}` vs
`t·2^{k−1}`), and the two steps reduce to:
- ½-step (5)⇒(6) → eq (7) = the **universal crux** `0≤{x}−√2{x/2}+√2/2<1`.
- ε-step (6)⇒(5) → eq (8) `0≤(1−√2){α√2·2^{k−l−1}}+√2ε<1`, **uniform** for all ε∈[1−√2/2,√2/2).

**For pair 5**, v_{2k} and v_{2k+1} share the **same** floor `⌊√2·2^{k−1}⌋`, so the roles swap:
- ½-step → `0≤(1−√2){√2·2^{k−1}}+√2/2<1` (= eq 8 at ε=½). Always holds. Fine.
- ε-step → `0 ≤ {x} − √2{x/2} + √2·ε < 1` with **x=√2·2^k** (so {x/2}={√2·2^{k−1}}).
  This is the **crux shape but ε-perturbed**. It equals the universal crux **only when ε=½**.

So your read in the request is exactly right: pair-5's ε-step bracket is `{x}−√2{x/2}+√2ε`, not
eq8's `(1−√2){y}+√2ε`. (Derivation: with F=⌊√2·2^{k−1}⌋, √2·F = 2^k − √2{√2·2^{k−1}}, and the
floor collapses to the bracket above. Confirmed two independent ways + numerically.)

### Why ε≠½ breaks it
The crux only gives `{x}−√2{x/2} ∈ [−√2/2, 1−√2/2)`. Adding √2ε instead of √2/2 shifts this by
√2(ε−½). For ε>½ the upper wall (value→1) is at risk; for ε<½ the lower wall (value→0) is at risk.
The extreme of `{x}−√2{x/2}` is approached exactly when **{√2·2^m} → ½** (from below → sup
1−√2/2; from above → inf −√2/2). So the ε-step requires `{√2·2^m}` to **avoid a band around ½**
for all m — an infinitary property of √2's binary digits. **This is the crux you correctly
identified, and it has no elementary uniform bound.**

---

## The bombshell: the stated pair-5 interval is too wide (exact computation)

Stoll, Thm 3.2 / remark (b): *"The binary digits of √2 are obtained for any choice of ε in the
interval `[0.4959953…, 0.5012400…)`"*, i.e. `ε₅ ∈ [309/2·√2−218, 1296121037/2·√2−916495974)`.

Exact integer recurrence (digits of √2, ε of the exact algebraic form (c/2)√2−d):

| ε | first n where d_n ≠ bit of √2 |
|---|---|
| **ε = ½** (interior, GP) | **none** (holds ∀ n; tested to 4000, provable via crux) |
| **ε = ξ₁,₅ = 309/2·√2 − 218 ≈ 0.4959954** (the *included* lower endpoint!) | **fails at n = 280** |
| ε = ξ₂,₅ ≈ 0.5012401 (excluded upper) | fails at n = 30 |

**Sanity check that this is not a setup bug:** with the identical machinery, pairs 1,2,4,6,8 at
their *included* lower endpoints hold over their full intervals to **n=1500 with zero failures**
(they enjoy eq-8 uniformity). Only pair 5 fails. This matches your report that pairs 1–4,6,7,8
formalize cleanly over full intervals — and isolates pair 5 as the genuine exception.

### The true admissible interval shrinks toward {½}

Admissible ε = {ε : ∀m≤H, the band condition holds}, as a function of the digit-horizon H:

| H (horizon) | true admissible ε-interval | width | binding m |
|---|---|---|---|
| 50  | [0.4959954, 0.5012401) | 5.2e-3 | (6, 28) |
| 200 | [0.4959954, 0.5012401) | 5.2e-3 | (6, 28) |
| 600 | [0.4995421, 0.5006323) | 1.1e-3 | (451, 333) |
| 2000 | [0.4995969, 0.5001184) | 5.2e-4 | (1300, 1400) |
| 6000 | [0.4998082, 0.5000042) | 2.0e-4 | (5332, 3064) |

**At small horizon (H≤~28) the admissible interval is EXACTLY Stoll's stated interval.** As H grows,
`{√2·2^m}` finds closer approaches to ½ (binding m climbs: 28→333→1400→5332), and the interval
collapses toward `{½}`. So **Stoll's endpoints are the small-horizon extremes of {√2·2^m}** —
they happen to coincide with the pair-4/pair-6 boundary values (ξ₁,₅=ξ₂,₄, ξ₂,₅=ξ₁,₆, fixed by the
*neighbors'* finite eq-(9) computations at l₄=7, l₆=29, i.e. m up to ~30). Stoll then assumed the
leftover gap is entirely pair-5 territory. It isn't.

### Stoll knew the obstruction (remark (d), verbatim)
> "(d) There is also a connection to normal numbers… Suppose there exists c₁ with
> `{√2·2^{k−1}} ≤ c₁ < 1` for all k≥1. Then – according to (8) – the interval given for ε₁ can be
> enlarged… The inequality (3) implies that √2 is not normal in base two…"

He ties **interval extensibility to non-normality of √2** for ε₁ and ε₈, but never circles back to
note that the **same mechanism shrinks pair 5's own interval to {½}**. If √2 is normal in base 2
(believed, unproven), `{√2·2^m}` is equidistributed ⇒ gets arbitrarily close to ½ from both sides ⇒
the only ε that works for all n is ε=½. So the full-interval pair-5 claim is, at best, equivalent to
an open Diophantine statement, and as a "holds for all n" theorem it is false at the stated
endpoints.

---

## What to do in Lean (actionable)

The request asked: *does pair 5 need new Diophantine machinery, or is there an elementary finite
proof?* **Answer: neither — the full-interval target is not a theorem.** Concretely:

1. **Formalize pair 5 only at ε = ½** (the Graham–Pollak case). There the ε-step is *exactly* the
   universal `crux` `0≤{x}−√2{x/2}+√2/2<1` and the ½-step is `(1−√2){y}+√2/2` (= eq8 at ε=½, an
   easy interval bound). Both reusable lemmas you already have. The clean statements to prove:
   - `v_{2k} = ⌊√2·2^{k−1}⌋ + 2^{k−1}` and `v_{2k+1} = ⌊√2·2^{k−1}⌋ + 2^k` (k≥1), then
   - `d_n = v_{2n+1} − 2 v_{2n−1} = (n−1)-th binary digit of √2`.

   This *is* the true mathematical content of pair 5 (and is your existing headline). Axiom-clean,
   no Diophantine machinery, no native_decide.

2. **Do not state pair 5 for the open interval [ξ₁,₅, ξ₂,₅).** If you want a complete Theorem-3.2
   formalization covering all 8 pairs, scope pair 5 to ε=½ and add a docstring/`NOTE` recording that
   Stoll's stated interval is the small-horizon (m≲28) interval, not an all-n theorem (cite this
   findings file; the lower endpoint provably fails at n=280). That keeps the repo honest and
   axiom-clean rather than chasing a false target or smuggling in an unprovable axiom.

3. **If you ever want the sharp positive statement**, it is: *the interval for ε₅ can be taken as
   `[ξ, √2−ξ]`-type only under an explicit hypothesis* `{√2·2^{m}} ∉ (½−δ, ½+δ) for all m` (a
   non-normality / Diophantine hypothesis). That's the honest "conditional" version, mirroring how
   Stoll's remark (d) conditionally enlarges ε₁/ε₈. Not recommended unless you specifically want the
   conditional theorem.

---

## Faithfulness flags
- **Typo claim (k−2→k−1)**: verified by exact arithmetic — the printed formula gives a non-integer
  at k=1; the corrected one matches the recurrence for all k. High confidence it's a genuine paper
  typo in the "leave to the reader" line.
- **"Full interval is false" claim**: verified by exact integer recurrence (ε=ξ₁,₅ fails at n=280)
  and cross-checked against the i∈I pairs holding to n=1500 with the same code. High confidence.
- **"Collapses to exactly {½}"**: strongly supported numerically (band shrinks monotonically, binding
  m climbs) and consistent with normality of √2, but the *exact* limiting set ({½} vs a measure-zero
  Diophantine set) is open-problem-adjacent. The actionable facts (Stoll's endpoints fail; ε=½ is
  robust) do not depend on resolving this.
