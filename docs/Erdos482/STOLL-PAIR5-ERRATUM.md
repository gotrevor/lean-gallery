# Erratum / caveat: Stoll, *A fancy way to obtain the binary digits of 759250125√2*, Theorem 3.2, pair i=5 (t₅=√2)

Paper: T. Stoll, *Amer. Math. Monthly* **117** (2010), no. 7, 611–617 (arXiv:0902.4168). Page references
below are to the arXiv version. Two issues in Stoll's **Theorem 3.2** (p. 2; the proof is in §4), pair
`i=5` (`t₅=√2`), found while formalizing the result in Lean 4,
both verified by **exact integer arithmetic** (`math.isqrt`, no floating point). Reproduction scripts:
[`tools/sandbox/`](tools/sandbox/) (`stoll_pair5_verify.py`, `stoll_pair5_digits.py`,
`stoll_pair5_shrink.py`). A fuller write-up — the mechanism (tie to Stoll's remark (d) / normality of √2),
the horizon-contraction table, and a map of the Lean formalization — is in
[`NOTES-ON-STOLL-2010.md`](NOTES-ON-STOLL-2010.md). Detailed derivation:
[`archive/findings/ON-LINE-FINDINGS-2026-06-06-pair5.md`](archive/findings/ON-LINE-FINDINGS-2026-06-06-pair5.md).

## 1. Typo in the pair-5 closed form (certain)
In the §4 proof, the `i=5` paragraph (p. 5) prints:  `v_{2k} = ⌊t₅·2^{k−2}⌋ + 2^{k−2}`.
This is **wrong** (gives v₂=0.5, v₄=2; true v₄=4). The correct formula is
> `v_{2k} = ⌊√2·2^{k−1}⌋ + 2^{k−1}`,  `v_{2k+1} = ⌊√2·2^{k−1}⌋ + 2^k`  (k ≥ 1),
both sharing the floor `⌊√2·2^{k−1}⌋`. (`v_{2k+1}` is correct as printed.) Verified by exact
integer arithmetic.

## 2. The pair-5 interval claim is too wide (substantive — not just a typo)
Theorem 3.2 (the i=5 row, p. 2) and remark (b) (p. 3) claim the digits of √2 are obtained for **any** ε in
`[309/2·√2−218, 1296121037/2·√2−916495974) ≈ [0.4959953, 0.5012400)`.
**False as an "all-n" statement.** Exact computation: at the *included* lower endpoint
ε=ξ₁,₅ the digit claim **fails at n=280**; the true admissible ε-set shrinks toward `{½}` as the
digit-horizon grows (governed by `{√2·2^m} → ½`, i.e. the base-2 normality of √2 — the very
connection Stoll flags in remark (d) (p. 3) but never applies to pair 5). Stoll's endpoints are the
**small-horizon** extremes (m≲28), inherited from the pair-4/pair-6 boundaries; he then wrongly
assumed the whole leftover gap is pair-5 territory. Cross-check: pairs 1,2,4,6,8 (eq-8 uniform) DO
hold over their full intervals to n=1500 with the same machinery — only pair 5 fails.

## Consequence for the formalization
Pair 5 (digits of √2) is a genuine theorem **only at ε=½** (the original Graham–Pollak), where the
ε-step is exactly the universal `crux` `0≤{x}−√2{x/2}+√2/2<1`. That is the case formalized here. The
open interval is **not** claimed: it is not an elementary theorem (it is open-Diophantine /
normality-flavored) and the stated endpoints provably fail (n=280, above). So this repo scopes pair 5 to
ε=½ and records the honest content instead — the typo-corrected closed form, the exact ε-step band
characterization, and a conditional full-interval theorem.
