# St06 Theorem 3.4 — numerical findings (2026-06-13)

Thm 3.4 is the "other binary family": `a = 2k+1 + 2l/(t+2m)`, `b = 2/a`, `1 ≤ l ≤ m`, `m ≥ 1`,
`k ≥ 0`, `t ∈ [1,2)`. Same recurrence shape as 3.3 (`u₁=m`, `u_{n+1}=⌊a(uₙ+½)⌋` n odd,
`⌊b(uₙ+ε)⌋` n even).

## Closed forms (verified 0/4000 random `(m,l,k,t)`, n→24)
* **odd** `su(2j)   = m·2ʲ + ⌊t·2ʲ/2⌋`            (IDENTICAL to Thm 3.3 / the universal odd form)
* **even** `su(2j+1) = (2k+1)·(m·2ʲ+⌊t·2ʲ/2⌋) + k + l·2ʲ`   (DIFFERENT from 3.3)

So conclusion (1) `su(2n) − 2·su(2n−2) = nth binary digit of w` is the SAME statement as 3.3 and
follows from `digit_of_evenClosed_coeff` once the odd form is proved.

## The ε-interval is Diophantine, NOT a t-universal elementary interval ⚠️
The crux analysis: `a`-step is unconditional; `b`-step needs `0 ≤ (1−d) − b(ρ−ε) < 1` with the
a-step fractional part `ρ = ½ + l(1−2x)/(t+2m)`, `x = {t·2^{j−1}} ∈ [0,1)`, `d = ⌊2x⌋ ∈ {0,1}`.
- For **d=0** (x<½): ρ ∈ (½, ½+l/(t+2m)] ⇒ needs ε ≤ ½.
- For **d=1** (x≥½): ρ ∈ (½−l/(t+2m), ½] ⇒ needs ε ≥ ½.

The two ρ-ranges **MEET at ½** (unlike Thm 3.3, whose d=0 / d=1 ρ-ranges are *separated*, leaving a
genuine t-universal interval `½ ± (2l+1)/(2(2m+1))`). So requiring the b-crux for *all* `x ∈ [0,1)`
forces **ε = ½** exactly. A numerical scan for `w=√2` shows a stable narrow asymmetric band (e.g.
`(1,1,0)`: `[0.49450, 0.50175]`, width 0.00725, stable past n=40) — that width is `√2`-specific (the
digits of √2 avoid the boundary `x=½`), exactly the **pair-5 Diophantine phenomenon**. Stoll's
printed k-dependent interval `½−(m−l+½)/((2k+1)(2m+1)+2l) ≤ ε < ½+(…)` is therefore a t-/w-specific
claim, NOT t-universal; the symmetric guess fails (`c1` fails at the lower endpoint for √2).

## What we formalize (honest, t-universal): the ε=½ case
At **ε=½** the b-crux holds for *all* `t∈[1,2)` (both d-cases close with room): see `St06Thm34.lean`.
This gives Thm 3.4's digit conclusion (1) for every real `w>0`. The full Diophantine interval is left
as `ON-LINE-REQUEST` (need the St06 PDF's exact Thm 3.4 statement + proof to know whether Stoll's
interval is per-w or a transcription artifact, mirroring the pair-5 erratum).

(Conclusion (2) of the 3.3-style `d_{n+1}+k(2dₙ−1)` does NOT hold for 3.4 — the even form differs;
`su(2j+1)−2·su(2j−1) = (2k+1)·dₙ + (l−... )`-type, not pursued.)

## FORMALIZED RESOLUTION (2026-06-13) — the full interval is NOT a t-universal theorem ✅
The Diophantine obstruction above is now **machine-checked** in `St06Thm34.lean` (all axiom-clean):
* `st06_thm34_bstep_value` — exact general-ε b-step value: `b(E'+ε) = 2(ms+B)+1 − frac`,
  `frac = (2·Nq − 2(t+2m)ε)/Da`, `Nq=(t+2m)/2 + l(1−t·s+2B)`, `Da=(2k+1)(t+2m)+2l`.
* `st06_thm34_bstep_band` — the b-step lands on the digit value `2ms+C` **iff** `frac ∈ (−d, 1−d]`,
  `d=C−2B∈{0,1}` (the exact admissible band; analogue of `pair5_estep_band`).
* `st06_thm34_band_fails_below_half` — ε<½, a `d=1` boundary step (`C=2B+1`, `t·s` near `C`) has
  `frac>0=1−d` ⇒ band's upper bound fails ⇒ b-step misses `2ms+C`.
* `st06_thm34_band_fails_above_half` — ε>½, a `d=0` boundary step (`C=2B`, `t·s` near `C+1`) has
  `frac<0=−d` ⇒ band's lower bound fails.
Together: no single `ε≠½` keeps `frac` in the band for *all* fractional parts, so Stoll's printed
k-dependent interval cannot be a `t`-universal digit theorem (the conclusion "digits of `w`" holds for
all `w` only at ε=½). This mirrors exactly how pair 5 was resolved. **Open St06 items: none.**
