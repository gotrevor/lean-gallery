# St06 Theorem 3.1 — ε-interval erratum (subcone 𝒟₂⁻)

**Date:** 2026-06-13. **Status:** numerically established (~1M test points), not yet read off the
original PDF (box has no internet; the PDF is gitignored). Treat as a verified working correction.

## The discrepancy

`notes/ST06-PLAN.md` transcribes St06 Theorem 3.1's offset condition as

> `1 + γᵢ⁺ ≤ ε < 1 + δᵢ⁺` (resp. `1 + γᵢ⁻ ≤ ε < 1 + δᵢ⁻`)

with (Def 2.4) for subcone 𝒟₂⁻:
`γ₂⁻ = (g−l−1)(mg+1)/(klg)` and `δ₂⁻ = −(mg+1)/(kg)`.

Taken literally, the **upper** endpoint `1 + δ₂⁻` is **too large** and the digit-extraction fails.

## What is actually true (verified)

Re-deriving the even→odd induction step from the two St06 closed forms
`u_{2n+1} = m·gⁿ + ⌊t·g^{n−1}⌋`, `u_{2n} = l(k·gⁿ−1)/(g−1)` gives the reduced core inequality

> for all fractional parts `f ∈ [0,1)`:  `0 ≤ l/(g−1) + a·(ε − f) < 1`,  with `a = klg/((g−1)(t+mg))`.

Since `a < 0` on 𝒟₂⁻ (k<0, l>0, g≥3, t+mg>0), the expression is increasing in `f`; the two
endpoints give:

- **lower** ε-bound (from `core < 1`): `ε ≥ 1 + (g−l−1)(mg+1)/(klg)` = `1 + γ₂⁻`  ✓ (matches plan, **with** the +1)
- **upper** ε-bound (from `core ≥ 0`): `ε < −(mg+1)/(kg)` = `δ₂⁻`  — **NO "+1"**.

So the correct condition for 𝒟₂⁻ is

> **`1 + γ₂⁻ ≤ ε < δ₂⁻`**, i.e. `1 + (g−l−1)(mg+1)/(klg) ≤ ε < −(mg+1)/(kg)`.

The lower endpoint keeps the `1+`; the upper endpoint does not. (Both `γ` and `δ` are pinned at the
worst mantissa `t = 1`; for `t > 1` the admissible interval is strictly wider, but the theorem must hold
for all `1 ≤ t < g`, so the `t=1` endpoints govern.)

## Evidence

- With the plan's `ε < 1 + δ₂⁻`: counterexample g=3, m=1, l=1, k=−1, t≈1.27, ε≈1.93, f=0 →
  `l/(g−1)+a(ε−f) = −0.18 < 0`, so `⌊a(u_{2k}+ε)⌋` lands one below the claimed closed form.
- With the corrected `ε < δ₂⁻`: **0 failures over 994 800** random `(g,m,l,k,t,ε,f)` points
  (g∈[3,9], m∈[1,7], 0<l≤g−1, k<0, t∈[1,g), ε∈[1+γ₂⁻,δ₂⁻), f∈{0,.2,.5,.8,1⁻}).
- Cross-check: the showcase **Example 1.1** (g=3, m=3, l=2, k=−1, ε=π) lies in the corrected interval
  `[1, 10/3)` (π ≈ 3.14 < 10/3 ≈ 3.333) but the plan's `[1, 13/3)` would also (wrongly) admit ε up to
  4.33, where the extraction breaks (ε=4 already fails at t=1).

## Caveat / likely reading

This is consistent with Stoll's Def 2.4 defining `δ₂⁻` so that the *condition* reads `1+γ ≤ ε < δ`
(asymmetric), **or** with a `δ₂⁻` that is one less than the value the plan recorded. Either way the
numerically-correct interval is the boxed one above. Confirm against the PDF when available; until then
**formalize against the corrected (verified) interval**, per the repo's "verify, don't trust" rule
(cf. `STOLL-PAIR5-ERRATUM.md`).

## General rule — verified for ALL 12 sub-subcones (2026-06-13)

Re-deriving the core for every cone (the reduction `0 ≤ l/(g−1)+a(ε−f) < 1` is cone-independent; only
the ε-endpoints differ) and matching the endpoints against St06's Def 2.4 `γᵢ±, δᵢ±` gives a **single
uniform correction**:

> **The St06 Thm 3.1 offset condition is `1 + γᵢ^s ≤ ε < δᵢ^s`** (for cone `i`, sign `s∈{+,−}`).
> The lower endpoint keeps the `+1`; the **upper endpoint has NO `+1`**.  The plan's transcription
> `… < 1 + δᵢ^s` over-shoots the upper endpoint on every cone.

With `γ, δ` read off Def 2.4's four lines:

| line | value | appears as |
|---|---|---|
| L1 | `−(mg+1)/(kg)`        | `γ₂⁺ δ₂⁻ γ₃⁺ δ₃⁻ γ₄⁺ δ₄⁻` |
| L2 | `(g−l−1)(mg+1)/(klg)` | `δ₂⁺ γ₂⁻ γ₁⁺ δ₁⁻ γ₆⁺ δ₆⁻` |
| L3 | `−(m+1)/k`            | `δ₅⁺ γ₅⁻ δ₁⁺ γ₁⁻ δ₆⁺ γ₆⁻` |
| L4 | `(g−l−1)(m+1)/(kl)`   | `γ₅⁺ δ₅⁻ δ₃⁺ γ₃⁻ δ₄⁺ γ₄⁻` |

**Evidence:** `1 + γᵢ^s ≤ ε < δᵢ^s` gives **0 failures over ~250 000** `(g,m,l,k,t,ε,f)` points across
**all 12** sub-subcones (𝒟₁..𝒟₆, both signs), `g∈[3,8]`, `m∈[1,7]∪[−7,−2]`, `t∈[1,g)`, `f∈{0,½,1⁻}`,
including the `Ω₂` cones (`m ≤ −2`, where `t+mg < 0`).  The plan's `< 1+δ` fails on every cone.

So **formalize each cone against `1 + γᵢ^s ≤ ε < δᵢ^s`** (lower keeps the +1, upper drops it).  The
`src/Erdos482/General/St06Thm31.lean` `d2m_core`/`d2p_core` lemmas already do this for 𝒜₂; the other
cones are the same proof shape with the line-`Lk` endpoints substituted (watch the sign of `t+mg`:
positive on `Ω₁`/𝒟₁₋₃, negative on `Ω₂`/𝒟₄₋₆, which flips the `÷(g−1)(t+mg)` step).
