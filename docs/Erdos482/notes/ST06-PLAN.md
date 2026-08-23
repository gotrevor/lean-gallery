# St06 formalization plan (fun extension) — branch `st06`

**Source:** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125** (2006),
no. 1, 89–100. DOI 10.4064/aa125-1-8. Zbl 1167.11302. MSC 11B37, 11A63. (Solo Stoll — NOT Fuchs.)

This is an **optional "for fun" extension** of the (complete, axiom-clean) #482 work, on branch `st06`.
**The box has no internet and the PDF is gitignored**, so the statements you need are transcribed below
(faithfully, from the paper). **Rules: (1) DO NOT push — work stays on `st06` locally. (2) verify-don't-
trust — numerically check every formula before formalizing (pair 5 had a false interval AND a typo; St06
formulas are unverified except Example 1.1). (3) reuse the existing machinery — `Crux`, `Induction`,
`Digits`, and especially `General/` (Prop 2 = `digitStep`/`gdigit`, the `thm13`-style closed-form
induction). Commit when green (the `.githooks/pre-commit` gate runs `lake build`).**

St06 does NOT supersede St05 (the general base-g resolution, already formalized). It adds: a 3-parameter
`(m,l,k)` *family* of recurrences (Thm 3.1), striking examples (Example 1.1), two extra binary families
(Thms 3.3/3.4), and a Beatty-theorem unification (Cor 3.5).

---

## Notation (St06 §2)

`g∈ℤ, g≥2`; `w∈ℝ⁺` with base-g expansion `w = Σ_{i≥1} dᵢ·g^{M−i+1}`, `dᵢ∈ℤ`, `0≤dᵢ<g`, `d₁≠0`.
`M = ⌊log_g w⌋`, `t = w/g^M`, so `t = (d₁.d₂d₃…)_g` with `1 ≤ t < g`. (Same `t`/`M` as our `General/`.)

---

## TIER 1 — Example 1.1 (ternary digits of e) ✅ VERIFIED — do this first

A self-contained showcase (the analogue of `cor33_unconditional` / `Cor13e`). **Already numerically
verified** by `tools/sandbox/st06_example11_verify.py` (matches e's ternary digits to n=40, exact).

> Define `v₁ = 3`,
> `v_{n+1} = ⌊ −3/(e+9) · (vₙ + π) ⌋` if `n` odd,
> `v_{n+1} = ⌊ −(e+9) · (vₙ + 1) ⌋` if `n` even.
> Then `v_{2n+1} − 3·v_{2n−1}` is the `n`-th ternary digit of `e = (2.201101121…)₃`.

This is Thm 3.1 with `g=3, m=3, l=2`: `(3,2)∈𝒜₂`, `β₂=10/3`, triple `(3,2,−1)∈𝒟₂⁻`, `w=t=e`, `ε=π`.
Check: `a = klg/((g−1)(t+mg)) = (−1·2·3)/(2·(e+9)) = −3/(e+9)` ✓; `b = g/a = −(e+9)` ✓;
`l/(g−1) = 2/2 = 1` (the even-step shift) ✓.

**Lean approach:** mirror `Cor13e.lean` / `cor33_unconditional`. You'll need `e` and `π` bounds from
mathlib (`Real.exp_one_gt_d9`/`_lt_d9`, `Real.pi_gt_d6`/`_lt_d6`) to (a) pin `M = ⌊log₃ e⌋ = 0`
(`1 ≤ e < 3`), (b) discharge the floor steps. The digit-extraction bridge is the same Prop-2 machinery
(`General/Digits.lean`, `digitStep`/`gdigit`). Target name e.g. `st06_example11_ternary_e` (+ a `_literal`
form reading `Real.digits e 3 i` if convenient, like the other `_literal`s).

---

## TIER 2 — Theorem 3.1 (the `(m,l,k)` family) — the real generalization

The headline of St06. Bigger (cone bookkeeping) but elementary; same induction as `thm13`.

**Def 2.1.** `Ω = Ω₁ ∪ Ω₂`,
`Ω₁ = {(m,l)∈ℤ×(ℤ∖{0}) | m≥1, −(mg+1)/(2g−1) < l < (mg+g)/(2g−1)}`,
`Ω₂ = {(m,l)∈ℤ×(ℤ∖{0}) | m≤−2, (mg+g)/(2g−1) < l < −(mg+1)/(2g−1)}`.

**Def 2.2.** `Ω₁ = 𝒜₁∪𝒜₂∪𝒜₃`, `Ω₂ = 𝒜₄∪𝒜₅∪𝒜₆`:
`𝒜₁={(m,l)∈Ω₁|l<0}`, `𝒜₂={(m,l)∈Ω₁|0<l≤g−1}`, `𝒜₃={(m,l)∈Ω₁|l>g−1}`,
`𝒜₄={(m,l)∈Ω₂|l<0}`, `𝒜₅={(m,l)∈Ω₂|0<l≤g−1}`, `𝒜₆={(m,l)∈Ω₂|l>g−1}`.

**Def 2.3.** For `1≤i≤6`: `𝒟ᵢ = {(m,l,k) | (m,l)∈𝒜ᵢ, 0<|k|<βᵢ, k∈ℤ}` with
`β₁=−β₆=−(mg+l+1)(g−1)/(lg)`, `β₂=(mg+1)(g−1)/(lg)`, `β₃=−β₄=(mg+g−l)(g−1)/(lg)`, `β₅=−(m−1)(g−1)/l`.
`𝒟ᵢ⁺={k>0}`, `𝒟ᵢ⁻={k<0}`.

**Def 2.4.** `γᵢ±, δᵢ±`:
`γ₂⁺=δ₂⁻=γ₃⁺=δ₃⁻=γ₄⁺=δ₄⁻ = −(mg+1)/(kg)`;
`δ₂⁺=γ₂⁻=γ₁⁺=δ₁⁻=γ₆⁺=δ₆⁻ = (g−l−1)(mg+1)/(klg)`;
`δ₅⁺=γ₅⁻=δ₁⁺=γ₁⁻=δ₆⁺=γ₆⁻ = −(m+1)/k`;
`γ₅⁺=δ₅⁻=δ₃⁺=γ₃⁻=δ₄⁺=γ₄⁻ = (g−l−1)(m+1)/(kl)`.

**Theorem 3.1.** Let `w∈ℝ⁺`, `g≥2`, `t=w/g^M`, `M=⌊log_g w⌋`. Let `(m,l,k)∈𝒟ᵢ⁺` (resp. `𝒟ᵢ⁻`),
`1≤i≤6`, with `(g−1) | (k−1)l`. Define `u₁=m`,
`u_{n+1}=⌊a(uₙ+ε)⌋` (`n` odd), `u_{n+1}=⌊b(uₙ + l/(g−1))⌋` (`n` even),
with `a = klg/((g−1)(t+mg))`, `b = g/a`, and `1+γᵢ⁺ ≤ ε < 1+δᵢ⁺` (resp. `1+γᵢ⁻ ≤ ε < 1+δᵢ⁻`).
Then `u_{2n+1} − g·u_{2n−1}` is the `n`-th digit in the g-ary expansion of `w`.

**Lean approach:** the engine is **Prop 4.1** (below) — the same closed form as our `thm13`. The work is
(a) the closed-form induction `u_{2n+1}=m·gⁿ+⌊t·g^{n−1}⌋`, `u_{2n}=l(k·gⁿ−1)/(g−1)` (St06 §4.1), and
(b) showing the floor steps land, which reduces (St06 eq 4.1) to `0 ≤ l/(g−1) − a{klgⁿ/(a(g−1))} + aε < 1`
for all `1≤t<g`, closed by the `βᵢ`/`γᵢ`/`δᵢ` interval bounds (case split on the 6 subcones). Consider
proving it for **one subcone first** (e.g. `𝒟₂⁻`, which contains Example 1.1) before the full 6-way split.
**Numerically verify** a few `(m,l,k,g,w,ε)` instances per subcone first (extend the sandbox script).

**Prop 4.1 (the closed-form engine, St06 §4).** `w∈ℝ⁺`, `0<w<g`, `t=w·g^{−M}=(d₁.d₂…)_g`, `M=⌊log_g w⌋`,
`m∈ℤ`, `u₁=m`, `u_{2n+1}=g·u_{2n−1} + (0 if 1≤n≤−M, d_{n+M} if n>−M)`. Then
`u_{2n+1} = m·gⁿ + ⌊w·g^{n−1}⌋` and `u_{2(n−M)+1} − g·u_{2(n−M−1)+1} = dₙ`. (Cf. our `thm13_closed` /
`General/Thm13.lean` — likely reusable almost verbatim.)

---

## TIER 3 — binary families + Beatty unification (capstone)

**Cor 3.2** (odd base `g`, `m∉{−1,0}`, the `l=(g−1)/2, ε=½` specialization): `v₁=m`,
`v_{n+1}=⌊c_{n+1}(vₙ+½)⌋`, `c_{n+1}=(2(t+mg))⁻¹g` (`n` odd), `2(t+mg)` (`n` even). Then
`v_{2n+1}−g·v_{2n−1}` = `n`-th g-ary digit of `w`.

**Theorem 3.3** (binary `g=2`, NOT covered by Thm 3.1). `t=w/2^M=(d₁.d₂…)₂`, `m,l,k∈ℤ`, `m∉{−1,0}`,
`k≥0`, `0≤l≤m−1` (if `m≥1`) resp. `m+1≤l≤−1` (if `m≤−2`). `u₁=m`,
`u_{n+1}=⌊a(uₙ+½)⌋` (`n` odd), `⌊b(uₙ+ε)⌋` (`n` even), `a=2k+1+(t+2l)/(t+2m)`, `b=2/a`,
`½−(2l+1)/(2(2m+1)) ≤ ε < ½+(2l+1)/(2(2m+1))` (`m≥1`; symmetric for `m≤−2`). Then
`u_{2n+1}−2u_{2n−1}=dₙ` **and** `u_{2n+2}−2u_{2n}=d_{n+1}+k(2dₙ−1)`. (`w=√2,(m,l,k)=(1,0,0),ε=½` →
Graham–Pollak; digits obtained whenever `1/3≤ε<2/3`. Note: ε-bounds here are **independent of k**.)

**Theorem 3.4** (the other binary family). Same shape, `a=2k+1+2l/(t+2m)`, `b=2/a`, `1≤l≤m` (`m≥1`),
ε-bounds `½−(m−l+½)/((2k+1)(2m+1)+2l) ≤ ε < ½+(…)`  (k-dependent, unlike 3.3). Same conclusion.

**Cor 3.5 (Beatty unification — the elegant capstone).** Using Beatty's theorem
(`S(1+1/√2) ∪ S(1+√2) = ℤ∖{−1}`, `S(1+1/√2) ∩ S(1+√2) = {0}`, where `S(α)={⌊rα⌋ | r∈ℤ}`): for every
`m∈ℤ∖{−1,0}` there is a unique `r∈ℤ` with `m=⌊r(1+1/√2)⌋` or `m=⌊r(1+√2)⌋`. Set
`w = r√2 − 2⌊r/√2⌋` (first case) or `2r√2 − 2⌊r√2⌋` (second), `M=⌊log₂ w⌋`. Define `u₁=m`,
`u_{n+1}=⌊√2(uₙ+½)⌋`. Then `u_{2(n−M)+1} − 2u_{2(n−M)−1}` is the `n`-th binary digit of `w`. This
**characterizes all representable numbers** and unifies the Borwein–Bailey examples `m=1..10`
(OEIS A091524/A091525):

| m | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| w/2 | √2−1 | √2−1 | 2√2−2 | 2√2−2 | 3√2−4 | 4√2−5 | 3√2−4 | 5√2−7 | 4√2−5 | 6√2−8 |

**Lean approach for Cor 3.5:** check mathlib for **Beatty / Rayleigh** (`Nat.beattySeq`,
`compl_beattySeq`, `Beatty` namespace exist in recent mathlib — confirm what's available at v4.29.1). If
the Beatty partition is there, this is a clean capstone; if not, scope it down (drop the "all m" framing,
keep the explicit `m=1..10` instances, each a Thm-3.3/3.4 application).

---

## Suggested lap order
1. **Example 1.1** (Tier 1) — verified, self-contained, half-day. `src/Erdos482/General/St06Example.lean`.
2. **Prop 4.1** as a shared lemma (likely reuse `thm13_closed`), then **Thm 3.1 for one subcone** (`𝒟₂⁻`).
3. Full Thm 3.1 (6 subcones), then Thm 3.3/3.4, then Cor 3.5.

Numerically verify each statement first (extend `tools/sandbox/st06_*.py`). Keep everything axiom-clean
(`#print axioms` = trust base only). Refresh `STATUS.md` as targets land. **Do not push.**
