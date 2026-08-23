# ST05 GENERAL PLAN — formalize the real #482 resolution (any `w>0`, any base `g`)

> ## ✅✅ COMPLETE 2026-06-06 — the ENTIRE St05 paper is formalized & axiom-clean.
> Every main theorem now has a machine-checked, `[propext, Classical.choice, Quot.sound]`-only proof
> in `src/Erdos482/General/`:
> - **Thm 1.3** (g-ary, ANY base, ANY `w>0`) — `Thm13Closed.lean`: `thm13_closed` (closed forms by
>   joint induction, the piece the stalled Aristotle job couldn't crack — proved locally) +
>   `thm13_digits` (digit extraction, end to end). **This is the headline #482 resolution.**
> - **Thm 1.2 Case II** (binary, ε=½, ∞-family `j`) — `Thm12.lean`: `gv` recurrence, `thm12_caseII_eo`
>   /`_oe`/`_closed`/`_digits`.
> - **Thm 1.2 Case I** (binary, ε-INTERVAL `[1/3,2/3)`, ∞-family `j`) — `Thm12CaseI.lean`:
>   `thm12_caseI_eo`/`_oe`/`_closed`/`_digits` (oe uniform over the whole ε-interval).
> - **Thm 1.1** (Rabinowitz–Gilbert) — `Thm11.lean`: `thm11_rabinowitz_gilbert` (= Case I `j=1,ε=½`).
> - **Cor 1.1** (both √2 binary families) — `Cor11.lean`: `cor11_binary_sqrt2` (Case II slice) +
>   `cor11_binary_sqrt2_caseI` (Case I slice; `j=1`⇒Graham–Pollak).
> - **Cor 1.2** (ternary √2) — `Cor12.lean`: `cor12_ternary_sqrt2`.
> - **Prop 2** (g-ary digit extraction bridge) — `Digits.lean`: `realDigits_eq_digitStep` (general base).
>
> Numerics: `tools/sandbox/st05_thm13_verify.py` (Thm 1.3) + `st05_thm12_verify.py` (Thm 1.2 both cases,
> all `j`, ε endpoints). The milestone notes below are kept for provenance.
>
> **Open polish (optional, not blocking):** connect the capstone digit output
> `Real.digits (t·g^{n−1}/g) g 0` to mathlib's `Real.digits w g ·` of `w` itself (a mantissa-offset
> index shift `m = ⌊log_g w⌋`); fetch **St06** (Acta Arith., sharper) when IMPAN egress returns.

**Status:** scaffolded as a plan 2026-06-06, NOT started. Picks up the next time a lap chooses this track.
**Goal:** formalize Stoll [St05] (Thms 1.1–1.3) — the construction that, for ANY positive real `w` and ANY
integer base `g≥2`, gives an explicit floor-recurrence whose `u₂ₙ₊₁ − g·u₂ₙ₋₁` reads off the n-th g-ary
digit of `w`. This is the actual answer to Erdős–Graham "for √m and other algebraic numbers" — strictly
bigger than the `0902.4168` α√2 work already in `src/Erdos482/Stoll.lean`.

**Read first:** `../SOURCES.md` (verbatim theorem statements + closed forms + the ⚠️ verify-don't-trust
caution) and the ground-truth PDF `papers/St05-stoll-JIS2005.pdf` (gitignored, present in the tree). The
existing `STOLL-PAIR5-ERRATUM.md` is proof that Stoll's printed claims can be wrong — **verify every St05
closed form / interval endpoint numerically before formalizing.**

## Why this is tractable (~75%, days-to-~2-weeks, #403-tier — NOT a wall)

The proof is the SAME shape as our headline, with coefficients parametrized. Reuse map:

| St05 needs | Existing repo asset | action |
|---|---|---|
| Prop 2: `dₙ = ⌊t·gⁿ⁻¹⌋ − g⌊t·gⁿ⁻²⌋` | `Digits.lean`: `digit_bridge` / `digits_eq_floor_sub` (g=2) | generalize base 2 → g |
| closed forms `u₂ₖ`,`u₂ₖ₊₁` by joint induction | `Induction.lean`: `gp_pair` | re-template with parametrized `(a,b)` |
| each step `⌊z+c⌋=z`, `c∈[0,1)` | `Crux.lean`: `crux` / `eq8_general` | generalize off hardcoded √2 |

Two things make this potentially *easier* than the `0902.4168` pairs:
1. The closed forms hold from `k=1` (`u₁=1`) directly — **no per-pair script-generated base-case chains**.
2. No `(√m)²=m` algebra — `a,b` are explicit rational functions of the mantissa `t`; the √2 case's
   `a=b=√2` was a coincidence, not the mechanism.

**NB — do NOT import the pair-5 Diophantine scare.** `PENDING_WORK.md §1` documents that the
`0902.4168` pair-5 (α√2 over an ε-*interval*) is Diophantine-hard / possibly generational. That is
specific to *that* paper's α√2-interval parametrization. **St05's proofs close UNIFORMLY** — every
induction step bottoms out at the trivial digit-tail bound
`0 ≤ t·gᵏ − g⌊t·gᵏ⁻¹⌋ = (d_{k+1}.d_{k+2}…)_g < g` (read it in the PDF: Case II p.6, Case I p.5), with NO
distance-to-integer / badly-approximable input. So St05 should NOT inherit pair-5's wall. (Still verify
numerically — milestone 0 — the paper has been wrong before.)

## Module layout (proposed)

- `src/Erdos482/General/Digits.lean` — `gdigit g w n := ⌊w·gⁿ⌋ − g·⌊w·gⁿ⁻¹⌋`; prove `0 ≤ gdigit < g`,
  Prop 2 (`gdigit g w n = ⌊t·gⁿ⁻¹⌋ − g⌊t·gⁿ⁻²⌋`), and a reconstruction lemma. **Open Q:** does mathlib
  have a general-base real digit API? `grep`/`exact?` for `Real.digits`/`Nat.digits` first; if only base-2
  / Nat exists, `gdigit` (the Prop-2 formula) IS the faithful definition — define it, don't block on a
  mathlib API.
- `src/Erdos482/General/Mantissa.lean` — `t = w/g^m`, `m = ⌊Real.logb g w⌋`; prove `1 ≤ t < g`.
- `src/Erdos482/General/Recurrence.lean` — the parametrized two-step sequence
  `gv (a b ε δ : ℝ) : ℕ → ℤ` (odd step uses one offset, even step the other; ℤ-valued, nonneg-arg so
  `Nat.floor = Int.floor`), mirroring `vv` in `Stoll.lean`.
- `src/Erdos482/General/Thm12.lean`, `Thm13.lean` — the headline theorems + Cor 1.1/1.2.

## Milestone order (do them in THIS order — each is a green-buildable lap)

0. **Verify numerically** (script in `tools/`, like the pair base-case generators): test St05's closed
   forms + digit identities over many `n` for `w ∈ {√2,√3,π,rand}`, at the ε-interval **endpoints**, a few
   `j`/`g`. Record results in this file. If anything fails at an endpoint → erratum + scope down.
1. **`gdigit` + Prop 2** (g-ary digit extraction). Generalize `digit_bridge`. Self-contained, green.
2. **Mantissa** `1 ≤ t = w/g^m < g`. Small, green.
3. **Thm 1.2 Case II** (binary, ε=½ fixed, single family) — the proof-of-concept that the machinery
   parametrizes. Closed forms by joint induction (clone `gp_pair`), steps via generalized `crux`.
4. **Thm 1.2 Case I** (`1/3 ≤ ε < 2/3` interval — handle the open interval like the pair work did).
5. **Thm 1.3** (g-ary, any base) — the headline general result.
6. **Cor 1.1 / 1.2** (√2 binary family; √2 ternary) — specialization showcases + cross-checks against the
   existing `graham_pollak` / `Stoll.lean` results.

## Axiom hygiene

Same bar as the rest of the repo: zero `sorry`, zero custom axioms, zero `native_decide`; every theorem
ends at `[propext, Classical.choice, Quot.sound]`. Refresh `STATUS.md` with the new declarations + ledger
on each review lap.

## Relation to existing work / coordination

`src/Erdos482/Stoll.lean` (the `0902.4168` α√2 pairs) stays as-is — this is an additive new track. Keep
General/* in its own modules so it doesn't collide with any in-flight pair-6 / erratum work on `Stoll.lean`.
St06 (Acta Arith) is likely sharper but probably not required for the headline; fetch when IMPAN is back
(`DOI 10.4064/aa125-1-8`) and reconcile then.
