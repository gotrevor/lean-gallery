# How this proof got built — a process retrospective

*Erdős–Graham problem #482, formalized in Lean 4 / mathlib v4.29.1. Written at the point where the
problem is resolved end-to-end and axiom-clean (87 commits, ~36 hours of autonomous laps, 2026-06-06
→ 2026-06-07). This is a narrative of **how** the formalization progressed — the order, the dead
ends, and the methodological lessons — not a description of the final code (for that, see `STATUS.md`).*

---

## The problem in one paragraph

Erdős and Graham asked (roughly): take a number, run a simple floor-recurrence, and out come its
digits. The canonical instance is **Graham–Pollak**: `u₀ = 1`, `u(n+1) = ⌊√2·(uₙ + ½)⌋`, and then
`u(2n+1) − 2·u(2n−1)` is the *n*-th binary digit of `√2`. Stoll's 2005 paper [St05] generalizes this
to **any** real `w > 0` in **any** base `g ≥ 2`: an explicit two-parameter recurrence reads off `w`'s
base-`g` digits. That general theorem *is* the resolution of #482. A 2009 "fancy way" note (arXiv
0902.4168) is a bonus showcase: the binary digits of `759250125·√2` via eight special parameter pairs.

---

## The arc

The work moved through five phases, each building infrastructure the next reused.

**Phase 1 — the headline (√2).** Scaffold the sequence, prove `graham_pollak` by an elementary
induction on the concrete `u`, then bridge Stoll's floor-formula digit (`binDigit`) to mathlib's
`Real.digits`. The first real lesson landed immediately as a *refactor*: the digit-bridge wanted to be
stated for **any** `y ≥ 0` (`digits_eq_floor_sub`), with √2 a corollary. **Generalizing the lemma the
moment a second use-case is visible** paid back many times over — that bridge became `Prop 2` of the
general track verbatim.

**Phase 2 — the bonus (759250125√2).** Stoll's Theorem 3.2 + Corollary 3.3. Eight parameter pairs,
each an interval of admissible offsets `ε`. Seven pairs fell to a shared α√2-only invariant plus an
"interior-ε" trick; the title result `cor33_unconditional` (digits of `759250125√2`) came out
axiom-clean. This phase taught **state the result in the paper's own notation** (the verbatim `tᵢ`-form
restatements) so a reader can diff Lean against the PDF line by line.

**Phase 3 — the pair-5 saga (the instructive failure).** Pair 5 (`t₅ = √2`, `β = 0`) resisted. The
turning point: **the printed closed form in the paper was wrong.** Numerics (always run *before*
formalizing) showed interior offsets in Stoll's stated pair-5 interval diverge from √2's digits at
n=452, then again the margin shrinks to 1.4e-6 at n=1811 — i.e. the obstruction is genuinely
*Diophantine*, not a finite check. We did **not** formalize the false claim. Instead we formalized the
honest content: the typo-corrected formula, an exact *band characterization* of the ε-step, the
*conditional* full-interval theorem, and the *precise two-sided obstruction* proving no `ε ≠ ½` is
uniformly admissible. A `vv ε = u` reformulation looked promising and was pursued — then killed by
numerics as a dead end. **The errata (`STOLL-PAIR5-ERRATUM.md`) is a deliverable, not an
embarrassment.**

**Phase 4 — the general resolution (St05).** This is the real #482. The spine is a closed-form **joint
induction**: at even indices the value is `2^k + ⌊t·2^k/2⌋`, and two single-step floor identities
(`step_eo` even→odd, the crux; `step_oe` odd→even, exact) chain into the digit extraction for any
mantissa `1 ≤ t < g`. The decisive methodological moment: the previous lap **handed the whole
induction to Aristotle** (Harmonic's auto-formalizer) and it **stalled at 9%**. Decomposing the
all-in-one obligation into per-step floor lemmas cracked it **locally** in one lap. **Lesson:
decompose before delegating — a solver chokes on a monolithic induction but handles bounded floor
identities.** Theorem 1.2 split into two cases (Case II a point, Case I a whole ε-interval); Theorem
1.1 (Rabinowitz–Gilbert) is `j=1, ε=½` of Case I; Cor 1.1/1.2 instantiate at √2.

**Phase 5 — packaging, closure, and showcases.** `erdos482_resolution` packages "any `w>0`, any `g≥2`"
into one statement. The sharper companion paper [St06] turned out to be **genuinely unobtainable** (its
only free host is a broken SPA; not on arXiv or shadow libraries) — but the online-research lap
established it is **not on the critical path**: St05 *is* the resolution; St06 only adds sharper
restatements + showcase constants. The remaining work was then honest polish:
- `cor13` — base-3 digits of `e` (the transcendental-in-an-odd-base constant St06 is OEIS-tagged to),
  as a direct instantiation of *our own* Theorem 1.3.
- `gv_sqrt2_eq_u` — proving the general recurrence at `j=1` *is literally* the original `u`, so the
  general theorem re-derives √2 with a **machinery-disjoint** proof tree.
- `erdos482_resolution_general_literal` — closing the deliberately-left mantissa index-shift, so the
  headline reads off **any `w ≥ 1`'s genuine `Real.digits w g`**, not just the mantissa's.

---

## What worked (the transferable methodology)

1. **Verify numerically before formalizing — every closed form, every time.** A throwaway Python
   oracle (`tools/sandbox/*.py`) caught a *published* error (pair 5) and one of my own (the `e`-base-3
   docstring expansion). In a formalization, the kernel guarantees you proved *what you stated* — it
   cannot tell you the *statement* is the wrong theorem. Numerics guard the statement.

2. **Generalize the lemma the moment a second instance appears.** The base-2 digit bridge → any-base
   `Prop 2`; the √2 non-termination → any-irrational. Specializing back (√2 from the general theorem)
   is then a one-liner; the reverse is not.

3. **Decompose monolithic inductions into per-step identities before reaching for any solver.** The
   joint induction Aristotle couldn't touch became tractable once split into `step_eo` / `step_oe`.

4. **Treat the auto-formalizer as insurance, not the critical path.** Every Aristotle result was
   kernel-verified + `#print axioms`-checked before being trusted, and local work beat it to the
   punch every time it mattered. It earned its keep on bounded, self-contained Diophantine lemmas
   (`sqrt2_badly_approximable`, `vv_one_le_and_mono`), not on the headline inductions.

5. **Axiom hygiene as a continuous gate.** Every declaration's `#print axioms` is the trust base only
   (`propext, Classical.choice, Quot.sound`) — zero custom axioms, zero `sorry`, repo-wide. A
   pre-commit hook re-runs `lake build`, so "green" is never claimed unseen.

6. **Honest negative results are first-class.** The pair-5 errata, the conditional theorem, the precise
   obstruction, and the "St06 is unobtainable but off the critical path" finding are all committed
   artifacts. Not proving a false claim is a result.

---

## The instructive failures

- **A published closed form was wrong** (the "fancy way" note, arXiv:0902.4168, pair 5). Caught by
  numerics; never formalized.
- **A promising reformulation was a dead end** (`vv ε = u` for interior ε). Caught by numerics at
  n=452; recorded, not buried.
- **The auto-formalizer stalled on a monolithic goal** (9% on the joint induction). Fixed by
  decomposition, not by waiting.
- **My own illustrative expansion was wrong** (`e` in base 3, first draft). Caught by re-deriving it
  from the high-precision value before committing.

The common thread: **every one was caught by an independent check** — numerics, the kernel, or a
re-derivation — rather than by trusting a plausible-looking artifact.

---

## A closing reflection: did proving √2 first help prove the general case?

Less than you'd hope, and instructively so. The √2 work gave **infrastructure** (the digit bridge
generalized cleanly) and **discipline** (verify-first). But `a = b = √2` is **symmetric**, so the
original proof never confronts the even→odd vs odd→even asymmetry (`step_eo` vs `step_oe`) that is the
entire spine of the general proof. The √2 case *hid* the main difficulty. The general closed-form
induction had to be invented fresh — and once it existed, it re-proved √2 in ~30 lines, while having
√2 in hand had not materially shortened it. A nice coda fell out of the bridge: the original
(`graham_pollak`) reads the **odd-index** differences = the *fractional* digits `0,1,1,0,1,0,…`, while
the general route at `j=1` reads the **even-index** differences = the *full* expansion
`√2 = 1.0110101…₂`, leading `1` included — two genuinely independent proofs reading complementary
digit streams of the very same sequence.

---

*Pointers: `STATUS.md` (living overview + axiom ledger) · `STOLL-PAIR5-ERRATUM.md` (the published-error
finding) · `archive/findings/` (consumed online-research docs) · `src/Erdos482/` (original √2 + bonus)
· `src/Erdos482/General/` (the St05 general resolution).*
