# Erdős Problem #403 🔢

Sums of **distinct factorials** that are powers of 2. A complete, kernel-pure Lean 4 formalization
of [Erdős problem #403](https://www.erdosproblems.com/403).

**Code:** [`LeanGallery/NumberTheory/Erdos403/`](../../LeanGallery/NumberTheory/Erdos403) —
`Basic.lean`, `Engine.lean`, `Statement.lean`.

## The problem

> Write `2^m = a₁! + a₂! + ⋯ + aₖ!` as a sum of **distinct** factorials (`a₁ < a₂ < ⋯ < aₖ`).
> Erdős (attributed to Burr–Erdős [ErGr80, p.79]) asks: this has only **finitely many** solutions,
> and the largest is `2⁷ = 2! + 3! + 5!`.

## What is proven

```lean
-- Finiteness (Erdős's question, "Tier 1"):
theorem LeanGallery.NumberTheory.Erdos403.erdos_403_finite :
    {S : Finset ℕ | ∃ m, factSum S = 2 ^ m}.Finite

-- Sharp bound ("Tier 2", the "largest is 2⁷"):
theorem LeanGallery.NumberTheory.Erdos403.erdos_403_sharp :
    factSum S = 2 ^ m → m ≤ 7
```

where `factSum S = ∑ a ∈ S, a!` (a `Finset ℕ` of indices gives distinct factorials automatically;
note `0! = 1! = 1`). The witness `factSum {2,3,5} = 2⁷` is verified and `2⁷` is attained, so the
bound is sharp.

### Kernel-pure 🔒

Both headlines depend on **exactly** `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, and
no `native_decide` (no `Lean.ofReduceBool` compiler-trust axiom). `native_decide` was eliminated in a
`7 → 3 → 2 → 0` axiom pass; see [`SOLVED.md`](SOLVED.md).

This is machine-checked on every push rather than asserted here: the gallery's
[`scripts/AxiomCheck.lean`](../../scripts/AxiomCheck.lean) wraps each `#print axioms` in a
`#guard_msgs` pinning that exact triple, so drift fails the build. Statement-level checking is a
separate gate again — [`Comparator/Erdos403/`](../../Comparator/Erdos403) states the headlines
against Mathlib alone, and CI verifies the two agree under both the Lean kernel and the independent
`nanoda` kernel.

## How it works (one paragraph)

The whole problem reduces to: *for every `m ≥ 8`, `2^m` is not a sum of distinct factorials.* In the
factorial number system, "`n` is a sum of distinct factorials" ⟺ "every digit
`factDigit i n = (n / i!) % (i+1)` is `≤ 1`." The key fact is that for every `m ≥ 8`, both `2^m` and
`2^m − 1` have an FNS digit `≥ 2` at some index `≤ 11`. Because `factDigit i n` for `i ≤ 11` depends
only on `n mod 12!`, and `2^m mod 12!` is periodic in `m` with period 1620, this is a **finite check
over one period**, done by a kernel-pure `decide` over a residue fold.

## Documents

| File | Contents |
|------|----------|
| [`SOLVED.md`](SOLVED.md) | How the proof works, and the kernel-purity journey |
| [`LITERATURE-FINDINGS.md`](LITERATURE-FINDINGS.md) | 🕳️ Why the original proofs are **lost** — see below |
| [`RECONSTRUCTION.md`](RECONSTRUCTION.md) | The original 2-adic plan, superseded by the FNS proof |
| [`404-NOTES.md`](404-NOTES.md) | Investigation notes on the sibling problem [#404](https://www.erdosproblems.com/404), still **open** |
| [`archive/`](archive) | Session-by-session development handoffs, kept as a record |

## Provenance & honesty 📝

The original proofs are **lost by construction**. [Lin (1976)] is an unpublished Bell Labs internal
memorandum and [Frankl (1976)] was a personal communication; neither was written for publication, and
no source reproduces the argument. So this is a **reconstruction**, not a transcription. (Pleasingly,
that Shen Lin is the Busy-Beaver Lin–Rado / Lin–Kernighan one.) Notably, the reconstruction did **not**
need the lost carry estimate: a fixed modulus `12!` closes the power-of-two case. Full account in
[`LITERATURE-FINDINGS.md`](LITERATURE-FINDINGS.md).

This formalization was produced by Trevor Morris with Claude Code (Anthropic), following
[Mathlib's AI-usage conventions](https://leanprover-community.github.io/contribute/index.html).

---

*Originally developed in the standalone `gotrevor/erdos-403` repository, which now redirects here.
That repository's git history holds the full development record.*
