# Gallery documentation 📚

Per-result writeups: what the problem was, how the proof works, what the literature actually said,
and the development record. The Lean lives in [`LeanGallery/`](../LeanGallery); this is the prose
that used to live in each result's standalone development repo.

| Result | Docs |
|--------|------|
| **Erdős #403** — distinct factorials summing to a power of 2 | [`Erdos403/`](Erdos403) |

*(More results absorb here as their standalone repos are folded in.)*

## 🕳️ Findings about the literature

The most interesting output of formalizing published mathematics is not the Lean. It is what you
discover about the papers on the way — and that only surfaces because a proof assistant refuses to
accept "clearly."

Richard Buckman's framing, which is the whole thesis in one line:

> *"Software has so many bugs in it. Why would we assume that math proofs don't?"*

Findings so far:

| Finding | Result | Where |
|---|---|---|
| The original proofs are **lost by construction** — [Lin 1976] is an unpublished Bell Labs internal memorandum, [Frankl 1976] was a personal communication. Neither was written for publication and no source reproduces the argument, so the formalization is a **reconstruction**, not a transcription. It also turned out not to need the lost carry estimate. | #403 | [`Erdos403/LITERATURE-FINDINGS.md`](Erdos403/LITERATURE-FINDINGS.md) |

These are reported as findings about *published mathematics*, in the ordinary way one reports an
erratum: the mathematics is what is at issue, and nothing here is a claim about any author.

## On the `archive/` directories

Each result keeps its session-by-session development handoffs under `archive/`. They are a record
rather than documentation — preserved because they are a worked example of **coordinating a long
proof effort across many LLM sessions**: what a handoff has to carry, what gets lost between
sessions, which plans survived contact and which did not. They describe intermediate states that are
deliberately wrong by the end, and their file paths refer to the pre-gallery repo layouts. Each
`archive/README.md` says so.

## Provenance

These formalizations were produced with heavy AI assistance, disclosed per-result and in the
repository's [`formalization.yaml`](../formalization.yaml). Where an external system (e.g. Harmonic's
Aristotle) closed specific lemmas, that is recorded rather than smoothed over — **no result is
trusted on any tool's say-so.** Every headline is re-checked by the Lean kernel, gated on an exact
axiom triple by [`scripts/AxiomCheck.lean`](../scripts/AxiomCheck.lean), and verified
statement-for-statement against a Mathlib-only rendering by
[`comparator`](https://github.com/leanprover/comparator) under a second, independent kernel.
