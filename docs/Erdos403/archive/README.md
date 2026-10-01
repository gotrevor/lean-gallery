# #403 development archive 🗂️

Session-by-session handoff notes from the original `gotrevor/erdos-403` development, kept verbatim.

**These are a record, not documentation.** They are preserved for a reason that has nothing to do
with #403: they are a worked example of *coordinating a long proof effort across many LLM sessions* —
what a handoff has to carry, what gets lost between sessions, which plans survived contact and which
did not. Read `PLAN.md` and the dated `HANDOFF-*.md` files in order to see an approach get proposed,
ground down, abandoned, and replaced. `ARISTOTLE-RACE.md` records running the problem against
Harmonic's Aristotle in parallel with the hand development.

If you are looking for how the proof actually works, read [`../SOLVED.md`](../SOLVED.md) instead.
These notes describe intermediate states that are, by design, wrong by the end.

## ⚠️ Paths in these files refer to the old repo layout

They were written against the standalone repo, whose Lean sources lived under `src/Erdos403/`
(`Basic.lean`, `FactBase.lean`, `Sharp.lean`, `Superseded.lean`). The gallery restructured the
development into [`LeanGallery/NumberTheory/Erdos403/`](../../../LeanGallery/NumberTheory/Erdos403)
as `Basic.lean` / `Engine.lean` / `Statement.lean`, and the split is not file-for-file. So a
`src/Erdos403/…` path below will not resolve, and is best read as "somewhere in the #403 sources at
that point in the development."

Left uncorrected on purpose: rewriting the paths would make the record claim a layout that did not
exist when the note was written.
