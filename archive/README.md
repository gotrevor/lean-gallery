# Archive

Process artifacts, kept for the curious. Not part of the build.

## `handoff/`

Session **handoff docs** written by the AI agent(s) that built the gallery entries,
preserved verbatim. Each entry here was produced by a Claude Code agent working a
tightly-scoped spec inside a network-isolated sandbox; when a session ends it leaves a
handoff for the next one. These are those notes.

Read them if you're curious *how* an AI-driven formalization actually goes: the dead
ends, the design pivots (e.g. realizing the ε₀ order via `Relation.CutExpand` after
mathlib removed `Ordinal.nadd`), the gotchas, and what got mechanically verified.

They are **not** authoritative. The source, the `#print axioms` output, and a green
`lake build` are. If a handoff and the code ever disagree, trust the code.

- `handoff/HANDOFF.md` — completion note for the Kirby–Paris hydra entry (design decisions).
- `handoff/HANDOFF-2026-06-26-0222.md` — the timestamped session checkpoint (gotchas, key files).

Best case: you improve on the pattern, or learn something from it. Worst case: you
decide it's noise. Either's fine. 🌱
