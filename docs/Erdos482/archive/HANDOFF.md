# HANDOFF — pointer (branch `st06`)

**You are on branch `st06`, NOT `main`.** The #482 core (Graham–Pollak + Stoll arXiv:0902.4168
Thm 3.2 / Cor 3.3 + St05 general base-`g` resolution) is **COMPLETE and axiom-clean on `main`**. This
branch is the **St06 "for fun" extension** (Stoll, *Acta Arith.* 125 (2006), 89–100) — now
**COMPLETE, axiom-clean, AND faithfulness-corrected**: Example 1.1, Thm 3.1 all 12 cones, Thm 3.3 full,
**Thm 3.4 genuine full symmetric interval** (the prior "Diophantine obstruction / only ε=½" was a
SWAPPED recurrence — corrected 2026-06-13, see newest baton), Cor 3.5 the Beatty capstone. Plus a NEW
result `SelfRefWall.lean`: the self-referential digit recurrence `⌊√g(u+c)⌋` works **iff g=2, c=½**.
**Open frontier**: cubic/higher-degree self-reference (research; `ON-LINE-REQUEST.md`).

**DIRECTION (2026-06-14 deep-reflection lap — `REFLECTION.md`): the impossibility frontier is COMPLETE
and its generalization axis is SATURATED.** The uniform general degree-`d` + base-`g` self-referential
impossibility is DONE & axiom-clean for every `d≥3`, every base `g≥2` (headline
`ae_no_dStep_schedule_reads_base_{two, g, g_all}` + capstones). **The whole repo is `sorry`-free,
custom-axiom-free, 0 math axioms — there is nothing to discharge.** Do **NOT** add further bases /
composite-degree variants (≈ 0 marginal value). The **next grind target is CONSOLIDATION**, in order:
1. a top-level **`Statement.lean`** audit surface stating/re-exporting every headline with a citation
   docstring (#482 core, St05 `erdos482_resolution`, St06 Thm 3.1/3.3/3.4/Cor 3.5,
   `ae_no_dStep_schedule_reads_base_{two,g_all}`);
2. isolate the **mathlib-absent Weyl/equidistribution/Borel-normality** layer as a clean reusable
   module + a `notes/UPSTREAM-EQUIDISTRIBUTION.md` PR-prep brief for Trevor.
The **fixed-`W`** impossibility is a famous **open problem** (Mahler's 3/2) — cite, don't grind.

This is a THIN POINTER. The durable state lives in:
- **[`REFLECTION.md`](REFLECTION.md)** — the 2026-06-14 direction call (read first).
- **[`STATUS.md`](STATUS.md)** — the living overview + axiom ledger (refreshed each review lap).
- **Newest baton** — [`HANDOFF-2026-06-14-1247.md`](HANDOFF-2026-06-14-1247.md) (reflection lap:
  impossibility axis saturated → consolidation delivered: `Statement.lean` audit surface +
  `UPSTREAM-EQUIDISTRIBUTION.md` brief + deprecation sweep; next = upstream-prep, NOT another base).
- **[`PENDING_WORK.md`](PENDING_WORK.md)** — ★★★★★ authoritative state + roadmap.

## Standing rules
- **DO NOT push** — work stays on `st06`; Trevor reviews/merges/pushes. Commit every green build.
- **verify-don't-trust** — numerically check every formula (extend `tools/sandbox/st06_*.py`) before
  formalizing. Keep everything **axiom-clean** (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`; no `sorry`, no custom axiom, no `native_decide`). Pre-commit gate runs `lake build`.
- New St06 Lean lives under `src/Erdos482/General/`.

→ Start: read `STATUS.md`, then the newest `HANDOFF-*.md`. **Lesson this lap: `#print axioms` clean ≠
statement-faithful — verify any "obstruction/not-universal" claim against the paper's recurrence.**
