# HANDOFF — Kirby–Paris hydra termination (COMPLETE)

**Status: DONE.** The assigned headline (`HYDRA-TERMINATION-SPEC.md`) is proven,
axiom-clean, and committed. `box done` signalled; host will honor (src/ sorry-free).

## What landed (commit `592f8aa`)
`LeanGallery/Logic/Hydra/{Basic,Engine,Statement}.lean`, wired into `LeanGallery.lean`
and `README.md`. Headline:

```
theorem hydra_terminates {H : ℕ → Hydra} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ leaf → Step (turn k) (H k) (H (k + 1))) : ∃ N, H N = leaf
```
(plus alias `hercules_wins`). Quantifies over all battles (every head choice) and all
regrowth schedules. `#print axioms hydra_terminates = [propext, Classical.choice,
Quot.sound]`. `lake build` green under warnings-as-errors + the header linter; the
pre-commit gate passed on commit.

All `HYDRA-TERMINATION-SPEC.md` §0 acceptance items hold.

## Key design decisions (why it differs from the spec's primary plan)
- **`nadd` (natural ordinal sum) was REMOVED from mathlib** (the 702-line
  `SetTheory/Ordinal/NaturalOps.lean` was deleted in mathlib #35550; absent at the
  v4.31.0 pin). The spec's primary ordinal route (`o(node) = ♯ ωᵒ⁽ᶜ⁾` via `Ordinal.nadd`)
  is therefore impossible without re-deriving ~700 lines. **Pivoted** to realizing the
  *same* ε₀ order as a **recursive multiset (path) order `HLt`** built on mathlib's
  existing `Relation.CutExpand` (`Mathlib/Logic/Hydra.lean`) — which directly answers
  that file's `TODO: formalize … Kirby–Paris … hydras`.
- **Datatype:** nested-through-`Multiset` is kernel-rejected (quotient, positivity), so
  `Hydra := node : List Hydra → Hydra` (spec's documented fallback); the game is on
  unordered trees, so children are compared up to `List.Perm` everywhere. `deriving
  DecidableEq` and plain `induction` don't fire on the nested type — a custom
  `@[induction_eliminator] Hydra.ind'` is provided; no `DecidableEq` is needed anywhere.
- **Bootstrap trick:** `HLt`'s removed child is pinned present (`a ∈ s`). This makes
  irreflexivity a plain structural induction, which then gives `Std.Irrefl HLt`,
  unblocking mathlib's `acc_of_singleton` / `Acc.cutExpand` for well-foundedness —
  breaking the usual irreflexivity↔well-foundedness circularity for recursive orders.

## Open work in this repo
None on this target. `src/` is sorry-free and green. (`HYDRA-TERMINATION-SPEC.md` is the
operator brief, left untracked.)

## Natural follow-ons (separate expeditions, NOT started)
- Kirby–Paris hydra **independence** (PA ⊬) — reuses the private goodstein-independence
  `crux-2` engine + a `Hydra ⟹ PRWO(ε₀)` bridge. Out of scope here.
- Buchholz hydra — needs a TFB ordinal-notation system mathlib lacks; much bigger.
