/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Kirby–Paris hydra — comparator CHALLENGE (the trusted audit surface)

This file is the **thing a human audits.** It imports *only* Mathlib, defines every notion used in
the headline statement, and states it with `sorry`. `Solution.lean` (which imports the real
development) must prove *this exact statement*, and `comparator` machine-checks that it did: every
declaration appearing in the statement here must be **identical** in the solution environment, the
proof must be accepted by the Lean kernel, and it may use no axioms beyond `propext`, `Quot.sound`,
`Classical.choice`.

So the trust chain is: *read this file, and only this file* — then comparator certifies the rest.

⚠️ Deliberately **no definition holes** (`definition_names`). Comparator only checks a hole's name,
type and universe, which is a gameable surface (its own README: a hole "can be gamed without
additional oversight"). Every definition below carries its real body, so it is covered by the strict
statement-identity check instead — and that check is *transitive*: comparator walks the constant
closure of the statement, including the constructors of `Step` and `Chop`, and demands byte-identity
of each `ConstantInfo`. Nothing below is taken on faith.

## Why the `LeanGallery.Logic.Hydra` namespace

The statement closure contains **inductive types** (`Hydra`, `Chop`, `Step`). Inductives are
*generative*: a copy declared under a fresh namespace would be a genuinely different type from the
gallery's, and the solution could not discharge the challenge by delegation — it would have to carry
a transport across an isomorphism, which is extra trusted surface for zero gain.

So this file re-declares the gallery's constants **under their own names**, from scratch, against
Mathlib alone. It still imports nothing from the gallery: everything below is written out in full
and is auditable on its own terms. Comparator then compares this file's `LeanGallery.Logic.Hydra.*`
against the *real* `LeanGallery.Logic.Hydra.*` in the solution environment and fails unless they are
the same declarations. The certificate you get is therefore about the gallery's actual
`hydra_terminates` constant — not about an isomorphic stunt double.

## The problem

*Hercules always wins: no matter how the heads are chopped, every hydra dies.* — L. Kirby &
J. Paris, *Accessible independence results for Peano arithmetic*, Bull. LMS **14** (1982), 285–293.

A **hydra** is a finite rooted tree (a rose tree; `leaf = node []` is a single head, and the child
*list* is an incidental carrier — every notion below is stated up to `List.Perm`, so the game is
genuinely on unordered trees). One legal move at turn `n`: chop a head, and

* if the head hangs directly off the root, nothing regrows (`Step.root`);
* otherwise the head's parent `p` is cut down to `p'`, and `n + 1` copies of `p'` are grafted onto
  the grandparent (`Chop.grand`, reached through a child by `Chop.deep`).

`hydra_terminates` says every battle — *any* sequence of legal moves, under *any* regrowth schedule
`turn : ℕ → ℕ` — reaches the dead hydra in finitely many moves.

⚠️ **Scope: the positive theorem only.** This is hydra *termination* (true, and provable in ZFC
hence in Lean). The Kirby–Paris *independence* result — that Peano Arithmetic cannot prove it — is a
metamathematical statement about PA and is out of scope, as for the sibling Goodstein entry.

## Anti-vacuity

`Step` being *empty* would make `hydra_terminates` vacuously true (the hypothesis would force
`H k = leaf` at every `k`). The ground-truth anchors at the bottom of this file are therefore
load-bearing, and they are **proved here, not sorried**: they exhibit concrete legal moves —
including the regrowth blow-up — and show the dead hydra is terminal. Because comparator certifies
that `Hydra`, `leaf`, `Chop` and `Step` are the *same declarations* in the solution environment,
anything proved about them here holds there too.
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

-- The headline type is `LeanGallery.Logic.Hydra.Hydra`; the trailing-`Hydra` dup is intentional
-- (mirrors `Mathlib/Logic/Hydra.lean`'s placement, and the gallery's `Basic.lean`).
set_option linter.dupNamespace false

namespace LeanGallery.Logic.Hydra

/-- A **hydra**: a finite rooted tree. A node carries the list of its child hydras; a
**head** is a leaf, `leaf = node []`. The list carrier is incidental — the whole
development is invariant under permuting children (see the module doc). -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra / a single head: a node with no children. -/
def leaf : Hydra := node []

end Hydra

open Hydra

/-- **Regrowing chop at turn `n`.** `Chop n before after` holds when `after` results
from `before` by chopping a head whose parent is *not* the root, regrowing `n + 1`
copies of the cut node one level up. Two shapes:

* `grand` — the head is at depth two from this node: a child `node ps` of the root has
  a head `leaf` (so `ps ~ leaf :: ps'`); we drop that child and graft `n + 1` copies of
  `node ps'` onto the root.
* `deep` — the head is deeper still: recurse into a child `c`, which becomes `c'`. -/
inductive Chop (n : ℕ) : Hydra → Hydra → Prop
  | grand {gs gs' ps ps' : List Hydra}
      (hg : List.Perm gs (node ps :: gs')) (hp : List.Perm ps (leaf :: ps')) :
      Chop n (node gs) (node (gs' ++ List.replicate (n + 1) (node ps')))
  | deep {cs cs' : List Hydra} {c c' : Hydra}
      (hc : List.Perm cs (c :: cs')) (hrec : Chop n c c') :
      Chop n (node cs) (node (c' :: cs'))

/-- **One legal move at turn `n`.** `Step n before after`: either a regrowing `Chop`,
or the depth-one case where a head hangs directly off the root and is removed with no
regrowth (`cs ~ leaf :: rest`, result `node rest`). -/
inductive Step (n : ℕ) : Hydra → Hydra → Prop
  | root {cs rest : List Hydra} (h : List.Perm cs (leaf :: rest)) :
      Step n (node cs) (node rest)
  | chop {h h' : Hydra} (hc : Chop n h h') : Step n h h'

/-- **Kirby–Paris hydra termination ("Hercules always wins").** For every battle — any
sequence of hydras in which each step is a legal move at its turn while the hydra is
alive — the hydra is dead (`leaf`) after finitely many moves, no matter how the heads
are chosen and no matter how fast it regrows. -/
theorem hydra_terminates {H : ℕ → Hydra} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ leaf → Step (turn k) (H k) (H (k + 1))) :
    ∃ N, H N = leaf := sorry

/-! ### Ground-truth anchors (the anti-vacuity lock)

`hydra_terminates` would be *vacuously true* if `Step` were empty — the hypothesis `hstep` would
then force `H k = leaf` for every `k` and the conclusion would come for free. These anchors are what
rules that out, so they are part of the audit surface and are **proved here** (no `sorry`): explicit
term proofs straight from the `Chop` / `Step` constructors, plus the terminality of `leaf`. A
placeholder or degenerate move relation could not exhibit them.

`Ordinal` is noncomputable and the game is unordered, so we pin the *move* by exhibiting derivations
rather than by `decide` on an ordinal. -/

/-- A head hanging directly off the root dies in one move (depth-one case, no regrowth):
`node [leaf] → leaf`. -/
example (n : ℕ) : Step n (node [leaf]) leaf := Step.root (List.Perm.refl _)

/-- The **regrowth** rule, made concrete. On the length-two path `node [node [leaf]]`
the only head is at depth two, so chopping it grafts `n + 1` fresh heads onto the root:
`node [node [leaf]] → node (replicate (n+1) leaf)`. The hydra gets *bigger* before it
can die — the whole subtlety of the game. -/
example (n : ℕ) :
    Step n (node [node [leaf]]) (node (List.replicate (n + 1) leaf)) :=
  Step.chop (Chop.grand (List.Perm.refl _) (List.Perm.refl _))

/-- With two heads off the root, chopping one leaves the other: `node [leaf, leaf] →
node [leaf]`. -/
example (n : ℕ) : Step n (node [leaf, leaf]) (node [leaf]) :=
  Step.root (List.Perm.refl _)

/-- The dead hydra is **terminal**: no move is possible from `leaf`. (So "reaches
`leaf`" genuinely means the battle is over.) -/
example (n : ℕ) (h' : Hydra) : ¬ Step n leaf h' := by
  rintro hs
  cases hs with
  | root h => simpa using h.length_eq
  | chop hc => cases hc with
    | grand hg _ => simpa using hg.length_eq
    | deep hc _ => simpa using hc.length_eq

end LeanGallery.Logic.Hydra
