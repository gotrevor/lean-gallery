# BUILD SPEC — Kirby–Paris Hydra termination ("Hercules always wins")

> Box build brief. Goal: add a second gallery entry — the **Kirby–Paris tree-hydra
> termination theorem** — as the ε₀ combinatorial sibling of the existing
> `Logic/Goodstein` entry. Same proof shape (ordinal descent + well-foundedness of
> `Ordinal`), same three-file layout, same axiom-clean gate.
>
> **Mirror `LeanGallery/Logic/Goodstein/` exactly.** Read those three files first;
> they are the template for structure, header, docstring style, and the audit surface.
> Do NOT invent a new house style.
> Consider *sharing* logic from there, rather than copy/pasting.

This is **termination only** — "Hercules always defeats the hydra," provable in ZFC
hence in Lean. The *independence from PA* (Kirby–Paris 1982 proper) is a separate
metamathematical result and is **OUT OF SCOPE** here (it lives in the private
`goodstein-independence` expedition). Say so in the docstrings, exactly as Goodstein's
`Statement.lean`/`Basic.lean` do for their independence result.

---

## 0. Definition of done (acceptance — the treadmill stops when ALL hold)

- [ ] `lake build LeanGallery` is **green**, **no `sorry`** anywhere reachable, **no warnings**
      (the repo runs warnings-as-errors; a warning fails the build).
- [ ] `#print axioms <headline>` is **exactly** `[propext, Classical.choice, Quot.sound]`.
      No custom axioms; no `native_decide`/`ofReduceBool` artifact on the headline's path.
- [ ] `native_decide` (if used) appears **only** on standalone anti-vacuity `example`s that
      the headline does not depend on (mirror Goodstein's anchors block + its disclaimer).
- [ ] Three files exist under `LeanGallery/Logic/Hydra/`: `Basic.lean`, `Engine.lean`,
      `Statement.lean`, each with the verbatim Apache header (Authors: Trevor Morris).
- [ ] `LeanGallery.lean` imports all three + gains a `## Results` bullet.
- [ ] `README.md` gains a Contents-table row + a "What to audit" subsection for Hydra.
- [ ] `.githooks` pre-commit gate passes (run `git config core.hooksPath .githooks` on the
      clone first; it builds on commit).

Commit when green. Do not push (host decides pushes).

---

## 1. Placement & names

| Thing | Value |
|---|---|
| Directory | `LeanGallery/Logic/Hydra/` (mirrors mathlib's `Mathlib/Logic/Hydra.lean` + the `Logic/Goodstein` sibling) |
| Namespace | `LeanGallery.Logic.Hydra` |
| Files | `Basic.lean` (abstract + audit surface), `Engine.lean` (proof), `Statement.lean` (headline) |
| Headline theorem | `hydra_terminates` (mirror `goodstein_terminates`); optional alias `hercules_wins` |
| Header | `Copyright (c) 2026 Trevor Morris. … Authors: Trevor Morris` (copy verbatim from Goodstein) |

---

## 2. The mathematics (faithful target)

### 2.1 The object — a finite rooted hydra (tree)
A hydra is a finite rooted tree; its leaves are **heads**. Encode it as a recursive tree.

- **Preferred:** `inductive Hydra | node : Multiset Hydra → Hydra` (a node = the multiset of
  its child hydras; a leaf is `node 0`). This matches mathlib's `CutExpand`/`Multiset` idiom
  and is order-free.
- **Fallback if the nested inductive through `Multiset` is rejected** by positivity / wf:
  `inductive Hydra | node : List Hydra → Hydra`. Order is irrelevant to everything below
  (the ordinal uses a *commutative* sum), so a `List` encoding is sound; just note in the
  docstring that the game is on unordered trees and order plays no role.
- Check first whether a usable rose-tree already exists to reuse; don't fight the kernel.

Decidable-eq on `Hydra` is needed for the `native_decide` anchors — derive it (`deriving
DecidableEq`, or build it; `List`/`Multiset` of a `DecidableEq` type is fine).

### 2.2 The move — chop a head, regrow (Kirby–Paris rule, turn `n`)
A head is a leaf (`node 0` / `node []`). One legal move at **turn `n`**:
1. Pick a head. It hangs off a node `p` (its parent).
2. Remove that head from `p`, giving `p'`.
3. **If `p` is the root:** the result is `p'` (no regrowth).
4. **If `p` is not the root:** let `g` be the grandparent (parent of `p`). Attach **`n`
   extra copies of `p'`** to `g` (so `g` keeps its children and gains `n` copies of `p'`).

Model this as a relation `Chop : ℕ → Hydra → Hydra → Prop` (turn `n`, before, after),
or as `play : Strategy → Hydra → ℕ → Hydra` plus a `Strategy` choosing which head. The
**headline must quantify over all strategies/choices** — "Hercules wins no matter how he
plays." The strict-decrease lemma (2.4) is what makes it strategy-independent.

⚠️ The tree-level chop/regrow bookkeeping (locate a head, find its grandparent, splice `n`
copies) is the fiddliest part of the whole build. Spend the engineering here; the ordinal
side is comparatively mechanical.

### 2.3 The ordinal assignment `o : Hydra → Ordinal`
```
o (leaf)              = 0
o (node [c₁,…,cₖ])    = ω ^ o(c₁)  ♯  …  ♯  ω ^ o(cₖ)      -- natural (Hessenberg) sum
```
- Use mathlib's **natural sum** `Ordinal.nadd` (notation `♯`) so the assignment is
  order-independent and the strict-decrease arithmetic is clean. **Verify the exact API**
  (`Ordinal.nadd`, `Ordinal.nadd_comm`, `Ordinal.nadd_lt_nadd_left/right`, monotonicity) with
  `#check`/`exact?` — names/signatures may differ at the v4.31.0 pin; don't trust this brief
  over the compiler.
- Alternative (if `nadd` API is awkward): sort children's ordinals descending and use ordinary
  `+` to build the Cantor normal form directly — this is what Goodstein's `Engine.lean` leans on
  (`Ordinal.CNF`/`coeff`/`eval`); you may be able to share lemmas. Pick whichever lands cleanly.

### 2.4 The crux lemma — every chop strictly decreases `o`
**`Chop n h h' → o h' < o h`**, for every turn `n` and every head choice. This is the
genuinely-new content (the analog of Goodstein's "bump fixes the ordinal, −1 drops it").

Mechanism (gives the box the proof skeleton):
- Removing a head leaf from its parent `p` drops one `ω^0 = 1` summand: `o p = o p' ♯ 1`,
  so `o p' < o p` and in fact `o p' + 1 = o p` (hence `o p' < o p ⟹ o p' + 1 ≤ o p`).
- **Root case:** the hydra *is* `p`, result `p'`, and `o p' < o p`. Done.
- **Grandparent case:** `g`'s contribution changes from `ω ^ o(p)` to
  `(n+1) · ω ^ o(p')` (the surviving `p'` plus `n` fresh copies). Since `o p' + 1 ≤ o p`,
  `(n+1) · ω ^ o(p') < ω ^ (o(p') + 1) ≤ ω ^ o(p)`  (finite multiple of `ω^β` is `< ω^(β+1)`).
  So `g`'s contribution strictly drops.
- **Lift to the root** via a *context-monotonicity* lemma: replacing a subtree `t` by `t'`
  with `o t' < o t` strictly decreases `o` of the whole tree (because `ω^·` is strictly
  monotone and `♯` is strictly monotone in each argument). Prove this congruence lemma once
  by structural induction; the two cases above are its instances.

Key mathlib facts to lean on (verify names): `Ordinal.opow_lt_opow_right`/strict-mono of
`ω ^ ·`; `ω ^ (β+1) = ω ^ β * ω` and `ω^β * (n:Ordinal) < ω^β * ω` for `n < ω`
(`Ordinal.mul_lt_mul_left` + `Ordinal.nat_lt_omega`/`omega0`); strict monotonicity of `nadd`.

### 2.5 The headline — termination from well-foundedness
A *battle* is a sequence `H : ℕ → Hydra` with `Chop (k+1) (H k) (H (k+1))` while `H k` is
nontrivial. By 2.4, `o ∘ H` is strictly decreasing; `Ordinal` is well-founded
(`Ordinal.wellFoundedLT` / `Ordinal.lt_wf`), so no infinite battle exists — every battle
reaches the trivial hydra (`leaf`) in finitely many steps. **Mirror Goodstein's
`Engine.lean` `goodstein_terminates_engine`**: it closes with `Ordinal.lt_wf.has_min` on
`Set.range (seqOrd …)`; do the same with `o ∘ H`.

Suggested headline (pick the cleanest faithful form):
```
theorem hydra_terminates (strat : Strategy) (h₀ : Hydra) :
    ∃ N, play strat h₀ N = Hydra.leaf
```
(quantified over `strat` = "for any way Hercules plays"). A `WellFounded`-of-the-move
corollary is a nice optional add.

---

## 3. File-by-file (mirror Goodstein)

**`Basic.lean`** — abstract + **audit surface**. Module docstring: `# Kirby–Paris hydra`,
the construction explained in prose against Kirby–Paris 1982 (tree, head, chop+regrow rule,
turn-`n` growth), `## Main definitions` (`Hydra`, `Chop`/`play`, `leaf`), `## Main statements`
(point at `hydra_terminates`), `## References`. Then the **anti-vacuity anchors** block: small
concrete `decide`/`native_decide` `example`s pinning the *move* (since `Ordinal` is not
computable, anchor the **game**, not `o`): e.g. one explicit `Chop`-step on a 2–3 node hydra,
and a tiny battle that reaches `leaf` under an explicit "leftmost head" strategy (a single head
off the root dies in one move; a length-2 path is a good second anchor). Copy Goodstein's
"these `example`s are standalone, re-check `#print axioms` not these" disclaimer.

**`Engine.lean`** — the proof machinery: `o : Hydra → Ordinal`, the context-monotonicity
lemma, the per-chop strict-decrease (2.4), and `hydra_terminates_engine` (2.5). Header note
"NOT part of the trust surface," like Goodstein's.

**`Statement.lean`** — the thin headline `hydra_terminates := hydra_terminates_engine`, with
the "designated audit surface (with `Basic.lean`)" docstring and the explicit
**out-of-scope: independence** note (copy Goodstein's `## Scope` block, swap Goodstein→Hydra).

---

## 4. Wiring & docs

- `LeanGallery.lean`: add `import LeanGallery.Logic.Hydra.{Basic,Engine,Statement}` and a
  `## Results` bullet: `- `Logic/Hydra` — Kirby–Paris hydra: Hercules always wins / every
  hydra dies (termination, ε₀).`
- `README.md`: add a Contents-table row (✅ axiom-clean) and a "What to audit" subsection
  naming `Basic.lean` (the `Hydra` datatype + the chop/regrow `Chop` move + the anchors) and
  `Statement.lean` (the headline). Note the trust surface = those two; `Engine.lean` is proof.

---

## 5. Relationship to existing work (don't reinvent, don't over-reach)

- **mathlib already has `Mathlib/Logic/Hydra.lean`** (`CutExpand`, Junyan Xu) — the *abstract
  single-level* multiset hydra, with an explicit `TODO: formalize … Kirby–Paris and Buchholz
  hydras`. This gallery entry IS that Kirby–Paris case. You may *cite* `CutExpand` as related
  prior art, but the self-contained ordinal-descent route above is the primary; do NOT try to
  reduce to `CutExpand` unless it's strictly easier (it likely isn't — `CutExpand` is flat,
  this is the nested tree).
- mathlib 1000-theorems list: the **Kirby–Paris theorem** entry (`Q1149185X`) is the
  *independence* (out of scope here); this termination entry parallels the **Goodstein's
  theorem** entry that the gallery already fills.

---

## 6. Gotchas (pre-flagged so you don't rediscover them)

- **Nested inductive via `Multiset`** may be rejected → `List Hydra` fallback (§2.1).
- **`Ordinal` is noncomputable** → no `decide`/`native_decide` on `o`; anchor the *move*
  (§3 `Basic`), not the ordinal.
- **Well-founded recursion on `Hydra`** won't kernel-reduce (`lean-wf-recursion-no-kernel-reduce`);
  keep computable anchors on the *tree/move* functions (structural), not on wf-recursive defs.
- **`native_decide` mints a per-call axiom** → it must never sit under the headline. Verify with
  a real `#print axioms hydra_terminates` (not a grep), exactly as the Goodstein gate does.
- **Verify every mathlib lemma name** at the v4.31.0 pin (`#check`/`exact?`); this brief names
  lemmas from memory and may be stale. The compiler is ground truth.
- mathlib **bans `native_decide`** in-tree, but the gallery permits it on standalone anchors
  (Goodstein does) — fine here; just keep it off the axiom path. (Relevant only if upstreaming.)

---

## 7. References
- L. Kirby, J. Paris, *Accessible independence results for Peano arithmetic*, Bull. London
  Math. Soc. **14** (1982), 285–293. (Introduces the hydra game.)
- mathlib `Mathlib/Logic/Hydra.lean` (`CutExpand`) — the abstract multiset hydra + the
  Kirby–Paris TODO this entry answers.
- Template: `LeanGallery/Logic/Goodstein/{Basic,Engine,Statement}.lean` (read first).
