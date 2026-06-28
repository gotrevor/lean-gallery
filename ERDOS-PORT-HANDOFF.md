# Handoff: port the remaining 3 Erdős formalizations into lean-gallery

**For: a fresh `c-yolo lean-gallery` box (no permission prompts).**
**Author: Ren 🪷 (host session, 2026-06-28).**

## Goal

Port the **3 remaining** solved-and-axiom-clean Erdős formalizations from their source repos in
`~/src` into this public showcase, matching the pattern already used for **#403** and **#1213**.

When you are done: **5 Erdős entries** in the gallery, every headline axiom-clean
(`[propext, Classical.choice, Quot.sound]`), `lake build` green under warnings-as-errors, each
committed. **Do not push** (you are network-isolated); the host will push + watch CI.

## Already done — study these two as your reference

- **#403** → `LeanGallery/NumberTheory/Erdos403/{Basic,Engine,Statement}.lean` (committed `475334d`,
  CI green). This one was hand-restructured into the strict Basic/Engine/Statement idiom (it had only
  3 source files).
- **#1213** → `LeanGallery/Combinatorics/Erdos1213/` (committed `a1b7673`). This one was **re-homed
  with the script below** (kept its multi-file structure). **This is the pattern you will follow for
  all 3.** Read its files + the commit diff to see exactly what the end state looks like.

## What "port" means (the recipe)

Each source repo's **clean `src/<Lib>/` tree** is the whole deliverable. (The `tools/aristotle/` and
top-level `aristotle/` dirs are scaffolding **outside `src/`** — they hold `sorry`-stubbed Problem.lean
files; **never copy those.**) For each repo:

1. **Re-home** `src/<Lib>/` (and `src/<Lib>.lean`) into `LeanGallery/<Area>/<Lib>/`.
2. **Rename** the namespace + imports: `Erdos<N>` → `LeanGallery.<Area>.Erdos<N>` (word-boundary; the
   lowercase decl names like `erdos_403` are untouched).
3. **Prepend** the Apache copyright header to every file; ensure each file has a module docstring
   (the header linter requires both). The script does all of 1–3.
4. **Wire** into `LeanGallery.lean` (one `import LeanGallery.<Area>.<Lib>` for the umbrella + a Results
   bullet).
5. **Build green** — `lake build LeanGallery.<Area>.<Lib>` — and fix every warning (this repo sets
   `warningAsError = true`; the source repos did not, so they carry latent warnings). See **Warning
   playbook**.
6. **Exclusions** (only #1050 and #880): remove the axiom-backed bonus file(s) and prune their
   references, so the **whole** lib is axiom-clean. (#482 has no exclusions.) See **Per-repo**.
7. **Verify axiom-clean**: for every headline, `#print axioms` must be exactly
   `[propext, Classical.choice, Quot.sound]`.
8. **CI gate + README**: add each headline to `.github/workflows/ci.yml` and add the README rows.
9. **Commit** (the pre-commit hook re-runs `lake build` as the green gate). Do **not** push.

## The port script

Run this once per repo (`bash /tmp/port.sh <repo> <Area> <Lib>`):

```bash
cat > /tmp/port.sh <<'SCRIPT'
#!/usr/bin/env bash
set -euo pipefail
REPO="$1"; AREA="$2"; LIB="$3"          # e.g.  erdos-1050 NumberTheory Erdos1050
SRCROOT="$HOME/src/$REPO/src"
GALROOT="$HOME/src/lean-gallery/LeanGallery/$AREA"
NS="LeanGallery.$AREA.$LIB"
HDR="$(mktemp)"
cat > "$HDR" <<'EOF'
/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
EOF
mkdir -p "$GALROOT"
cp -R "$SRCROOT/$LIB" "$GALROOT/$LIB"
cp "$SRCROOT/$LIB.lean" "$GALROOT/$LIB.lean"
# rename namespace + imports + qualified refs (\bLib\b -> NS; lowercase decls unaffected)
find "$GALROOT/$LIB" "$GALROOT/$LIB.lean" -name '*.lean' -print0 \
  | xargs -0 perl -0777 -pi -e "s/\\b\\Q$LIB\\E\\b/$NS/g"
# prepend Apache header where missing; ensure each file has a module docstring
while IFS= read -r -d '' f; do
  head -1 "$f" | grep -q '^/-' || { cat "$HDR" "$f" > "$f.tmp" && mv "$f.tmp" "$f"; }
  grep -q '/-!' "$f" || printf '\n/-! # `%s` (umbrella import) -/\n' "$NS" >> "$f"
done < <(find "$GALROOT/$LIB" "$GALROOT/$LIB.lean" -name '*.lean' -print0)
echo "ported $LIB -> $NS : $(find "$GALROOT/$LIB" -name '*.lean' | wc -l | tr -d ' ') leaf files + umbrella"
SCRIPT
```

## Warning playbook (gallery = warnings-as-errors)

These are the exact recurring warnings (all hit during the #1213 port). Fix in the **gallery copy**,
not the source repo:

- **`push_neg` deprecated → use `push Not`** (same syntax, e.g. `push Not at h`). Grep the whole
  ported tree for `push_neg` and fix all up front: `grep -rn 'push_neg' <tree>` then
  `perl -pi -e 's/\bpush_neg\b/push Not/g' <files>`.
- **`'<tac>' tactic does nothing`** (e.g. `push_cast`, `simp`, `norm_num`) — delete that tactic line;
  the next tactic still closes the goal. (Only the *no-op* occurrences are flagged — leave the ones
  that do work.)
- **`this tactic is never executed`** — a dead alternative, e.g. `all_goals first | omega | exact h`
  where `omega` always wins → simplify to `all_goals omega`.
- **`Variable name 'x' is not explicitly referenced`** — prefix the binder with `_` (e.g. `_hmono`).
  **Don't delete the hypothesis** (keeps the theorem's arity/API for callers).
- **`import Mathlib` is fine** — the header linter's broad-import check only forbids `Mathlib.Tactic`,
  `Lean`, `Lean.Elab`, `Std`, `Lake*`. Leave `import Mathlib` as the source has it.
- **Header linter** needs the Apache block + a module docstring (`/-! … -/`) after the imports on
  *every* file. The script handles both; if it ever complains about a specific file, add a one-line
  `/-! # … -/`.
- `lake build` reports **all** errors in the first failing file at once — fix them in one pass, rebuild,
  move to the next file.

## Verify axiom-clean (the real gate)

For each headline:

```bash
cd ~/src/lean-gallery
cat > axchk.lean <<'EOF'
import LeanGallery.<Area>.<Lib>
#print axioms LeanGallery.<Area>.<Lib>.<headline>
EOF
lake env lean axchk.lean    # must print: depends on axioms: [propext, Classical.choice, Quot.sound]
trash axchk.lean            # (or rm; host uses trash)
```

Anything other than the standard triple (a `sorryAx`, or a named `axiom`) means that headline is
**not** gallery-clean → exclude it (and its now-orphaned support files) per the per-repo notes.

## Per-repo specifics

### #1050 → `NumberTheory/Erdos1050`  (AMS 11)
- `bash /tmp/port.sh erdos-1050 NumberTheory Erdos1050`
- **Headline:** `erdos_1050_irrational` — `∑ 1/(2ⁿ−3)` is irrational (Borwein 1991/92).
- **⚠️ EXCLUDE the axiom-backed bonus:** `GeneralThm2.lean` declares
  `axiom borwein_approximants_alt` → Borwein **Theorem 2** is not axiom-clean. `trash` that file from
  the port, remove its `import …GeneralThm2` from the umbrella `Erdos1050.lean`, and drop any
  reference to it (likely in `GeneralAssembly.lean` / a Statement re-export). Then `#print axioms`
  every remaining headline and drop anything *still* showing `borwein_approximants_alt`. Borwein
  **Theorem 1** (`General.lean`) is expected to be clean — keep it if it verifies clean.
- **CI gate:** `erdos_1050_irrational` (+ a clean General-Thm-1 headline if you keep one).

### #482 → `NumberTheory/Erdos482`  (AMS 11)
- `bash /tmp/port.sh erdos-482 NumberTheory Erdos482`
- **No axiom declarations** → port the **full** lib clean (~56 files; biggest port — expect the most
  warnings, sweep `push_neg` first).
- **Headlines** live in `Erdos482.Statement` as `alias`es. Primary ones for the CI gate:
  `LeanGallery.NumberTheory.Erdos482.graham_pollak` (the Graham–Pollak / √2-digits headline) and
  `LeanGallery.NumberTheory.Erdos482.cor33_unconditional` (the `759250125·√2` showcase constant). The
  Statement file also exposes `statement_*` aliases, `erdos482_resolution`, the St06 family, and the
  impossibility-frontier theorems — all axiom-clean per the repo.

### #880 → `Combinatorics/Erdos880`  (AMS 05)
- `bash /tmp/port.sh erdos-880 Combinatorics Erdos880`
- **⚠️ EXCLUDE the Kneser / Theorem-10 subtree** (not axiom-clean): `Thm10.lean` declares
  `axiom kneser_density_residue`. `trash Thm10.lean`; then prune its references:
  - from the umbrella `Erdos880.lean`: the `import …Thm10` line;
  - from `Statement.lean`: the entire **"Theorem 10"** section (`erdos_880_thm10'`,
    `erdos_880_thm10_sandwich'`, and the `Conjecture2` paragraph);
  - from `AxiomGuard.lean`: the `#guard_msgs in #print axioms` entries for the Thm10 / Kneser names
    (`thm10_kneser_descent`, `kneser_*`, `kFun…`, `k1Fun`, etc. — keep all the clean ones).
  - `DensityKneser.lean` / `Kneser.lean`: keep only if they still build clean and something clean
    still imports them; otherwise `trash` them too. Let the build tell you (unused files just sit
    un-imported once the umbrella drops them — simplest is to `trash` any file only Thm10 used).
- **`AxiomGuard.lean` is gold — keep it.** It does `#guard_msgs in #print axioms` for ~50 theorems at
  build time, i.e. it's an in-library axiom gate. Once you've removed the Thm10/Kneser entries, it
  green-gates the rest for free.
- **Clean headlines to keep** (all `[propext, Classical.choice, Quot.sound]`): `erdos_880`,
  `erdos_880_order_two`, `erdos_880_exact_order`, `erdos_880_thm3_kh`, `erdos_880_thm4_fh`,
  `erdos_880_thm4_exact`, `erdos_880_delta`, `erdos_880_order_two_delta`, `erdos_880_prop7`,
  `erdos_880_prop5`, `erdos_880_thm9_step`, `erdos_880_thm8'`, `erdos_880_thm9'`,
  `Delta_restrictedSums_anti`, `Delta_restrictedSums_lt_top_of_le`, `erdos_880_thm3_delta`,
  `erdos_880_thm4_delta_transition`.
- **CI gate:** `erdos_880` (+ `erdos_880_order_two`).

## Wiring details (copy the #403/#1213 pattern exactly)

**`LeanGallery.lean`** — under the existing imports add one umbrella import per repo, and a Results
bullet for each. (For #403 the three files are imported individually; for the re-homed repos import the
single umbrella `LeanGallery.<Area>.<Lib>`.)

**`.github/workflows/ci.yml`** — the "Axiom-clean gate" step has one `printf '…' > axcheck.lean` line.
Append, into that same printf string, an `import …Statement\n` for each repo and a
`#print axioms …<headline>\n` for each headline you want gated. The gate asserts every printed theorem
is the standard triple, so only list axiom-clean headlines. (See the current value for #403/#1213.)

**`README.md`** — add (a) a row to the **Contents** table, (b) an entry in the **What to audit** section
pointing at the repo's `Statement.lean` (+ the few `Basic.lean` defs), and (c) a **References** line.
Mirror the #1213 entries.

## When all 3 build green + are committed (host will do this part)

1. Push `main`, `gh run watch` the CI run to green.
2. Open **formal-conjectures** PRs for all 5 (#403, #482, #1213, #1050, #880). The Google CLA was
   **signed 2026-06-28**, so the gate is clear. None of the 5 exist in
   `FormalConjectures/ErdosProblems/<N>.lean` yet. Convention: faithful statement + `:= by sorry` +
   `@[category research solved, AMS <code>, formal_proof using lean4 at "<gallery commit URL>"]`.
   On merge, erdosproblems.com auto-flips each `formalized: yes` (no separate erdosproblems PR needed).
3. Delete this handoff file (`ERDOS-PORT-HANDOFF.md`) once the ports are merged.

## Rules
- **Commit, don't push** (network-isolated). The pre-commit hook (`lake build`) is your green gate;
  a successful commit means the build is clean.
- Fix things in the **gallery copy**, never in the source repos (those are the private workbench).
- One commit per repo is fine (e.g. "Add Erdős #1050: …"); match the #403/#1213 messages.
