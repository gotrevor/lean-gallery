# SETUP — Erdős #482 repo + mathlib scaffold (Step 1 of 2)

**Goal:** stand up a private `gotrevor/erdos-482` Lean repo, mathlib v4.29.1, cache-shared with the
other Lean repos, with a buildable skeleton + the green-build pre-commit gate — so Step 2 can point a
`lean-treadmill` at it. **Step 2 = `HANDOFF.md` (the math attack plan the box laps resume from).**

This mirrors the `~/src/erdos-403` layout exactly (same toolchain, same lakefile shape, same
`.githooks` gate). Run from a **host** shell (the box has no GitHub egress / no `cache get`).

---

## A. Create the project files

Everything is hand-created (don't `lake new`/`lake init` — this dir already holds SETUP.md +
HANDOFF.md, and hand-creating is fully deterministic).

```bash
cd ~/src/erdos-482
mkdir -p src/Erdos482 .githooks
```

**`lean-toolchain`** (one line, no newline fuss — match #403):
```
leanprover/lean4:v4.29.1
```

**`lakefile.toml`:**
```toml
name = "Erdos482"
version = "0.1.0"
keywords = ["math", "number-theory", "digits", "erdos"]
srcDir = "src"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.29.1"

[[lean_lib]]
name = "Erdos482"
```

**`src/Erdos482.lean`** (root aggregator):
```lean
import Erdos482.Basic
import Erdos482.Crux
import Erdos482.Induction
import Erdos482.Digits
import Erdos482.Main
```

**`src/Erdos482/Basic.lean`** (sequence + the digit notion + headline statement):
```lean
import Mathlib

/-!
# Erdős #482 — Graham–Pollak: the recurrence extracts the binary digits of √2

`u 0 = 1`,  `u (n+1) = ⌊√2 · (u n + 1/2)⌋`.  Then `u (2n+1) − 2·u (2n−1)` is the n-th binary
digit of √2.  Source: Stoll, *A fancy way to obtain the binary digits of 759250125√2*,
arXiv:0902.4168 (free); orig. Graham–Pollak, Math. Mag. 43 (1970) 143–145.
-/

namespace Erdos482
open Real

/-- The Graham–Pollak sequence.  (`noncomputable`: `Real.sqrt` is.) -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-- The n-th binary digit of `t` (Graham–Pollak / Stoll definition): `⌊t·2ⁿ⌋ − 2⌊t·2ⁿ⁻¹⌋ ∈ {0,1}`. -/
def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

/-- HEADLINE (Graham–Pollak).  ⚠️ First lap: confirm the exact index form against Stoll eqs (1)–(2)
before trusting this statement (faithfulness > fluency). -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  sorry

end Erdos482
```

**`src/Erdos482/Crux.lean`** (THE crux — the only genuinely-new math; do this first):
```lean
import Mathlib

namespace Erdos482
open Real

/-- The crux universal inequality (Stoll eq (7), generalized): for every real `x`,
`0 ≤ {x} − √2·{x/2} + √2/2 < 1`.  Proof: case-split on parity of `⌊x⌋` (so `{x} = 2{x/2}` or
`2{x/2} − 1`), then `nlinarith [Real.sq_sqrt, Int.fract_nonneg, Int.fract_lt_one]` with `√2² = 2`,
`1 < √2 < 3/2`.  No mathlib lemma supplies this. -/
theorem crux (x : ℝ) :
    0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 < 1 := by
  sorry

end Erdos482
```

**`src/Erdos482/Induction.lean`** (the two floor identities (5),(6) — base index `k = l+2 = 3`):
```lean
import Erdos482.Basic
import Erdos482.Crux

namespace Erdos482
open Real
-- (5)  u (2k)   = ⌊√2·2^{k-2}⌋ + 3·2^{k-3}      (for GP: α=β=1, l=1, γ=3)
-- (6)  u (2k+1) = ⌊√2·2^{k-1}⌋ + 2^k
-- Each induction step (Nat.le_induction from k=3) reduces via Int.floor_eq_iff to `crux`.
end Erdos482
```

**`src/Erdos482/Digits.lean`** (optional bridge to mathlib's canonical `Real.digits`):
```lean
import Erdos482.Basic

namespace Erdos482
-- Bridge: (Real.digits t 2 i : ℕ) = (binDigit t (i+1)).toNat   (reindex + Fin.ofNat / mod-2).
-- Skippable for a self-contained headline (Stoll's floor-formula digit def IS standard); do BOTH
-- for a publishable result.
end Erdos482
```

**`src/Erdos482/Main.lean`** (assembles the headline; thin for now):
```lean
import Erdos482.Basic
import Erdos482.Induction
import Erdos482.Digits

namespace Erdos482
-- `graham_pollak` lands here once Induction + Crux are discharged.
end Erdos482
```

**`.githooks/pre-commit`** — copy the generic green-build gate verbatim from #403:
```bash
cp ~/src/erdos-403/.githooks/pre-commit ~/src/erdos-482/.githooks/pre-commit
chmod +x ~/src/erdos-482/.githooks/pre-commit
```

**`.gitignore`** (honor the never-commit-PDFs-in-eventually-public-repos rule):
```
/.lake
/lake-packages
papers/**/*.pdf
```

**`README.md`** (one-liner is fine to start):
```markdown
# erdos-482 — Graham–Pollak binary-digits identity (Erdős #482), formalized in Lean 4 / mathlib

`u 0 = 1`, `u(n+1) = ⌊√2(u n + ½)⌋` ⟹ `u(2n+1) − 2u(2n−1)` is the n-th binary digit of √2.
Crux = one fractional-part inequality. See `HANDOFF.md` for the attack plan.
```

## B. Cache + first build (validate the skeleton)

```bash
cd ~/src/erdos-482
lake exe cache get            # pulls mathlib v4.29.1 oleans — shared cache, fast (NOT a cold 40-min build)
lake build                    # validates the skeleton
```

⚠️ **Honest expectation:** the stubs above are written-not-built — the first `lake build` may surface
a stub typo (a stray import, the `noncomputable` on `u`, the headline index form). Fix those so the
skeleton is **green with only `sorry` warnings** before you call it a baseline. Do **not** claim green
off the file contents alone — that's the [[reference_lake_build_zero_jobs]] / false-green trap.

## C. Git + private GitHub repo

```bash
cd ~/src/erdos-482
git init
git config core.hooksPath .githooks      # LOCAL config — re-run on every fresh clone / box import
git add -A
git commit --no-verify -m "scaffold: Erdos482 skeleton (sequence + crux + headline, all sorry)"
# ^ --no-verify only because the gate would build; drop it once the skeleton is green.

gh repo create gotrevor/erdos-482 --private --source=. --remote=origin   # outward-facing — Trevor runs this
git branch -M main
git push -u origin main
```

## D. Box-import readiness (so Step 2's treadmill can build it)

- The lean-yolo-box has **no network / no `cache get`** → the box relies on the host-populated shared
  mathlib olean cache. Confirm the box can build before treadmilling (`c-yolo -r erdos-482` once, manually).
- **Re-run `git config core.hooksPath .githooks` inside the box clone** (it's local config, not tracked).
- Default branch is `main`.

✅ When `lake build` is green (sorries only) and the repo is pushed, **go to `HANDOFF.md` → Step 2.**
