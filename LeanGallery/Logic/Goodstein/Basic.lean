/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Data.Nat.Log

/-!
# Goodstein's theorem

*Every Goodstein sequence terminates.* — R. L. Goodstein (1944).

This file is the **abstract and audit surface** for the formalization: it fixes the
faithful definition of a Goodstein sequence, records machine-checked sample
trajectories that pin the definition down, and points at the headline theorem. The
ordinal-descent proof lives in `Engine.lean` and the headline statement in
`Statement.lean`; neither is part of the trust surface. Read this file against
Goodstein's paper.

## The construction (standard; Goodstein 1944)

For a base `b ≥ 2`, the *hereditary base-`b`* representation of `n` writes `n` in
base `b`, then rewrites every exponent in base `b`, recursively, until every number
appearing (other than `b` itself) is `< b`. Example in base `2`:
`266 = 2 ^ (2 ^ (2 + 1)) + 2 ^ (2 + 1) + 2`  (`= 2^8 + 2^3 + 2 = 256 + 8 + 2`).

The **bump** `bump b n` reads `n` in hereditary base `b` and replaces every
occurrence of the base `b` by `b + 1` (exponents bumped recursively, digits
unchanged). Peeling the top power — `e = Nat.log b n`, leading digit `c = n / b ^ e`
(so `1 ≤ c < b`), remainder `r = n % b ^ e` (so `r < b ^ e`) — gives
`bump b n = c * (b + 1) ^ (bump b e) + bump b r`, with `bump b 0 = 0`.

The **Goodstein sequence** seeded at `m` is `G 0 = m`, and `G (k + 1)` bumps the base
`(k + 2) ↦ (k + 3)` in `G k` and then **subtracts one** (`0` is a fixed point). So
`G 0` is read in base `2`, the first bump is `2 ↦ 3`, the next `3 ↦ 4`, and so on.
`goodsteinSeq m k` is `G k`, read in base `base k = k + 2`.

## Main definitions
* `base k = k + 2` — the base used to read the `k`-th term.
* `bump b n` — the hereditary-base bump.
* `goodsteinSeq m k` — the `k`-th term of the Goodstein sequence seeded at `m`.

## Main statements
The headline lives in `Statement.lean` (proved in `Engine.lean`):
```
theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0
```
Every Goodstein sequence eventually reaches `0`, despite astronomical early growth
(the `m = 4` sequence peaks near `3 * 2 ^ 402653211` before descending). The proof
interprets each term as an ordinal `< ε₀` by reading the base as `ω`: the base-bump
leaves the ordinal fixed and the subtract-one strictly decreases it, so
well-foundedness of `<` on `Ordinal` forbids infinite descent. Verified axiom-clean:
`#print axioms goodstein_terminates` reports only
`[propext, Classical.choice, Quot.sound]`.

This is Goodstein's theorem proper (provable in ZFC, hence in Lean). The
*Kirby–Paris independence result* — that Peano Arithmetic cannot prove it — is a
separate metamathematical statement and is out of scope here.

## Sample trajectories (machine-checked below)
The `decide +kernel` examples at the end of this file compute genuine trajectories
straight from the definition, so a vacuous or placeholder definition could not
reproduce them. The seed `m = 4` is the first whose hereditary form has an exponent
equal to the base (`4 = 2 ^ 2`), exercising the *recursive exponent bump* that the
seeds `m ≤ 3` never reach:
```
m = 0:  0
m = 1:  1, 0
m = 2:  2, 2, 1, 0
m = 3:  3, 3, 3, 2, 1, 0
m = 4:  4, 26, 41, 60, …   (then grows enormously before descending to 0)
```

## References
* R. L. Goodstein, *On the restricted ordinal theorem*, Journal of Symbolic Logic
  **9** (1944), no. 2, 33–41. <https://doi.org/10.2307/2268019>
-/

namespace LeanGallery.Logic.Goodstein

/-- The base used to read `G k` at step `k` of a Goodstein sequence: `base k = k + 2`
(so `G 0` is read in base 2, the first bump sends `2 ↦ 3`, and so on). -/
def base (k : ℕ) : ℕ := k + 2

/-- **Hereditary-base bump.** `bump b n` reads `n` in hereditary base `b` and
replaces every occurrence of `b` by `b + 1`. Peeling the top power (`e = log b n`,
`c = n / b^e`, `r = n % b^e`):
`bump b n = c · (b+1)^(bump b e) + bump b r`, with `bump b 0 = 0`. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- **Goodstein sequence** seeded at `m`: `goodsteinSeq m k = G k` (see the module
doc). `G 0 = m`; `G (k+1)` bumps the hereditary base `k+2 ↦ k+3` in `G k` and
subtracts one (`0` is a fixed point, as `bump b 0 = 0` and `0 - 1 = 0`). -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => bump (base k) (goodsteinSeq m k) - 1

/-! ### Ground-truth anchors (faithfulness gate)

Hand-computed Goodstein trajectories, discharged by `decide +kernel` straight from the
definition above. They are the anti-vacuity lock on `goodsteinSeq`: a placeholder
definition could not reproduce the nonzero intermediate values.

`decide +kernel` hands the evaluation to the **kernel**, so each anchor rests on exactly
the axioms the definition already carries — `[propext, Classical.choice, Quot.sound]`,
which enter through `bump`'s well-founded-recursion termination proof — and on nothing
else. That is the *same* whitelist as `goodstein_terminates`, so the anchors need no
excuse: unlike `native_decide`, which mints a fresh opaque axiom per declaration
(`…_native.native_decide.ax_1_1`) attesting that a compiled binary printed the right
answer, there is no appeal here to the compiler, and none to "these examples sit off the
headline's axiom path."

(Plain `decide` cannot discharge them: `bump` is compiled by well-founded recursion and
so is sealed `irreducible`, which stops the elaborator's `whnf`. The kernel ignores that
seal, and its GMP-backed `Nat` literals then make the reduction cheap — the whole block
below checks in about a second.) They live in `src/` so they count toward the no-`sorry`
gate. -/

-- m = 0 : already 0
example : goodsteinSeq 0 0 = 0 := by decide +kernel

-- m = 1 : 1, 0
example : goodsteinSeq 1 0 = 1 := by decide +kernel
example : goodsteinSeq 1 1 = 0 := by decide +kernel

-- m = 2 : 2, 2, 1, 0
example : goodsteinSeq 2 0 = 2 := by decide +kernel
example : goodsteinSeq 2 1 = 2 := by decide +kernel
example : goodsteinSeq 2 2 = 1 := by decide +kernel
example : goodsteinSeq 2 3 = 0 := by decide +kernel

-- m = 3 : 3, 3, 3, 2, 1, 0  (the classic short-but-not-trivial trajectory)
example : goodsteinSeq 3 0 = 3 := by decide +kernel
example : goodsteinSeq 3 1 = 3 := by decide +kernel
example : goodsteinSeq 3 2 = 3 := by decide +kernel
example : goodsteinSeq 3 3 = 2 := by decide +kernel
example : goodsteinSeq 3 4 = 1 := by decide +kernel
example : goodsteinSeq 3 5 = 0 := by decide +kernel

-- m = 4 : 4, 26, 41, 60, …  (first seed to exercise the recursive exponent bump,
-- since 4 = 2 ^ 2; the full trajectory grows enormously before descending to 0)
example : goodsteinSeq 4 0 = 4 := by decide +kernel
example : goodsteinSeq 4 1 = 26 := by decide +kernel
example : goodsteinSeq 4 2 = 41 := by decide +kernel
example : goodsteinSeq 4 3 = 60 := by decide +kernel

end LeanGallery.Logic.Goodstein
