/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Goodstein's theorem — comparator CHALLENGE (the trusted audit surface)

This file is the **thing a human audits.** It imports *only* Mathlib, defines every notion used
in the headline statement, and states it with `sorry`. `Solution.lean` (which imports the real
development) must prove *this exact statement*, and `comparator` machine-checks that it did:
every declaration appearing in the statement here must be **identical** in the solution
environment, the proof must be accepted by the Lean kernel, and it may use no axioms beyond
`propext`, `Quot.sound`, `Classical.choice`.

So the trust chain is: *read this file, and only this file* — then comparator certifies the rest.

⚠️ Deliberately **no definition holes** (`definition_names`). Comparator only checks a hole's name,
type and universe, which is a gameable surface (its own README: a hole "can be gamed without
additional oversight"). Every definition below carries its real body, so it is covered by the
strict statement-identity check instead. For Goodstein the definitions *are* the whole audit: the
theorem `∃ N, G N = 0` is worthless unless `goodsteinSeq` really is Goodstein's sequence.

## Why the `LeanGallery.Logic.Goodstein` namespace

This file re-derives the gallery's constants **under their own fully-qualified names**, from scratch,
against Mathlib alone — it still imports nothing from the gallery, and everything below is written
out in full and auditable on its own terms. `Solution.lean` then imports the real development and
declares **nothing**: the names line up, and comparator's job is to check that the two sets of
declarations are *identical*.

That is not a cosmetic choice. `bump` is defined by well-founded recursion, which Lean marks
**irreducible**, so a copy under a fresh namespace would *not* be interchangeable with the gallery's
by `rfl` — the solution would have to carry a hand-written propositional bridge (`bump_eq` by strong
induction, and so on) just to connect them. That is unaudited glue sitting directly on the trust
path, buying nothing. With the real names, the certificate is about the gallery's **genuine**
`goodsteinSeq` and `goodstein_terminates`, with zero glue in the middle.

## The construction (Goodstein 1944)

For a base `b ≥ 2`, the *hereditary base-`b`* representation of `n` writes `n` in base `b`, then
rewrites every exponent in base `b`, recursively, until every number appearing (other than `b`
itself) is `< b`. Example in base `2`:
`266 = 2 ^ (2 ^ (2 + 1)) + 2 ^ (2 + 1) + 2`  (`= 2^8 + 2^3 + 2 = 256 + 8 + 2`).

`bump b n` reads `n` in hereditary base `b` and replaces every occurrence of the base `b` by
`b + 1` (exponents bumped recursively, digits unchanged). Peeling the top power — `e = Nat.log b n`,
leading digit `c = n / b ^ e` (so `1 ≤ c < b`), remainder `r = n % b ^ e` (so `r < b ^ e`) — gives
`bump b n = c * (b + 1) ^ (bump b e) + bump b r`, with `bump b 0 = 0`.

The **Goodstein sequence** seeded at `m` is `G 0 = m`, and `G (k + 1)` bumps the base
`(k + 2) ↦ (k + 3)` in `G k` and then **subtracts one** (`0` is a fixed point). So `G 0` is read in
base `2`, the first bump is `2 ↦ 3`, the next `3 ↦ 4`, and so on. `goodsteinSeq m k` is `G k`, read
in base `base k = k + 2`.

## What the headline says

For every starting value `m`, the sequence reaches `0` — despite astronomical early growth (the
`m = 4` sequence peaks near `3 * 2 ^ 402653211` before descending).

This is Goodstein's theorem proper (true; provable in ZFC, hence in Lean's stronger logic). The
*Kirby–Paris independence result* — that Peano Arithmetic cannot prove it — is a separate
metamathematical statement and is **out of scope** here.

## A note on non-vacuity 📌

Unlike a sharp *upper bound* (e.g. Erdős #403's `m ≤ 7`), this headline is a positive existential
and so cannot be vacuously true; the only way to cheat it is to write down the *wrong sequence*.
That risk is closed by inlining `bump`/`goodsteinSeq` with their real bodies above — read them.

The gallery additionally pins the definition with machine-computed ground-truth trajectories
(`goodsteinSeq 4 1 = 26`, `goodsteinSeq 4 2 = 41`, …) in `LeanGallery/Logic/Goodstein/Basic.lean`.
Those are discharged by `decide +kernel` — kernel reduction and nothing else — so they rest on
exactly this pair's whitelist (`propext`, `Classical.choice`, `Quot.sound`, all entering via
`bump`'s termination proof) and add nothing further. In particular they do **not** appeal to the
compiler the way `native_decide` would. Check them there; check the definition bodies here.

## References
* R. L. Goodstein, *On the restricted ordinal theorem*, Journal of Symbolic Logic **9** (1944),
  no. 2, 33–41. <https://doi.org/10.2307/2268019>
-/

-- `sorry` is the point of a challenge file; the repo builds with warnings-as-errors.
set_option warningAsError false

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

/-- **Goodstein's theorem (1944).** For every starting value `m`, the Goodstein sequence seeded
at `m` eventually reaches `0`. -/
theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0 := sorry

end LeanGallery.Logic.Goodstein
