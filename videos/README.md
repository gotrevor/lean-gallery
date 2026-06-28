# Motivating videos 🎬

A running catalog of **popular-math videos that sent me down a formalization rabbit hole**, each
paired with where the result lives in Lean (mathlib, this gallery, in progress, or not yet done).

The loop this records: *see a cool video → ask "is this in mathlib?" → formalize the gap (or find
it already there).* The "not yet" rows double as a **wishlist** of clean, well-motivated targets.

There's precedent for citing video in mathlib itself, though it's narrow: the only YouTube links in
the library (3 of them, all in the Clausen–Scholze / condensed-mathematics corner) cite **lecture
series** that aren't yet in print. For classical results the docstring reference should still be the
paper; the video belongs *here*, as the spark.

## Legend

| Status | Meaning |
|--------|---------|
| ✅ in mathlib | the result is in Mathlib (possibly via a PR of mine) |
| 🖼️ in gallery | formalized as an entry in this repo |
| 🚧 in progress | being worked (often in a private workbench repo) |
| 🔎 wanted | no formalization yet — an open, motivated target |

## Catalog

| Video | Creator | Topic / theorem | Formalization | Status |
|-------|---------|-----------------|---------------|--------|
| *"base Fibonacci"* <!-- TODO: paste exact URL --> | *(YouTube)* | **Zeckendorf representation** — every `n` is a unique sum of non-adjacent Fibonacci numbers; the induced order on representations is lexicographic | `Mathlib/Data/Nat/Fib/Zeckendorf.lean` — base file existed; I added the **lex-order** characterization (`sum_fib_lt_iff_lex`, `zeckendorf_lt_iff`/`le_iff`, `zeckendorfOrderIso`). PR: [`gotrevor/mathlib4#2`](https://github.com/gotrevor/mathlib4/pull/2). Walkthrough: `lean-journey/walkthroughs/zeckendorf-lex-order.md` | ✅ in mathlib |

## Adding a row

1. Drop the video URL + creator in the first two columns.
2. Name the precise theorem (not just the vibe) in *Topic / theorem*.
3. Link the formalization: a mathlib path/PR, a gallery entry, a private-repo note, or leave it
   blank with status 🔎 if it's a wishlist target.
4. If a video earns a deep dive, add `videos/<slug>.md` and link it from the row.

Keep the reference rule in mind: the **paper** is the citation of record in any docstring; the video
is the motivation, and it lives here.
