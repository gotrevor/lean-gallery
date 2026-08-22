# ON-LINE-FINDINGS — cubic / higher-degree self-referential digit recurrences (literature)

**Request answered:** `ON-LINE-REQUEST.md` 2026-06-13 — does the literature study self-referential
(coefficient = algebraic generator) floor recurrences for **cubic / higher-degree** irrationals, is
there a **β-expansion / Pisot–Salem** explanation for the cubic failure, and is there a published
**impossibility** result confirming `SelfRefWall` is the right general statement?

**Researched by:** host Ren, 2026-06-13. **Sources read:** repo digests `papers/SOURCES.md` +
`notes/ST05-GENERAL-PLAN.md` (the box's own faithful transcriptions of [St05]/[St06]); web search of
the math literature; arXiv abstracts. Web summarizers refused verbatim paper math (expected), so the
Stoll statements below come from the repo's already-verified transcriptions, not re-OCR.

**Bottom line (high confidence ~85%):** the cubic self-referential question is **genuinely outside the
existing literature** — not "folklore-closed in print," just **un-asked**. No paper builds a
coefficient-equals-generator floor recurrence for any cubic (or higher-degree) irrational, and no paper
states an impossibility theorem for it. So `SelfRefWall` is **novel**, and a cubic impossibility
theorem would be **new math**, not a re-derivation. The structural reasons below say the cubic is very
likely **closed-negative**, and they reframe the Pisot question in a way the box's note half-anticipated.

---

## 1. What the literature actually contains (and what it doesn't)

The chain of papers behind Erdős–Graham #482, in order:

| ref | what it does | self-referential? |
|---|---|---|
| **[RG]** Rabinowitz & Gilbert, *A nonlinear recurrence yielding binary digits*, Math. Mag. **64** (1991), 168–171 | first general binary extractor `uₙ₊₁=⌊a(uₙ+½)⌋`/`⌊b(uₙ+½)⌋`, `a=2(1−1/(t+2))`, `b=2/a`, ANY `w>0` | **No** — coefficients tuned to the mantissa `t` |
| **[GP]** *A fancy way to obtain the binary digits of 759250125√2*, Amer. Math. Monthly **117** (2010) (arXiv:`0902.4168`) | the `α√2` slice (Thm 3.2/Cor 3.3) — already in `src/Erdos482/Stoll.lean` | **only** in the `√2` coincidence |
| **[St05]** Stoll, *On families of nonlinear recurrences related to digits*, J. Integer Seq. **8** (2005), 05.3.2 | **the real resolution**: ANY real `w>0`, ANY integer base `g≥2`, explicit floor recurrence reads `w`'s base-`g` digits (Thms 1.1–1.3) | **No** — `a,b` are rational functions of `t`; `a=b=√g` is impossible for `g≥3` |
| **[St06]** Stoll, *On a problem of Erdős and Graham concerning digits*, Acta Arith. **125.1** (2006), 89–100 | the 3-parameter `(m,l,k)` "vast extension"; ternary digits of `e`, etc. | **No** |

**The decisive observation.** Stoll's own work *demystifies* the Graham–Pollak coincidence by showing
digit extraction is **not special to √2 at all** — it works for every `w` and every base, with tuned
coefficients. The "self-referential" property (recurrence coefficient = the algebraic generator of the
number whose digits it reads) survives in [St05] only as a **measure-zero slice**: Cor 1.1 gives
`aⱼ = j+(−1)ʲ√2`, and the Graham–Pollak `a=b=√2` is the single `j=1` point. Stoll flags `a=b=√g` as a
**coincidence available only at `g=2`**, never pursued as a phenomenon in its own right. **No Stoll
paper, and nothing in the Erdős–Graham circle, asks for a cubic coefficient-equals-generator map.**
Erdős–Graham [*Old and new problems…*, 1980, p.96] asked for "similar results for √m and other
algebraic numbers" but wrote "we have no idea what they are" — and [St05] answered *that* (tuned
coefficients), leaving the **self-referential** sub-question (coefficient = generator) untouched.

So: sub-question (1) is **answered NO** — nobody has studied higher-degree self-referential extractors.
Your `SelfRefWall` is the first statement of the phenomenon-vs-impossibility, and it is new.

**A false lead, ruled out so you don't chase it:** arXiv:`2401.04058`, Steinerberger, *Nonlinear
recursions on the reals and a problem of Graham* (2024), is a **different** Graham problem — the
`xₙ₊₁ = xₙ − 1/xₙ` map (Chamberland–Martelli: topologically conjugate to the doubling map). No digit
extraction, no bases, no Pisot. Not relevant despite the title collision.

---

## 2. The β-expansion / Pisot frame — and why "Pisot explains it" is a trap

The right frame **is** β-expansions (Rényi 1957, Parry 1960). The greedy/Rényi digit map is exactly a
floor-multiplication recurrence:
`Tβ(x) = {βx}`, `dᵣ(x) = ⌊β·Tβʳ⁻¹(x)⌋`.
The Stoll/Graham–Pollak recurrences are **integerized** versions of this: instead of carrying the real
orbit `Tβʳ(x) ∈ [0,1)`, you carry an integer `uₙ ≈ w·gⁿ`, and the floor+offset corrects the bookkeeping.

But the Pisot story **cuts against** the naive guess, exactly as your note suspected:

- **√2 is NOT Pisot.** Its conjugate `−√2` has modulus `√2 > 1`. So Pisot-ness is *not* why the
  quadratic case works.
- **2^{1/3} is NOT Pisot either.** Its conjugates `2^{1/3}ω, 2^{1/3}ω²` are complex of modulus
  `2^{1/3} ≈ 1.26 > 1`. So Pisot-ness is *not* (directly) why the cubic fails.

The actual structural dichotomy — and I think this is the load-bearing insight for deciding whether to
formalize a cubic impossibility:

> **Radical structure (`βᵈ = N ∈ ℤ`) and the Pisot property are mutually exclusive for `d ≥ 2`.**
> A `d`-step map whose `d`-fold composite is a clean base-`N` shift forces the multiplier to be a pure
> radical `β = N^{1/d}`. But `N^{1/d}`'s conjugates are `N^{1/d}·(d-th roots of unity)`, all of modulus
> `N^{1/d} > 1` — the exact opposite of Pisot (conjugates `< 1`). So you can **never** have both "clean
> integer-base shift via a radical" and "Pisot-controlled floor errors" at once.

Why `d=2` (your √2) survives anyway, and `d≥3` doesn't:

- A `d`-step composite `⌊β(…⌊β(u+c₀)…+c_{d−1})⌋` has **`d−1` *internal* floors** whose rounding errors
  must cancel simultaneously for the readout to be a clean shift.
- `d=2`: only **one** internal floor → a **single** width-1 crux inequality
  `0 ≤ {x} − √g·{x/g} + c√g < 1`. That is exactly `Erdos482.crux`, and `SelfRefWall`
  (`selfref_crux_solvable_iff`) proves it is satisfiable `∀x` **iff `g=2`** (`c=½`). The quadratic case
  is the *boundary* case that barely closes — and only at base 2.
- `d≥3`: **≥2** internal floors must cancel together, against a multiplier `N^{1/d}` whose iterate
  fractional parts `{βⁿξ}` **equidistribute** (Weyl — guaranteed precisely because `β` is non-Pisot, so
  no orbit collapse). No **fixed finite offset schedule** `(c₀,…,c_{d−1})` can hold all internal
  floor-errors inside a width-1 window for all `n`: equidistribution forces some `{βⁿξ}` into the bad
  region eventually. **This is your numeric `j=64` breakdown, explained.** It is a genuine Diophantine /
  equidistribution wall, not a search that wasn't run long enough.

This also answers the **positive-construction** sub-question (field-valued offsets in `ℚ(2^{1/3})`,
non-constant modulus):

- **Constant offsets in `ℚ(2^{1/3})` won't rescue it.** A fixed offset only translates the target
  window; equidistribution of the *orbit* is independent of the offset values, so the obstruction
  survives any constant `c_i ∈ ℝ` (rational or field-valued).
- **The only thing that "works" is the trivial thing.** If you let the offset depend on the orbit
  `Tβⁿ(x)`, you recover the full Rényi map — which extracts digits for *every* `β`, but is no longer a
  "clean self-referential recurrence," just the β-expansion itself. So the dichotomy is exactly:
  **fixed schedule (fails for `d≥3`) vs. orbit-tracking Rényi map (works but is not elegant /
  self-referential).** That dichotomy *is* the precise sense in which "elegant self-referential
  extraction is impossible beyond the quadratic case."
- A genuinely different `d=3` construction (not `⌊α(·+c)⌋`-shaped) is not ruled out by the above with
  full rigor — but it would have to evade the `βᵈ=ℤ ⟹ non-Pisot ⟹ equidistribution` chain, and I found
  nothing in the literature attempting it. Treat a positive cubic construction as **unsupported by the
  literature and structurally unlikely**, not merely "unproven."

(Pisot/Salem theory does govern when β-orbits have eventually-periodic digit strings — Schmidt's
conjecture: `ℚ∩[0,1) ⊂ Per(β)` iff `β` is Pisot or Salem. That's the relevant *named* structure, but it
predicts the cubic **failure** here, not a construction, because `2^{1/3}` is neither Pisot nor Salem.)

---

## 3. Impossibility result confirming `SelfRefWall`?

**None exists in print.** I found no published theorem of the form "self-referential digit extraction
is impossible beyond quadratic/base-2." The phenomenon is treated in the literature only as a
*coincidence* ([GP] AMM note) that Stoll then *generalized away* by retuning coefficients — so the
question "for which `(coefficient, base)` is the coefficient *forced* to equal the generator?" was never
posed, hence never answered.

Consequence for the repo:
- `SelfRefWall.selfref_crux_solvable_iff` (single-internal-floor `√g`/base-`g` extractor solvable `∀x`
  iff `g=2`) is, as far as I can determine, **a novel result.** It is the right general statement for
  the `d=2` self-referential extractor and has **no prior art** to cite — state it as new.
- It does **not** by itself settle the cubic. `SelfRefWall` kills the *single-floor* `√g`-base-`g`
  extractor for `g≥3` (e.g. "`√3` reading base 3"); the cubic `2^{1/3}` 3-step map is a **different
  object** (two internal floors, offset *schedule* not a single offset). The honest status: the cubic is
  **open in the literature**, and strongly-conjecturally **closed-negative** per the §2 equidistribution
  argument.

---

## 4. Recommendation (decides the lap you were unblocking)

**Worth a lap; aim it at a `d`-step generalization of `SelfRefWall`, NOT at a positive cubic
construction.** The literature gives no positive cubic construction to chase and the §2 structure says
one is unlikely. The tractable, citable, *new* deliverable is the impossibility direction:

- **Tier-1 (clean, `SelfRefWall`-shaped):** prove no **single fixed offset** `c` makes
  `0 ≤ {x} − α·{x/2} + cα < 1` hold `∀x` for `α=2^{1/3}` reading base 2 — i.e. confirm even the
  "one-internal-floor cubic" has no constant offset, by the same two-witness method (`x=` something and
  `x=1/2`) scaled up. Quick, fully analogous to the quadratic proof.
- **Tier-2 (the real theorem, harder):** the **3-periodic offset-schedule** impossibility — show no
  `(c₀,c₁,c₂)` keeps the 3-fold composite a clean base-2 shift for all `n`. This is where you need the
  equidistribution / two-witnesses-per-internal-floor argument (defeat all three offsets simultaneously).
  Harder, but it is the statement that actually matches your numeric `j=64` finding and would be a
  genuinely new impossibility theorem.

Either tier is **new math with no citation to defer to** — so faithfulness risk is low (no paper to
mis-transcribe), and a `native_decide`-free, axiom-clean proof would be a clean repo addition. If you
only have budget for one, do **Tier-1**: it's `SelfRefWall`-tier effort and locks in "the cubic single
floor also fails," sharpening the `d=2` boundary story.

**Do NOT** spend a lap hunting a positive cubic construction or a field-valued-offset rescue — the
literature is silent and the structure is against it. If you ever want to *publish* the `SelfRefWall`
family, frame it as: "the Graham–Pollak self-reference is the `d=2` boundary case of a radical-extractor
hierarchy that is obstructed for `d≥3` by the radical-vs-Pisot incompatibility."

---

### Sources
- T. Stoll, *On families of nonlinear recurrences related to digits*, J. Integer Seq. **8** (2005),
  Art. 05.3.2 — [JIS open access](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf).
- T. Stoll, *On a problem of Erdős and Graham concerning digits*, Acta Arith. **125.1** (2006), 89–100,
  [doi:10.4064/aa125-1-8](https://doi.org/10.4064/aa125-1-8).
- *A fancy way to obtain the binary digits of 759250125√2*, Amer. Math. Monthly **117** (2010),
  [arXiv:0902.4168](https://arxiv.org/abs/0902.4168).
- S. Rabinowitz & P. Gilbert, *A nonlinear recurrence yielding binary digits*, Math. Mag. **64** (1991),
  168–171 (see [Rabinowitz bibliography](http://stanleyrabinowitz.com/bibliography/)).
- P. Erdős & R. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, 1980, p.96.
- β-expansion / Pisot–Salem digit theory: Rényi (1957), Parry (1960); Schmidt's conjecture
  (`ℚ∩[0,1)⊂Per(β)` iff β Pisot or Salem); survey of digit exchanges for Pisot/Salem bases
  ([arXiv:1902.05349](https://arxiv.org/abs/1902.05349)).
- *Not relevant* (ruled out): S. Steinerberger, *Nonlinear recursions on the reals and a problem of
  Graham*, [arXiv:2401.04058](https://arxiv.org/abs/2401.04058) — the `x−1/x` map, different problem.
- Repo internal: `papers/SOURCES.md`, `notes/ST05-GENERAL-PLAN.md`, `notes/CUBIC-EXPLORATION.md`,
  `src/Erdos482/General/SelfRefWall.lean`.
