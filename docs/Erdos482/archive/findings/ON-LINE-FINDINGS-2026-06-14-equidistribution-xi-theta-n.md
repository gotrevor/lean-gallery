# ON-LINE-FINDINGS — is `{ξ·θⁿ}` equidistribution (fixed algebraic `θ`, fixed `ξ`) open?

**Request answered:** `ON-LINE-REQUEST.md` 2026-06-14 — the cubic Tier-2 frontier. Is equidistribution of
`{ξ·θⁿ} mod 1` for a **fixed** base `θ>1` and **fixed** `ξ≠0` a theorem or open? Is the prior findings
doc's "non-Pisot ⟹ `{αⁿξ}` equidistributes for our `ξ`" valid? Does mathlib have the a.e.-`ξ`
geometric Weyl/Koksma result?

**Researched by:** host Ren, 2026-06-14. **Sources:** web literature search (Koksma 1935 + the
`{(3/2)ⁿ}` open-problem corpus + Aistleitner–Hofer–Larcher geometric-progression papers); direct grep of
the **in-repo mathlib checkout** (`.lake/packages/mathlib`) for the declaration-name question. Math
facts below are classical metric-number-theory; verified against multiple independent sources, not OCR.

**Bottom line (high confidence ~90%):** your understanding is **correct on all three counts**, and the
prior findings doc's §2 phrasing **is an over-claim** — which you already caught and fixed in
`PENDING_WORK.md` (the ★ FRONTIER caveat). This doc supplies the citations to lock that in.

1. **a.e.-`ξ` equidistribution = THEOREM** (Koksma 1935). **fixed-`ξ` = OPEN** in general.
2. **"non-Pisot ⟹ equidistributes for our `ξ`" = FALSE as stated** — it conflates the a.e.-`ξ` theorem
   with the fixed-`ξ` question, AND "non-Pisot" is *necessary, not sufficient*.
3. **mathlib does NOT have the geometric a.e.-`ξ` `{ξθⁿ}` result.** It has only integer-`×n`
   endomorphism ergodicity and irrational-rotation ergodicity — neither covers `θ = 2^{1/3}`.

**⟹ Formalize the CONDITIONAL cubic impossibility (attack path #1).** The unconditional version for your
*specific* `W` is **open in current mathematics**, not "deep machinery we haven't built." STATUS/notes
should say exactly that.

---

## 1. a.e.-`ξ` is a theorem; fixed-`ξ` is open

### 1a. The almost-all theorem — Koksma 1935 (this is the citation your PENDING_WORK caveat was missing)

> **Koksma (1935).** For every **fixed** real `θ > 1`, the sequence `({ξ·θⁿ})_{n≥1}` is uniformly
> distributed mod 1 for **Lebesgue-almost-every** real `ξ`.

This is the *symmetric form* of Koksma's metric theorem. The same paper's better-known special case is
"for a.e. `θ > 1`, `({θⁿ})` is u.d. mod 1" (i.e. `ξ = 1`, base varies); the form you need is the dual
(base fixed, `ξ` varies). Both are the same theorem.

- **Primary reference:** J. F. Koksma, *Ein mengentheoretischer Satz über die Gleichverteilung modulo
  Eins*, **Compositio Mathematica 2 (1935), 250–258.**
- **Lineage:** the integer-exponent ancestor is H. Weyl, *Über die Gleichverteilung von Zahlen mod.
  Eins*, Math. Ann. **77** (1916), 313–352 (for a sequence of **distinct integers** `(aₙ)`, `({aₙ x})`
  is u.d. mod 1 for a.e. `x`). Koksma's contribution is the version for `xⁿ`/`θⁿ`-type growth where the
  exponents need not be integer multipliers of a fixed `x`.
- **Textbook:** Kuipers & Niederreiter, *Uniform Distribution of Sequences* (Wiley 1974), Ch. 1 §4
  ("Some Important Examples") — the metric theorems for `(aₙx)` and `(θⁿx)`. ⚠️ I could not open K&N to
  confirm the **exact theorem number** (it's in the Thm 4.1–4.3 cluster); cite as "K&N Ch. 1 §4" unless
  you can verify the number. The Koksma + Weyl primary refs above are solid and sufficient on their own.
- **Modern restatement (good to cite, freely available):** the symmetric statement —
  "for any fixed `α ≠ 0`, for a.e. `ζ > 1`, `{αζⁿ}` is u.d. mod 1; and for any fixed `ζ > 1`, for a.e.
  `α`, `{αζⁿ}` is u.d. mod 1" — appears verbatim in the geometric-progression literature, e.g.
  C. Aistleitner, M. Hofer, G. Larcher, *Quantitative uniform distribution results for geometric
  progressions* (arXiv:1210.4215 / Israel J. Math. 2014) and the survey arXiv:2109.00562
  (*Equidistribution Mod 1 and Normal Numbers*).

### 1b. The fixed-`ξ` case is OPEN — the `{(3/2)ⁿ}` wall

For a **specific** `θ` and **specific** `ξ`, equidistribution of `{ξθⁿ}` is **not** decidable by current
methods in general. The canonical witness:

> **`{(3/2)ⁿ} mod 1`** is conjectured equidistributed but is **not even known to be dense** in `[0,1)`.
> (Tied to Mahler's `3/2`-problem / Z-numbers, and to Waring's problem.)

Note `3/2` is **non-Pisot** (not even an algebraic integer), yet equidistribution — indeed density — is
open. This single example is the clean refutation of "non-Pisot ⟹ equidistributes for a fixed `ξ`"
(see §2). The exceptional `ξ` where it provably *fails* are governed by Pisot/Salem structure (Pisot
`θ` ⟹ `{θⁿ} → 0`, never u.d.), but the *generic specific* `ξ` is simply unresolved. The null
exceptional set from §1a is uncountable and contains the structured `ξ` we have no control over.

- Sources: arXiv:2109.00562 (`{(3/2)ⁿ}` u.d. "still an unsolved problem… never even proven dense");
  arXiv:1501.07176 (*Integral powers of numbers in small intervals mod 1*); the Salem-number
  equidistribution literature.

**Your orbit's `ξ` is the worst case.** The relevant `ξ = W = lim u(3j)/2^j` is *defined by the orbit
itself* — we have no independent Diophantine handle on it, so we cannot place it in either the "good"
(a.e.) set or a known exceptional set. Equidistribution of `{W·αⁿ}` for *this* `W` is therefore open.

---

## 2. The prior doc's "non-Pisot ⟹ equidistributes for our `ξ`" is an over-claim

The prior findings doc (`archive/findings/…cubic-selfref-literature.md`, §2, line ~88) wrote that
`{αⁿξ}` "equidistributes (Weyl — guaranteed precisely because β is non-Pisot)." **Two distinct errors:**

1. **Dropped quantifier.** Weyl/Koksma guarantee equidistribution for **almost-every** `ξ`, *not* for a
   named `ξ`. Applying the a.e. theorem to "our `ξ`" (a single, structurally-special point) is exactly
   the conflation you suspected. The a.e. theorem says **nothing** about any individual `ξ`.
2. **Non-Pisot is necessary, not sufficient.** Non-Pisot-ness of `α` rules out the trivial `{αⁿ}→0`
   collapse, so it is *necessary* for `{αⁿ}` to equidistribute — but it is **nowhere near sufficient**
   for a fixed `ξ`. `{(3/2)ⁿ}` (§1b) is non-Pisot with equidistribution open. So "non-Pisot ⟹
   equidistributes for our `ξ`" has a standing open counterexample-class; it is not a valid implication.

Your `PENDING_WORK.md` ★-FRONTIER caveat (lines 18–23) already states this correctly. **Confirmed —
keep that caveat; this doc is its citation.** The `2^{1/3}` ⟹ non-Pisot fact is true and worth keeping
(its conjugates have modulus `2^{1/3} > 1`), but it only *fails to obstruct* equidistribution; it does
**not** *establish* it.

(One nuance, for completeness: the literature *does* have clean iff-statements, but for **lacunary
subseries / finite sums** `x·∑ θ^{nⱼ}`, not the full orbit — e.g. "`x∑θ^{nⱼ}` is u.d. iff (`θ` non-Pisot
& `x≠0`) or (`θ` Pisot & `x∉ℚ(θ)`)". Do **not** mis-cite that as a statement about the single orbit
`{xθⁿ}`; it's a different object with extra averaging that the full geometric orbit doesn't have.)

---

## 3. mathlib: the geometric a.e.-`ξ` result is NOT present

Grepped the in-repo checkout (`.lake/packages/mathlib`, current pin). **No** hits for `equidistrib`,
`Koksma`, `lacunary`, `Hadamard gap`, or `Weyl` (in the distribution sense — the `Weyl` hits are all
root-system theory). What mathlib **does** have, both in `Mathlib/Dynamics/Ergodic/`:

| declaration | file | what it gives |
|---|---|---|
| `AddCircle.ergodic_zsmul` / `ergodic_nsmul` (+ `…_add`) | `Dynamics/Ergodic/AddCircle.lean` | the **integer `×n` endomorphism** `y ↦ n•y` on the circle is ergodic for `1 < \|n\|`. (This is the normal-numbers / base-`n` digit map.) |
| `AddCircleAdd.ergodic_add_left` / `ergodic_add_right` | `Dynamics/Ergodic/AddCircleAdd.lean` | **irrational rotation** `y ↦ a + y` is ergodic ⇔ `addOrderOf a = 0` (i.e. `a/p` irrational). (This is the `{nα}`-rotation case.) |

**Neither covers `{ξ·θⁿ}` for `θ = 2^{1/3}`:**

- `ergodic_zsmul` is multiplication by an **integer** `n`. Via Birkhoff it yields "for a.e. *starting
  point* `x`, the orbit `{nᵏx}` equidistributes" — but (a) the multiplier must be an **integer** (`2^{1/3}`
  is not), and (b) it's a.e.-*point*, never a fixed point. It is the closest analogue in mathlib and it
  **still does not apply**.
- `ergodic_add_left` is **additive** (`{nα}`, linear), not geometric. This is the "`n·θ` linear
  equidistribution via AddCircle ergodicity" you correctly identified as the only thing present.

So: **the measure-theoretic Weyl/Koksma equidistribution of `{ξθⁿ}` for a.e. `ξ` is not in mathlib.**
There is no declaration to cite. Formalizing attack-path #2 (the a.e.-`W` version) would require
**building the metric theorem from scratch** (Weyl's criterion + a second-moment/Gál–Koksma estimate
over the lacunary sequence `θⁿ`) — a substantial development, not a one-lemma import. That is real
infrastructure work, but note it is *buildable* math (unlike the fixed-`W` version, which is open).

---

## 4. Recommendation — decides the frontier lap

This **confirms attack path #1 (conditional) is the honest unconditional ceiling**, and tells you exactly
how to label the cubic in STATUS/notes:

- **Formalize the CONDITIONAL impossibility.** State it as: *"if the orbit defect `{α²f₁+α·f₂+f₃}`
  (equivalently the relevant `{Wαⁿ}` orbit) realises two configurations differing by `>1`, then no fixed
  `(c₀,c₁,c₂)` schedule reads base-2 digits."* You've already proved the algebraic + range half
  (`cubic_threestep_defect`, `cubic_combined_defect_range_wide`). The hypothesis you discharge against is
  precisely an equidistribution/orbit-realisation statement — package it as an explicit hypothesis, not
  an axiom. **This is the strongest *unconditional theorem* available**, and it's clean + citation-free.
- **Label the cubic accurately.** In STATUS.md / `CUBIC-EXPLORATION.md` / `PENDING_WORK.md`:
  > "Cubic impossibility is **open in mathematics** for the specific orbit constant `W`: it reduces to
  > whether `{W·(2^{1/3})ⁿ}` is equidistributed (or merely realises a width-`>1` defect spread), and
  > equidistribution of `{ξθⁿ}` for a *fixed* `ξ` is a famous open problem (cf. `{(3/2)ⁿ}`). The
  > **conditional** result is formalized; the **a.e.-`W`** result is provable in principle (Koksma 1935)
  > but is **not** available in mathlib and would require building the metric Weyl/Koksma theorem."

  Do **not** write "needs deep machinery we haven't built" — that wrongly implies the unconditional
  fixed-`W` result is merely an engineering lift. For the specific `W` it is **open math**.
- **Attack path #2 (a.e.-`W`) is a real but large lane,** not a quick lap: it needs the geometric
  metric theorem (absent from mathlib, §3). Worth a dedicated expedition only if you want the
  "for a.e. `W`, no schedule works" headline; otherwise path #1 is the right deliverable now.
- **Your `j≈64` numerics** are consistent with (but do not prove) the defect eventually escaping the
  width-1 window — which is exactly the open equidistribution behaviour. Keep them as *evidence*, not as
  a discharged hypothesis.

---

### Sources
- J. F. Koksma, *Ein mengentheoretischer Satz über die Gleichverteilung modulo Eins*, Compositio Math.
  **2** (1935), 250–258 — the a.e.-`ξ` / a.e.-`θ` metric theorem.
- H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Math. Ann. **77** (1916), 313–352 — the
  integer-exponent ancestor.
- L. Kuipers & H. Niederreiter, *Uniform Distribution of Sequences*, Wiley 1974, Ch. 1 §4 (textbook;
  exact theorem number unverified — cite §4).
- C. Aistleitner, M. Hofer, G. Larcher, *Quantitative uniform distribution results for geometric
  progressions*, [arXiv:1210.4215](https://arxiv.org/abs/1210.4215) (Israel J. Math. 2014) — states the
  symmetric a.e. form explicitly.
- *Equidistribution Mod 1 and Normal Numbers*, [arXiv:2109.00562](https://arxiv.org/abs/2109.00562) —
  `{(3/2)ⁿ}` u.d. open, not even known dense.
- *Integral powers of numbers in small intervals modulo 1: the cardinality gap phenomenon*,
  [arXiv:1501.07176](https://arxiv.org/abs/1501.07176) — fixed-base power distribution, open cases.
- mathlib (in-repo pin): `Mathlib/Dynamics/Ergodic/AddCircle.lean`
  (`AddCircle.ergodic_zsmul`/`ergodic_nsmul`), `Mathlib/Dynamics/Ergodic/AddCircleAdd.lean`
  (`ergodic_add_left`/`ergodic_add_right`). No equidistribution/Koksma/lacunary declarations exist.
- Repo internal: `notes/CUBIC-EXPLORATION.md`, `PENDING_WORK.md` (★ FRONTIER caveat — confirmed
  correct), `src/Erdos482/General/CubicDefect.lean`, `archive/findings/…cubic-selfref-literature.md`
  (the §2 over-claim corrected here).
