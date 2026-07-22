# ON-LINE-FINDINGS — St06 (Stoll, Acta Arith. 125 (2006), 89–100)

**Request:** 2026-06-06 item in `ON-LINE-REQUEST.md` — the PDF/text of *On a problem of Erdős and
Graham concerning digits* (Acta Arith. **125** (2006), 89–100, DOI `10.4064/aa125-1-8`), or failing
that a faithful **summary**: what St06 strengthens vs St05, its closed forms, and whether it
supersedes anything already formalized.

**Bottom line:** I could **not** obtain the full text (it is genuinely free, but its only free host —
IMPAN/Acta Arith — is a JS SPA that is erroring, and the paper is too recent for the matwbn scans,
absent from arXiv/HAL, and not indexed by shadow libraries). **But** I pinned down an authoritative
record + the published review + a hard content signal from the curated OEIS tags. **Net: do NOT
block on St06 — it is not on the critical path for #482** (see "What this means for the repo").

**Sources actually read (this host session):**
- **Crossref** REST record for the DOI (`api.crossref.org/works/10.4064/aa125-1-8`) — authoritative
  title/author/pages.
- **zbMATH Open** API (`api.zbmath.org`) — the Zbl record **1167.11302** incl. the reviewer's
  summary, MSC, keywords, and OEIS links. Also pulled St05's Zbl **1068.11008** review for the delta.
- **OEIS** (`oeis.org`) — exact names of the two sequences zbMATH ties to St06.
- **erdosproblems.com/482** — how the problem-catalog frames St05+St06.
- Stoll's IECL Lorraine publication list; dblp `98/10720`. (IMPAN `link.impan.pl`, `matwbn`, HAL,
  Google Scholar all tried; none yielded the text — see "Access paths" at the bottom.)

---

## ⚠️ Correction to a fabricated attribution (read first)

An **earlier host chat** of mine confidently called this paper **"Fuchs, C. & Stoll, T."** —
**that was a hallucination. It is wrong.** Three independent authorities agree the author is
**Thomas Stoll, SOLO:**
- Crossref: single author `Thomas Stoll`.
- zbMATH Zbl 1167.11302: `contributors.authors = [Stoll, Thomas]`.
- erdosproblems.com #482 cites it as Stoll `[St06]`, no co-author.

Clemens Fuchs is a real frequent Stoll co-author (Diophantine equations), which is presumably what
my prior session pattern-matched onto — but **not on this paper.** Cite it as **T. Stoll**.

## Verified bibliographic record

> **Stoll, Thomas.** *On a problem of Erdős and Graham concerning digits.*
> **Acta Arithmetica 125** (2006), no. 1, 89–100. DOI [10.4064/aa125-1-8](https://doi.org/10.4064/aa125-1-8).
> Zbl **1167.11302**. MSC **11B37** (Recurrences), **11A63** (Radix representation; digital problems).
> Keywords: *Graham–Pollak's sequence; digital expansion.*
> Publisher: Inst. of Mathematics, Polish Acad. of Sciences (IMPAN), Warsaw. ISSN 0065-1036.

---

## The only published "summary" that exists (zbMATH review, verbatim)

Reviewer **Ahmet Tekcan (Bursa)**, Zbl 1167.11302:

> "In this work, the author derives **further results** on a problem of Erdős and Graham concerning
> digits. **Some of these generalizations were given in the author's earlier paper** [J. Integer Seq.
> 8, No. 3, Art. 05.3.2, 8 p., electronic only (2005; Zbl 1068.11008)]."

That earlier paper (Zbl 1068.11008) **is St05**, which the repo has **already fully formalized &
axiom-clean.** So the review tells us St06 ⟂ St05 is a *"further results, with overlap"* relationship,
**not** a strict-superset that obsoletes St05.

For contrast, here is **St05's** review (Zbl 1068.11008, verbatim) — the theorem we already have:

> "… let `w>0` be a real number and `g≥2` be an integer. Let `t = w/gᵐ`, where `m = ⌊log_g w⌋`, and
> `a = g/((g−1)(t+g))`, `b = g/a`. Define `(uₙ)_{n≥1}` by `u₁=1` and
> `u_{n+1} = ⌊a(uₙ+ε)⌋` if `n` odd, `⌊b(uₙ + 1/(g−1))⌋` if `n` even, where `−1/g ≤ ε < (g+1)(g−2)/g`.
> Then `u_{2n+1} − g·u_{2n−1}` is the `n`th digit base `g` of `w`."

⟹ **St05 already gives the maximally-general statement** (any real `w>0`, any integer base `g≥2`).
This is exactly the repo's `thm13_*`. There is no "more general real-in-a-base" theorem left for
St06 to hold.

---

## Hard content signal: what St06 actually contains (from the curated OEIS tags)

zbMATH ties **two** OEIS sequences to St06 (editor-curated, i.e. they appear *in the paper*):

| OEIS | exact name | meaning |
|---|---|---|
| **A004539** | *Expansion of √2 in base 2* | the original Graham–Pollak object |
| **A004594** | *Expansion of **e** in base 3* | a **transcendental** constant in an **odd base** |

This is the tell. **St06's "further results" are concrete/curious realizations of the recurrence for
named constants — including the base-3 digits of `e`.** That matches Stoll's taste exactly (cf. his
later 2009 "fancy way" paper extracting the binary digits of `759250125√2`, and the `1−π²/e³`
constant that shows up there). Combined with the review ("further results … overlap with St05") and
the keyword shift St05→St06 ("nonlinear recurrence, digits" → "**digital expansion**"), the high-
confidence reading is:

> **St06 = the Acta Arith. companion that (a) restates the general resolution and (b) adds sharper /
> more explicit statements + showcase examples** (√2 in base 2, **e in base 3**, etc.) — i.e. the
> "deeper/sharper, explicit-coefficient" treatment, where St05 is the bare general theorem.

**Confidence:** authorship/record/keywords/OEIS/MSC = **~97%** (multiple authorities agree).
The "what St06 adds" synthesis = **~75%** (inferred from review + OEIS + keyword delta + Stoll's MO;
**not** read off the paper's theorem statements, which I could not access — treat as a strong
hypothesis, not a transcription).

---

## What this means for the repo (the actionable part)

1. **You are NOT blocked. St06 is not a prerequisite for the #482 headline.** erdosproblems.com marks
   #482 **SOLVED** on the strength of *both* St05 and St06, but the *general resolution* lives in
   **St05** (the `w>0`, base-`g≥2` theorem above) — which you have **already formalized, end-to-end,
   axiom-clean** (`thm13_*`, `erdos482_resolution`). St06 contributes *further/sharper results +
   examples*, not a missing piece of the resolution. The request's own note ("likely not on the
   critical path; St05 alone answers Erdős–Graham") is **confirmed.**

2. **Treat St06 as an OPTIONAL bonus source, mirroring the 0902.4168 "fancy way" bonus you already
   did.** The natural new target it suggests is a **showcase digit-extraction for a transcendental in
   an odd base — specifically the base-3 digits of `e`** (OEIS A004594). That would be a `Thm 1.3`
   (g=3) instantiation at `w=e`, decorated with the right `ε` and the `a,b` for `g=3`, plus an
   `e`-bound discharge (mathlib `Real.exp_one_gt_d9` / `Real.exp_one_lt_d9`, like the `1−π²/e³`
   membership check you did for Cor 3.3). **Do NOT** start this until you can see St06's *exact*
   constants — the repo's own rule (`STOLL-PAIR5-ERRATUM.md`, `SOURCES.md` "verify, don't trust")
   applies doubly to formulas I'm inferring rather than reading.

3. **Do not invent St06 theorem statements from this doc.** I am giving you the *shape* (further/
   sharper results; √2-base-2 and e-base-3 examples), not verbatim closed forms. Anything you
   formalize "from St06" must be numerically verified first (you have the harness), and ideally
   checked against the real PDF once obtained.

---

## Access paths to actually get the PDF (for a human, later)

The paper is free; its free home is just down/JS-walled from a scripted fetch. In priority order:

1. **IMPAN / Acta Arith landing page** — DOI [10.4064/aa125-1-8](https://doi.org/10.4064/aa125-1-8)
   resolves to `journals.impan.pl` → `link.impan.pl` (a JS single-page app; it 302/503'd my bot but
   should render + offer a free PDF in a real browser, since AA opens old issues). **This is the
   one Trevor should click.** Earlier-session direct guess `impan.pl/download/pdf/aa125-1-8` just
   loops to the homepage right now.
2. **The author's institutional homepage** — Thomas Stoll, IECL Université de Lorraine
   (<https://iecl.univ-lorraine.fr/membre-iecl/stoll-thomas-2/> — lists the paper, no PDF).
   Contact details, if ever needed, are his to publish, not ours to republish.
3. **Cornell alumni EZproxy** fallback if it's ever gated:
   `https://login.proxy.library.cornell.edu/login?url=https://doi.org/10.4064/aa125-1-8`.
4. **zbMATH record** (free, no full text): <https://zbmath.org/?q=an:1167.11302>.

**Dead ends I verified so you don't repeat them:** matwbn (`matwbn.icm.edu.pl/ksiazki/aa/aa125/…`)
does not host vol 125 (all 404) — its AA scans stop before 2006. No arXiv preprint. No HAL deposit.
Not in Sci-Hub/shadow libraries (they index AA *books*, not individual articles). Crossref carries
no abstract field for it.

---

## Faithfulness flags
- **Solo-Stoll authorship**: ~97% (Crossref + zbMATH + erdosproblems agree; prior "Fuchs & Stoll"
  was my own fabrication — corrected here).
- **Record / MSC / keywords / OEIS tags / Zbl number**: ~97% (zbMATH + Crossref + OEIS, all read live).
- **zbMATH review text**: quoted verbatim from the zbMATH Open API; high confidence it's complete (AA
  reviews are short — this *is* the whole review).
- **"St06 = sharper/explicit companion incl. e-in-base-3 example" synthesis**: ~75%, **inferred**
  from the review + OEIS A004594 + the St05→St06 keyword shift + Stoll's known style. NOT read from
  the paper. The exact theorem statements / closed forms remain unseen — get the PDF before
  formalizing anything attributed to St06.
- **"Not on the critical path for #482"**: ~90% (St05 is the general resolution and is already
  formalized; erdosproblems credits St05+St06 jointly but the resolution is St05's; review frames
  St06 as "further results" overlapping St05).
