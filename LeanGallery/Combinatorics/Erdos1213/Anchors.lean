/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanGallery.Combinatorics.Erdos1213.Main

/-!
# Erdős #1213 — machine-checked anchors + certified lower bounds

Two jobs, both *executable* evidence, neither touching the headline theorem's trust base
(`#print axioms hegyvari_thm3` stays `[propext, Classical.choice, Quot.sound]`):

1. **Faithfulness anchors.** The headline statement is only as trustworthy as `csum` /
   `AllCSumsDistinct`. We check that those definitions compute as intended: known-valid sequences are
   `AllCSumsDistinct`, known-invalid ones are not (incl. the paper's `f(2,2)=10` **erratum**).
2. **Certified lower bounds on `f(1,K)`.** The Rust solver (`notes/`, `tools/sandbox/erdos1213_rs/`)
   found exact maxima; here we *certify* each by exhibiting its explicit witness sequence and
   machine-checking it is valid, giving `f(1,K) ≥ (last term)` for `K = 1..7`. (The matching upper
   bound is asymptotic/open — see `notes/BOUND-TIGHTENING.md`. These are the rigorous half: the
   "prove the experiment" lower bounds, the only part currently provable.)

## Why a Bool checker (not a `Decidable` instance)

`AllCSumsDistinct` is an unbounded `∀` over `ℕ`, so it has no `Decidable` instance, and a bounded
mirror via `Nat.decidableBallLE` / `Finset.decidableBAll` **fails to synthesize** through the nested
implication chain (tried; it doesn't fire). So we use a plain `Bool` function `distinctB` built from
`List.all` — no typeclass resolution at all — prove `distinctB a s = true ↔ AllCSumsDistinct a s`,
and evaluate the Bool. The pattern is `rw [← distinctB_iff]; decide +kernel`.

## Which evaluator, and why 🔑

`decide +kernel` evaluates in the **kernel**, adding no axioms of its own, so those uses rest on
exactly the whitelist above. It is the default here and is used everywhere it is affordable: all
seven faithfulness anchors, and the certified bounds for `K ≤ 4` (plus every `stepsOkB` check,
which is linear in the witness length).

`distinctB` is a 4-deep loop with a `csum` inside, so it costs about `s⁵` in the witness length
`s`. That curve ends the party. Measured, kernel-checking the `distinctB` obligation:

| `K` | `s` = witness length | `decide +kernel` |
|-----|----------------------|------------------|
| 2, 3 | 4, 9 | instant |
| 4 | 17 | ~5s |
| 5 | 26 | ~33s |
| 6 | 36 | ~5.5 min |
| 7 | 47 | not viable |

So `K = 5, 6, 7` keep `native_decide` for that one obligation, and **those three theorems alone
carry a compiler axiom** (`hegyvariF_ge_1_5/6/7`; check with `#print axioms`). Rewriting the
checker `Quot`-free (a `List` fold instead of `Finset.Icc`) was tried and does *not* help — the
cost is the raw `s⁵` volume, not the `Finset`/`Multiset` overhead. Closing this properly needs an
algorithmic fix (prefix sums, or collecting the c-sums and checking for duplicates in `s² log s`),
not a better evaluator.
-/

namespace LeanGallery.Combinatorics.Erdos1213
open Finset

/-- Bool mirror of `AllCSumsDistinct` on blocks inside `[1,s]`: every pair of blocks with equal c-sum
is the same block.  Built from `List.all` + `decide` of a (decidable) implication, so it carries no
`Decidable (AllCSumsDistinct …)` obligation and the evaluator computes it directly. -/
def distinctB (a : ℕ → ℕ) (s : ℕ) : Bool :=
  (List.range' 1 s).all fun u₁ =>
  (List.range' 1 s).all fun v₁ =>
  (List.range' 1 s).all fun u₂ =>
  (List.range' 1 s).all fun v₂ =>
    decide (u₁ ≤ v₁ → u₂ ≤ v₂ → csum a u₁ v₁ = csum a u₂ v₂ → u₁ = u₂ ∧ v₁ = v₂)

theorem distinctB_iff (a : ℕ → ℕ) (s : ℕ) :
    distinctB a s = true ↔ AllCSumsDistinct a s := by
  simp only [distinctB, List.all_eq_true, List.mem_range'_1, decide_eq_true_eq]
  unfold AllCSumsDistinct
  constructor
  · intro h u₁ v₁ u₂ v₂ ha1 hb1 hc1 ha2 hb2 hc2 hsum
    exact h u₁ ⟨ha1, by omega⟩ v₁ ⟨by omega, by omega⟩ u₂ ⟨ha2, by omega⟩ v₂ ⟨by omega, by omega⟩
      hb1 hb2 hsum
  · rintro h u₁ ⟨h1a, h1b⟩ v₁ ⟨h2a, h2b⟩ u₂ ⟨h3a, h3b⟩ v₂ ⟨h4a, h4b⟩ huv1 huv2 hsum
    exact h u₁ v₁ u₂ v₂ h1a huv1 (by omega) h3a huv2 (by omega) hsum

/-- A 1-indexed sequence from an explicit list: `seqOf l i = l[i-1]` (with `0` past the end). -/
def seqOf (l : List ℕ) : ℕ → ℕ := fun i => l.getD (i - 1) 0

/-! ## Faithfulness anchors

`distinctB`-based, so this evaluates the *real* `AllCSumsDistinct` (via `distinctB_iff`), kernel-pure. -/

/-- `f(1,1) = 2`, witness `[1,2]`. -/
example : AllCSumsDistinct (seqOf [1, 2]) 2 := by rw [← distinctB_iff]; decide +kernel

/-- `f(2,1) = 4`, witness `[2,3,4]`. -/
example : AllCSumsDistinct (seqOf [2, 3, 4]) 3 := by rw [← distinctB_iff]; decide +kernel

/-- `f(1,2) = 7`, witness `[1,3,5,7]`. -/
example : AllCSumsDistinct (seqOf [1, 3, 5, 7]) 4 := by rw [← distinctB_iff]; decide +kernel

/-- **Corrected** `f(2,2) = 8`, witness `[2,3,4,6,8]`. -/
example : AllCSumsDistinct (seqOf [2, 3, 4, 6, 8]) 5 := by rw [← distinctB_iff]; decide +kernel

/-- **The paper's `f(2,2)=10` is an erratum.** Its only candidate (gaps all `2`) collides:
`a₁+a₂ = 2+4 = 6 = a₃`. So `[2,4,6,8,10]` is NOT all-c-sums-distinct. -/
example : ¬ AllCSumsDistinct (seqOf [2, 4, 6, 8, 10]) 5 := by rw [← distinctB_iff]; decide +kernel

/-- One step past `f(1,1)=2`: `[1,2,3]` collides (`a₁+a₂ = 3 = a₃`). -/
example : ¬ AllCSumsDistinct (seqOf [1, 2, 3]) 3 := by rw [← distinctB_iff]; decide +kernel

/-- One step past `f(2,2)=8`: `[2,3,4,6,8,9]` collides (`9 = a₆ = a₁+a₂+a₃`). -/
example : ¬ AllCSumsDistinct (seqOf [2, 3, 4, 6, 8, 9]) 6 := by rw [← distinctB_iff]; decide +kernel

/-! ## Certified lower bounds on `f(1,K)`

Each computed maximum `f(1,K)` is certified by exhibiting its explicit witness sequence and
machine-checking it is a valid member of `validLastTerms 1 K` (strictly increasing, gaps `≤ K`, all
c-sums distinct). With `BddAbove`, `le_csSup` gives `f(1,K) = sSup (validLastTerms 1 K) ≥ (last term)`.
These are the rigorous "prove the experiment" lower bounds (the matching `O(K²)`-style upper bound is
open — see `notes/BOUND-TIGHTENING.md`). Together with `erdos_1213_f_finite` they sandwich `f(1,K)`. -/

/-- Bool check that the consecutive entries of `w` strictly increase with gaps `≤ K`. -/
def stepsOkB (K : ℕ) (w : List ℕ) : Bool :=
  (List.range (w.length - 1)).all fun i =>
    decide (w.getD i 0 < w.getD (i + 1) 0 ∧ w.getD (i + 1) 0 ≤ w.getD i 0 + K)

/-- `stepsOkB` certifies the monotonicity and gap conditions of `validLastTerms` for `seqOf w`. -/
theorem stepsOkB_spec (K : ℕ) (w : List ℕ) (h : stepsOkB K w = true) :
    ∀ i, 1 ≤ i → i < w.length →
      seqOf w i < seqOf w (i + 1) ∧ seqOf w (i + 1) ≤ seqOf w i + K := by
  simp only [stepsOkB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro i hi1 hi2
  have key := h (i - 1) (by omega)
  have e1 : i - 1 + 1 = i := by omega
  rw [e1] at key
  simpa only [seqOf, Nat.add_sub_cancel] using key

/-- `validLastTerms init K` is bounded above (by `⌊L⌋₊`), so its `sSup` is well-behaved. -/
theorem bddAbove_validLastTerms (init K : ℕ) (hK : 1 ≤ K) (ha : 1 ≤ init) :
    BddAbove (validLastTerms init K) := by
  refine ⟨⌊hegyvariBound (fun _ => init) K⌋₊, fun n hn => ?_⟩
  have hlt := validLastTerms_lt_bound init K hK ha hn
  have h1 : n = ⌊(n : ℝ)⌋₊ := (Nat.floor_natCast n).symm
  exact h1 ▸ Nat.floor_mono (le_of_lt hlt)

/-- Bridge: a machine-checkable witness list yields membership in `validLastTerms`. -/
theorem mem_validLastTerms (init K : ℕ) (w : List ℕ)
    (hlen : 1 ≤ w.length) (hhead : seqOf w 1 = init)
    (hsteps : stepsOkB K w = true) (hdist : distinctB (seqOf w) w.length = true) :
    seqOf w w.length ∈ validLastTerms init K :=
  ⟨w.length, seqOf w, hhead, hlen, rfl,
    fun i hi1 hi2 => (stepsOkB_spec K w hsteps i hi1 hi2).1,
    fun i hi1 hi2 => (stepsOkB_spec K w hsteps i hi1 hi2).2,
    (distinctB_iff _ _).mp hdist⟩

/-- Witnesses (max-last-term sequences) found by exhaustive search (`tools/sandbox/erdos1213_rs/`). -/
def w1 : List ℕ := [1, 2]
def w2 : List ℕ := [1, 3, 5, 7]
def w3 : List ℕ := [1, 4, 7, 10, 13, 14, 15, 18, 20]
def w4 : List ℕ := [1, 5, 9, 12, 16, 18, 22, 25, 29, 30, 32, 35, 38, 41, 44, 48, 52]
def w5 : List ℕ :=
  [1, 6, 11, 16, 20, 24, 28, 31, 35, 38, 42, 43, 46, 51, 56, 61, 64, 69, 74, 76, 81, 86, 87, 92, 96, 101]
def w6 : List ℕ :=
  [1, 7, 13, 19, 25, 31, 37, 43, 48, 54, 60, 66, 71, 77, 83, 89, 92, 98, 103, 104, 108, 113, 119, 124,
   129, 134, 138, 142, 144, 150, 154, 157, 161, 165, 170, 174]
def w7 : List ℕ :=
  [1, 8, 15, 20, 26, 33, 40, 47, 51, 57, 64, 71, 77, 83, 90, 97, 104, 111, 116, 123, 129, 136, 140,
   147, 154, 161, 165, 168, 174, 177, 182, 188, 193, 198, 203, 205, 211, 214, 220, 226, 230, 237,
   244, 248, 255, 257, 264]

/-- A uniform certified lower bound from a witness: `val ≤ f(1,K)`. -/
theorem hegyvariF_ge (K : ℕ) (hK : 1 ≤ K) (w : List ℕ) (val : ℕ)
    (hlen : 1 ≤ w.length) (hhead : seqOf w 1 = 1)
    (hsteps : stepsOkB K w = true) (hdist : distinctB (seqOf w) w.length = true)
    (hval : seqOf w w.length = val) :
    val ≤ hegyvariF 1 K := by
  have hb := bddAbove_validLastTerms 1 K hK (le_refl 1)
  have hmem := mem_validLastTerms 1 K w hlen hhead hsteps hdist
  exact hval ▸ le_csSup hb hmem

/-- `f(1,1) ≥ 2`. -/
theorem hegyvariF_ge_1_1 : 2 ≤ hegyvariF 1 1 :=
  hegyvariF_ge 1 (by norm_num) w1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `f(1,2) ≥ 7`. -/
theorem hegyvariF_ge_1_2 : 7 ≤ hegyvariF 1 2 :=
  hegyvariF_ge 2 (by norm_num) w2 7 (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
/-- `f(1,3) ≥ 20`. -/
theorem hegyvariF_ge_1_3 : 20 ≤ hegyvariF 1 3 :=
  hegyvariF_ge 3 (by norm_num) w3 20 (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
/-- `f(1,4) ≥ 52`. -/
theorem hegyvariF_ge_1_4 : 52 ≤ hegyvariF 1 4 :=
  hegyvariF_ge 4 (by norm_num) w4 52 (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
/-- `f(1,5) ≥ 101`. -/
theorem hegyvariF_ge_1_5 : 101 ≤ hegyvariF 1 5 :=
  hegyvariF_ge 5 (by norm_num) w5 101 (by decide) (by decide) (by decide) (by native_decide) (by decide)
/-- `f(1,6) ≥ 174`. -/
theorem hegyvariF_ge_1_6 : 174 ≤ hegyvariF 1 6 :=
  hegyvariF_ge 6 (by norm_num) w6 174 (by decide) (by decide) (by decide) (by native_decide) (by decide)
/-- `f(1,7) ≥ 264`. -/
theorem hegyvariF_ge_1_7 : 264 ≤ hegyvariF 1 7 :=
  hegyvariF_ge 7 (by norm_num) w7 264 (by decide) (by decide) (by decide +kernel) (by native_decide)
    (by decide)

end LeanGallery.Combinatorics.Erdos1213
