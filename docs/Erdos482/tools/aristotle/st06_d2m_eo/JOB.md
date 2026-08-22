# Aristotle job — `st06_d2m_eo`

**UUID:** `eaaf4840-cd44-4a21-9808-9e2549f6c2ee` (submitted 2026-06-13)

**Goal:** real-analysis core of St06 Thm 3.1's even→odd step for subcone 𝒟₂⁻ — the two-sided bound
`0 ≤ l/(g−1) + a(ε−f) < 1`. Pure inequality (no floor in conclusion). See `Problem.lean`.

**Status:** COMPLETE (2026-06-13) — Aristotle proved it (axiom-clean per its own check), independently
confirming the statement. We ALSO proved the same lemma by hand as `d2m_core` in
`src/Erdos482/General/St06Thm31.lean` (already in the build, kernel-verified axiom-clean), so the
Aristotle proof is a cross-validation, not ported. The full 𝒟₂⁻ subcone of St06 Thm 3.1 is now
formalized (`st06_thm31_d2m_closed` / `_digits`), with Example 1.1 recovered as the `(3,3,2,−1)`
instance (`st06_example11_from_thm31`).

**Key finding baked into the statement (numerically verified, ~1M points):** the 𝒟₂⁻ ε-interval is
`1 + (g−l−1)(mg+1)/(klg) ≤ ε < −(mg+1)/(kg)` — the UPPER endpoint has **no extra "+1"** (the
`notes/ST06-PLAN.md` transcription "ε < 1+δ₂⁻" overshoots; with the +1 the core fails, e.g.
g=3,m=1,l=1,k=−1,t=1.27,ε=1.93 gives val=−0.18 < 0). See `notes/ST06-THM31-ERRATUM.md`.
