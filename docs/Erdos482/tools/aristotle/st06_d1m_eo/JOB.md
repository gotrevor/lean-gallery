# Aristotle job — `st06_d1m_eo`

**UUID:** `b2089b31-0d4a-4f98-b82c-3fa6c1b22c9c` (submitted 2026-06-13)

**Goal:** even→odd inequality core for St06 Thm 3.1 subcone **𝒟₁⁻** (`l<0`, `k<0`, `a>0`):
`0 ≤ l/(g−1)+a(ε−f) < 1`. See `Problem.lean`.

**Status:** submitted in parallel; we ALSO proved this by hand as `d1m_core` in
`src/Erdos482/General/St06Thm31.lean` (kernel-verified, axiom-clean, already in the build). The
Aristotle run is a cross-validation. Statement verified numerically (~160k points) before submission.
