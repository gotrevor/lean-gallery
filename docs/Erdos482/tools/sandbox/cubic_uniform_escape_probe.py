#!/usr/bin/env python3
"""Cubic three-step digit map: probe whether the survival length is UNIFORMLY BOUNDED over schedules.

The three-step map with 3-periodic offsets (c0,c1,c2) and multiplier a=2^{1/3}:
    v1 = floor(a*(u+c0)); v2 = floor(a*(v1+c1)); v3 = floor(a*(v2+c2)); next u = v3.
Block digit = v3 - 2u must be in {0,1} for a base-2 readout.  `first_fail` returns the first block at
which the digit leaves {0,1} (None if it survives `maxstep`).

PENDING_WORK ★ attack-path #3 asks: is sup over all schedules of the survival length FINITE?  If yes,
a finite decidable check gives an UNCONDITIONAL cubic impossibility (no equidistribution needed).

Observations (float64, coarse search):
- random (c0,c1,c2)∈[0,2]^3, u0=1: mean first-fail ≈ 0.9, max ≈ 52 over 4000 samples.
- the literature-noted triple (1/6,1/3,4/3): first-fail ≈ 51 (float64) / ~64 (doc, higher precision).
- 31^3 grid (span ±0.06) around that triple, varied u0: best first-fail ≈ 51 — tuning did NOT push it
  much past ~64.

This is AMBIGUOUS, not a refutation: a measure-zero schedule (special algebraic offsets) could survive
far longer than a coarse float grid resolves.  To decide path #3, rerun with mpmath high precision,
finer/adaptive search, and varied starts; if the sup is genuinely bounded (~64), path #3 is the
unconditional route.  If survival length is unbounded as offsets are fine-tuned (Liouville-like), the
unconditional result needs the (open) {a^n xi} equidistribution and only the CONDITIONAL theorem
(`cubic_threestep_digit_pair_fails`) is provable.
"""
import math, random
from decimal import Decimal, getcontext
from fractions import Fraction

A = 2.0 ** (1.0 / 3.0)

# ---------------------------------------------------------------------------
# ⚠️ FLOAT-PRECISION CAVEAT (2026-06-14): u doubles each block, so by block ~52
# u ≈ 2^52 hits float64's 2^53 integer-precision wall — float `first_fail` then
# reports SPURIOUS failures. The float "survival caps at ~52" is therefore an
# ARTIFACT, not a uniform bound. Use `first_fail_exact` (below) past ~block 45.
# Exact check: the literature triple (1/6,1/3,4/3) genuinely fails at block 63
# (matches the doc's "j=64", off-by-one), NOT 52. Whether sup over schedules is
# finite (⇒ path #3 unconditional proof) is OPEN and needs an exact-arithmetic
# search — float searches cannot resolve it.
# ---------------------------------------------------------------------------

getcontext().prec = 400
_x = Decimal("1.26")
for _ in range(80):
    _x = (2 * _x + Decimal(2) / (_x * _x)) / 3
A_EXACT = _x  # 2^(1/3) to ~400 digits


def _dfloor(d):
    return int(d.to_integral_value(rounding="ROUND_FLOOR"))


def first_fail_exact(c0, c1, c2, u0=1, maxstep=400):
    """Exact survival length with rational offsets (Fraction) and ~400-digit a."""
    C0, C1, C2 = (Decimal(c.numerator) / Decimal(c.denominator) for c in (c0, c1, c2))
    u = u0
    for j in range(maxstep):
        v1 = _dfloor(A_EXACT * (Decimal(u) + C0))
        v2 = _dfloor(A_EXACT * (Decimal(v1) + C1))
        v3 = _dfloor(A_EXACT * (Decimal(v2) + C2))
        d = v3 - 2 * u
        if d not in (0, 1):
            return j
        u = v3
    return None


def first_fail(c0, c1, c2, u0=1, maxstep=3000):
    u = u0
    for j in range(maxstep):
        v1 = math.floor(A * (u + c0))
        v2 = math.floor(A * (v1 + c1))
        v3 = math.floor(A * (v2 + c2))
        d = v3 - 2 * u
        if d not in (0, 1):
            return j
        u = v3
    return None


def random_scan(n=4000, seed=1):
    random.seed(seed)
    fails = []
    for _ in range(n):
        c = [random.uniform(0, 2) for _ in range(3)]
        f = first_fail(*c, 1)
        fails.append(f if f is not None else 10 ** 9)
    fin = [f for f in fails if f < 10 ** 9]
    print(f"random schedules: n={n} max={max(fin)} mean={sum(fin)/len(fin):.2f} "
          f"survived={sum(1 for f in fails if f>=10**9)}")


def grid_near(base=(1 / 6, 1 / 3, 4 / 3), n=31, span=0.06, cap=400):
    best, cfg = 0, None
    lin = [-span + 2 * span * i / (n - 1) for i in range(n)]
    for d0 in lin:
        for d1 in lin:
            for d2 in lin:
                f = first_fail(base[0] + d0, base[1] + d1, base[2] + d2, 1, cap)
                if f and f > best:
                    best, cfg = f, (round(base[0] + d0, 4), round(base[1] + d1, 4), round(base[2] + d2, 4))
    print(f"grid near {tuple(round(b,4) for b in base)} (cap {cap}): best={best} at {cfg}")


if __name__ == "__main__":
    print("doc triple (1/6,1/3,4/3) float:", first_fail(1 / 6, 1 / 3, 4 / 3, 1),
          " EXACT:", first_fail_exact(Fraction(1, 6), Fraction(1, 3), Fraction(4, 3)))
    random_scan()
    grid_near()
