#!/usr/bin/env python3
"""Show pair-5's true admissible eps-interval SHRINKS toward {1/2} as the digit-horizon grows.
Exact: admissible band for sqrt2*eps from constraints up to horizon H is
  [ max_{m<=H} (-g_m) , min_{m<=H} (1-g_m) ),  g_m = (2-sqrt2){sqrt2 2^m} - [ {sqrt2 2^m}>=1/2 ].
Also: first-fail n for several eps between xi1 and 1/2 (exact integer recurrence)."""
from math import isqrt
from decimal import Decimal, getcontext
getcontext().prec = 2000
S2 = Decimal(2).sqrt(); HALF = Decimal(1)/2

def fracD(x): return x - x.to_integral_value(rounding='ROUND_FLOOR')

def band(H):
    lo, hi = Decimal(-10), Decimal(10)
    lo_m = hi_m = -1
    for m in range(0, H + 1):
        f = fracD(S2 * (Decimal(2) ** m))
        g = (2 - S2) * f - (1 if f >= HALF else 0)
        if -g > lo: lo, lo_m = -g, m
        if 1 - g < hi: hi, hi_m = 1 - g, m
    return lo, hi, lo_m, hi_m

xi1 = Decimal(309)/2*S2 - 218
xi2 = Decimal(1296121037)/2*S2 - 916495974
print("Stoll's stated pair-5 interval:  eps in [%.10f , %.10f)  (width %.5e)" %
      (xi1, xi2, xi2 - xi1))
print("                                                                  1/2 = 0.5\n")
print("=== TRUE admissible eps-interval vs digit-horizon H (must hold for all m<=H) ===")
print(f"  {'H':>6} {'eps_lo':>16} {'eps_hi':>16} {'width':>12}  binding(m_lo,m_hi)")
for H in [50, 200, 600, 2000, 6000, 15000]:
    lo, hi, lm, hm = band(H)
    elo, ehi = lo / S2, hi / S2
    print(f"  {H:>6} {elo:>16.10f} {ehi:>16.10f} {ehi-elo:>12.3e}  ({lm},{hm})")

# exact integer recurrence: first n where digits of sqrt2 break, for eps between xi1 and 1/2
def floor_x_sqrt2(x): return isqrt(2*x*x) if x >= 0 else -(isqrt(2*x*x)+1)
def step_half(v): return isqrt(2*(2*v+1)**2)//2
def step_eps(v, c, d): return c + floor_x_sqrt2(v - d)
def sbit(k): return isqrt(2**(2*k+1)) % 2
def first_fail(c, d, nmax):
    v = [None, 1]
    for m in range(1, 2*nmax+6):
        v.append(step_eps(v[m], c, d) if m % 2 == 1 else step_half(v[m]))
    for n in range(1, nmax+1):
        if 2*n+1 >= len(v): break
        if v[2*n+1] - 2*v[2*n-1] != sbit(n-1):
            return n
    return None

print("\n=== first-fail n for exact algebraic eps = (c/2)sqrt2 - d (digits of sqrt2), nmax=4000 ===")
# eps values of the (c/2)sqrt2 - d form at increasing closeness to 1/2:
#   xi1: c=309,d=218 (0.49600)  |  v_n based dyadic-ish approximants to 1/2
cand = [
    ("xi1 = 309/2 v2 - 218",            309, 218),
    ("c=746, d=527  (~0.49874)",        746, 527),     # 527/746 ~ ... near 1/sqrt2
    ("c=1817, d=1285 (~0.49968)",       1817, 1285),
    ("c=4756, d=3363 (~0.49995)",       4756, 3363),
    ("1/2 exact (every step half)",     None, None),
]
for label, c, d in cand:
    if c is None:
        # eps = 1/2: all half steps
        v = [None, 1]
        for m in range(1, 2*4000+6): v.append(step_half(v[m]))
        ff = None
        for n in range(1, 4000):
            if v[2*n+1]-2*v[2*n-1] != sbit(n-1): ff = n; break
        approx = 0.5
    else:
        approx = float(Decimal(c)/2*S2 - d)
        ff = first_fail(c, d, 4000)
    print(f"  {label:34} eps~{approx:.6f}  first-fail n = {ff}")
