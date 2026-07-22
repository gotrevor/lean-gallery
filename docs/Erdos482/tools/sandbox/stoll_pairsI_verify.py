#!/usr/bin/env python3
"""Sanity check: do the i in I pairs (eq8-uniform) hold over their FULL stated intervals
to large n, with the SAME exact machinery used for pair 5?  If yes, the setup is sound and
pair 5's failure is real, not a bug.  Tests digits of t_i (not sqrt2)."""
from math import isqrt

def floor_x_sqrt2(x):
    return isqrt(2 * x * x) if x >= 0 else -(isqrt(2 * x * x) + 1)

def step_half(v):
    return isqrt(2 * (2 * v + 1) ** 2) // 2

def step_eps(v, c, d):           # eps = (c/2)sqrt2 - d
    return c + floor_x_sqrt2(v - d)

def vseq(c, d, n):
    v = [None, 1]
    for m in range(1, n):
        v.append(step_eps(v[m], c, d) if m % 2 == 1 else step_half(v[m]))
    return v

def floor_t_pow(alpha, beta, l, j):
    """floor(t * 2^j) where t=(alpha*sqrt2 - beta)/2^l, for j>=l (so beta*2^{j-l} integral)."""
    e = j - l
    assert e >= 0
    return floor_x_sqrt2(alpha * (2 ** e)) - beta * (2 ** e)   # = floor(alpha*sqrt2*2^e) - beta*2^e

def t_bit(alpha, beta, l, n):
    """n-th binary digit of t_i = floor(t 2^n) - 2 floor(t 2^{n-1})."""
    return floor_t_pow(alpha, beta, l, n) - 2 * floor_t_pow(alpha, beta, l, n - 1)

def first_digit_fail(seq, alpha, beta, l, nmax):
    for n in range(l + 3, nmax + 1):          # digits valid only for n >= l_i+3 (skip transient)
        if 2 * n + 1 >= len(seq):
            break
        d = seq[2 * n + 1] - 2 * seq[2 * n - 1]
        ref = floor_t_pow(alpha, beta, l, n - 1) - 2 * floor_t_pow(alpha, beta, l, n - 2)  # (n-1)-th bit
        if d != ref:
            return n
    return None

NMAX = 1500
N = 2 * NMAX + 6

# (label, c_lower, d_lower, alpha, beta, l)  -- eps at the INCLUDED lower endpoint xi1_i
PAIRS = [
    ("pair 1  eps=xi1 [1-v2/2 .. )",        1,        1,        1,         1,        0),
    # xi1_1 = 1 - sqrt2/2 = -(1/2)sqrt2 + 1 -> (c/2)sqrt2 - d with c=-1,d=-1
    ("pair 2  eps=xi1",                      None,     None,     11,        5,        3),
    ("pair 4  eps=xi1 = 77/2 v2 - 54",       77,       54,       181,       75,       7),
    ("pair 6  eps=xi1 = 1296121037/2 v2-9e8",1296121037,916495974,759250125, 314491699,29),
    ("pair 8  eps=xi1 = 5/2 v2 - 3",         5,        3,         3,         1,        1),
]
# fix pair1 lower endpoint (1 - sqrt2/2): c=-1, d=-1
PAIRS[0] = ("pair 1  eps=xi1 = 1 - v2/2",   -1,       -1,        1,         1,        0)
# pair2 lower endpoint xi1_2 = sqrt2 - 1 = (2/2)sqrt2 - 1 -> c=2,d=1
PAIRS[1] = ("pair 2  eps=xi1 = v2 - 1",      2,        1,        11,        5,        3)

print(f"=== i-in-I pairs: digit-of-t_i first-fail over FULL interval, eps at INCLUDED lower endpoint ===")
print(f"    (exact arithmetic, tested to n={NMAX})\n")
print(f"  {'pair / eps':40} {'alpha,beta,l':>16} {'digit-fail n':>12}")
for label, c, d, a, b, l in PAIRS:
    seq = vseq(c, d, N)
    ff = first_digit_fail(seq, a, b, l, NMAX)
    print(f"  {label:40} {f'{a},{b},{l}':>16} {str(ff):>12}")

print("\n=== contrast: pair 5 (digits of sqrt2) at its endpoints ===")
def first_sqrt2_digit_fail(seq, nmax):
    def bit(k): return isqrt(2 ** (2 * k + 1)) % 2
    for n in range(1, nmax + 1):
        if 2 * n + 1 >= len(seq): break
        if seq[2 * n + 1] - 2 * seq[2 * n - 1] != bit(n - 1):
            return n
    return None
for label, c, d in [("pair5 eps=xi1=309/2 v2-218 (INCLUDED)", 309, 218),
                    ("pair5 eps=1/2 (GP, interior)", None, None)]:
    if c is None:
        v = [None, 1]
        for m in range(1, N): v.append(step_half(v[m]))
        seq = v
    else:
        seq = vseq(c, d, N)
    print(f"  {label:42} digit-fail n = {first_sqrt2_digit_fail(seq, NMAX)}")
