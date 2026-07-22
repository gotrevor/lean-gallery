#!/usr/bin/env python3
"""Does pair-5's DIGIT claim (d_n = bit of sqrt2) hold over [xi1,xi2), even where the
closed form breaks?  Exact integer arithmetic.  Also: map the true validity interval."""
from math import isqrt

def floor_x_sqrt2(x):
    return isqrt(2 * x * x) if x >= 0 else -(isqrt(2 * x * x) + 1)

def floor_sqrt2_pow(k):
    return isqrt(2 ** (2 * k + 1))

def step_half(v):
    return isqrt(2 * (2 * v + 1) ** 2) // 2

def step_eps(v, c, d):           # eps = (c/2)sqrt2 - d
    return c + floor_x_sqrt2(v - d)

def vseq(c, d, n):
    v = [None, 1]
    for m in range(1, n):
        v.append(step_eps(v[m], c, d) if m % 2 == 1 else step_half(v[m]))
    return v

def vseq_half(n):
    v = [None, 1]
    for m in range(1, n):
        v.append(step_half(v[m]))
    return v

def sqrt2_bit(k):
    return floor_sqrt2_pow(k) % 2

def first_digit_fail(seq, nmax):
    """d_n = v_{2n+1}-2v_{2n-1} should equal sqrt2_bit(n-1). Return first failing n."""
    for n in range(1, nmax + 1):
        if 2 * n + 1 >= len(seq):
            break
        d = seq[2 * n + 1] - 2 * seq[2 * n - 1]
        if d != sqrt2_bit(n - 1):
            return n
    return None

def first_closedform_fail(seq, kmax):
    for k in range(1, kmax + 1):
        if 2 * k + 1 >= len(seq):
            break
        if seq[2 * k] != floor_sqrt2_pow(k - 1) + 2 ** (k - 1) or \
           seq[2 * k + 1] != floor_sqrt2_pow(k - 1) + 2 ** k:
            return k
    return None

NMAX = 600
N = 2 * NMAX + 6

c1, d1 = 309, 218                       # xi1_5
c2, d2 = 1296121037, 916495974         # xi2_5

print("=== DIGIT claim d_n = sqrt2 bit, and closed-form, first-fail index ===")
print(f"  (tested to n/k = {NMAX}; exact integer arithmetic)\n")

cases = [
    ("xi1 = 309/2 v2 - 218          (pair-5 INCLUDED lower)", vseq(c1, d1, N)),
    ("xi2 = 1296121037/2 v2 - 9e8   (pair-5 EXCLUDED upper)", vseq(c2, d2, N)),
]
vh = vseq_half(N)
print(f"  {'eps':52} {'digit-fail n':>12} {'closedform-fail k':>18}")
print(f"  {'eps = 1/2 (Graham-Pollak)':52} {str(first_digit_fail(vh,NMAX)):>12} {str(first_closedform_fail(vh,NMAX)):>18}")
for label, seq in cases:
    print(f"  {label:52} {str(first_digit_fail(seq,NMAX)):>12} {str(first_closedform_fail(seq,NMAX)):>18}")

# --- Map the TRUE validity interval: scan eps = (c/2)sqrt2 - d over candidate (c,d) ---
# Use the convergent-like endpoints from neighbors; also brute force a fine eps grid via
# the bracket sign to find {eps : digits hold for all n<=NMAX}.
# Cheap proxy: directly bisect on a real eps using float is too imprecise; instead test the
# family eps_t = 1/2 + t for rational t won't be (c/2)sqrt2-d. So just report what we have.

# How close does {sqrt2 2^m} get to 1/2 over m=0..NMAX (drives endpoints)?
from decimal import Decimal, getcontext
getcontext().prec = 400
S2 = Decimal(2).sqrt(); HALF = Decimal(1)/2
def fracD(x): return x - x.to_integral_value(rounding='ROUND_FLOOR')
rows = []
for m in range(0, NMAX + 2):
    f = fracD(S2 * (Decimal(2) ** m))
    rows.append((abs(f - HALF), m, f))
rows.sort()
print("\n=== closest {sqrt2*2^m} to 1/2, m=0..%d (top 12) ===" % NMAX)
for dist, m, f in rows[:12]:
    side = "BELOW" if f < HALF else "ABOVE"
    print(f"  m={m:>3}  dist={dist:.4e} ({side} 1/2)")

# The validity for eps: need for all k: 0 <= g(x_k) + sqrt2*eps < 1, g(x_k)=g(sqrt2 2^k).
# g near sup 1-sqrt2/2 when {sqrt2 2^{k-1}} -> 1/2^- ; near inf -sqrt2/2 when -> 1/2^+.
# sqrt2*eps must lie in ( sup over BELOW-approaches of (sqrt2/2 - gap) , ... ). Compute the
# exact admissible band for sqrt2*eps from the worst approaches:
sqrt2 = S2
# For each m, {sqrt2 2^m}=f. This contributes a constraint via k=m+1 (x=sqrt2 2^{m+1}, x/2=sqrt2 2^m).
# g(x) = (2-sqrt2)*f         if f<1/2   (then near 1-sqrt2/2)  -> need sqrt2 eps < 1 - g  => upper bound
#      = (2-sqrt2)*f - 1     if f>=1/2  (near -sqrt2/2)        -> need sqrt2 eps >= -g     => lower bound
lo = Decimal(0)          # sqrt2*eps must be >  lo  (from f>1/2 approaches): need sqrt2 eps >= 1-(2-sqrt2)f
hi = Decimal(2)          # sqrt2*eps must be <  hi  (from f<1/2 approaches): need sqrt2 eps < 1-(2-sqrt2)f
lo_m = hi_m = -1
for m in range(0, NMAX + 2):
    f = fracD(S2 * (Decimal(2) ** m))
    g = (2 - sqrt2) * f - (1 if f >= HALF else 0)
    # need 0 <= g + sqrt2 eps < 1  ->  -g <= sqrt2 eps < 1 - g
    if -g > lo: lo, lo_m = -g, m
    if 1 - g < hi: hi, hi_m = 1 - g, m
print("\n=== admissible band for sqrt2*eps (from m=0..%d) ===" % NMAX)
print(f"  sqrt2*eps in [ {lo:.10f} , {hi:.10f} )   (binding m_lo={lo_m}, m_hi={hi_m})")
print(f"  => eps in [ {lo/ sqrt2:.12f} , {hi/sqrt2:.12f} )")
print(f"  compare stated xi1={Decimal(c1)/2*S2-d1:.12f}  xi2={Decimal(c2)/2*S2-d2:.12f}")
print(f"  1/2 = {HALF}  ; sqrt2/2 = {S2/2:.12f}")
