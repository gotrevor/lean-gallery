#!/usr/bin/env python3
"""Verify Stoll St06 (Acta Arith 125, 2006) Example 1.1: a recurrence with pi and e
(negative coefficients) whose digit differences give the TERNARY digits of e.

  v_1 = 3
  v_{n+1} = floor( -3/(e+9) * (v_n + pi) )   if n odd
          = floor( -(e+9) * (v_n + 1) )      if n even
  claim:  v_{2n+1} - 3*v_{2n-1}  =  n-th ternary digit of e = (2.201101121...)_3

High-precision (mpmath if available, else Decimal) so floors are exact enough.
"""
from decimal import Decimal, getcontext
getcontext().prec = 200

# high-precision e and pi via mpmath if present, else Decimal series
try:
    from mpmath import mp, mpf, e as MPE, pi as MPPI, floor as mpfloor
    mp.dps = 120
    E = mpf(MPE); PI = mpf(MPPI)
    def fl(x): return int(mpfloor(x))
    HP = "mpmath"
except Exception:
    # Decimal fallback
    getcontext().prec = 200
    # e via series, pi via Machin
    def _e():
        s = Decimal(0); term = Decimal(1); n = 0
        while term > Decimal(10) ** -180:
            s += term; n += 1; term /= n
        return s
    def _atan_inv(x):  # arctan(1/x)
        x = Decimal(x); s = Decimal(0); k = 0; term = 1/x; xx = x*x; sign = 1
        t = 1/x
        while abs(t) > Decimal(10) ** -180:
            s += sign * t / (2*k+1); k += 1; t /= xx; sign = -sign
        return s
    PI = 16*_atan_inv(5) - 4*_atan_inv(239)
    E = _e()
    def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
    HP = "decimal"

print(f"[precision backend: {HP}]")
print(f"e  = {str(E)[:40]}...")
print(f"pi = {str(PI)[:40]}...\n")

A = -3 / (E + 9)      # coefficient for n odd
B = -(E + 9)          # coefficient for n even

N = 40
v = [None, 3]  # 1-indexed, v_1 = 3
for n in range(1, 2*N + 3):
    if n % 2 == 1:
        v.append(fl(A * (v[n] + PI)))
    else:
        v.append(fl(B * (v[n] + 1)))

# recurrence digits
rec = [v[2*n+1] - 3*v[2*n-1] for n in range(1, N+1)]

# independent ternary digits of e: e = 2.(d1 d2 d3...)_3 ; d_n = floor(e*3^n) mod 3
# (with the integer part '2' as d_0; the recurrence's d_n for n>=1 are the fractional ternary digits,
#  but Stoll indexes so d_1 = integer digit 2. We compare both alignments and report.)
def tern_digit_from0(k):   # k-th digit, k=0 -> integer part
    return fl(E * (Decimal(3) if HP=="decimal" else 3) ** k) % 3 if False else fl(E * (3**k)) % 3

ref0 = [fl(E * (3**k)) % 3 for k in range(0, N)]   # d_0 (=2), d_1, d_2, ...
print("recurrence v_{2n+1}-3v_{2n-1}, n=1..20:")
print(" ", rec[:20])
print("ternary digits of e (d_0=int part), k=0..19:")
print(" ", ref0[:20])

match0 = all(rec[i] == ref0[i] for i in range(N))      # aligned: rec[n] == d_{n-1}? test both
match_shift = all(rec[i] == ref0[i] for i in range(N))
# try alignment rec[n] (n=1..) == ref0[n-1] (d_0,d_1,...)
aligned = all(rec[n-1] == ref0[n-1] for n in range(1, N+1))
print(f"\ne in base 3 = 2.201101121...  -> digits [2,2,0,1,1,0,1,1,2,1,...]")
print(f"recurrence reproduces e's ternary digits (d_1=integer '2'): {aligned}")
print(f"first mismatch: ", next((n for n in range(1,N+1) if rec[n-1]!=ref0[n-1]), 'NONE'))
