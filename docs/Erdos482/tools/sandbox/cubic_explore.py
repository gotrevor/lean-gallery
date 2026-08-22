#!/usr/bin/env python3
"""Explore: does a CUBIC self-referential GP-type recurrence read off binary digits?
α = 2^{1/3}, α³ = 2. Try u(n+1) = floor(α(u(n) + c)) for offset c; the THREE-step map
should approximate multiply-by-2 (α³=2), so u(3j+r) ~ floor(β·2^j) for some β, and
u(3(j+1)+r) - 2 u(3j+r) should be a binary digit.
Search for the offset c making this exact (analogue of ε=1/2 for √2)."""
from decimal import Decimal, getcontext
getcontext().prec = 120
def cbrt2():
    x = Decimal(1.26)
    for _ in range(200):
        x = x - (x**3 - 2)/(3*x*x)
    return x
A = cbrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def orbit(m, c, N=90):
    u=[Decimal(m)]
    for _ in range(3*N+6):
        u.append(Decimal(fl(A*(u[-1]+c))))
    return u
# For each candidate offset c, check if u(3j+r)-2u(3(j-1)+r) is in {0,1} (a bit) for all j, some phase r
import itertools
def is_bitstream(m, c, N=80):
    u=orbit(m,c,N)
    res={}
    for r in range(3):
        diffs=[int(u[3*j+r])-2*int(u[3*(j-1)+r]) for j in range(1,N)]
        res[r]=all(d in (0,1) for d in diffs)
    return res, u
# scan offsets c
print("scan offset c for m=1 (which c gives a clean bitstream at some phase?):")
for cnum in range(1,12):
    c=Decimal(cnum)/6
    res,_=is_bitstream(1,c)
    if any(res.values()):
        print(f"  c={cnum}/6={float(c):.4f}: phases with bitstream:", [r for r in res if res[r]])
# also try c that makes α(m+c) land nicely; classic ε=1/2 analogue and c=1/(α-1) etc
for c in [Decimal(1)/2, Decimal(1)/(A-1), Decimal(1)/(A*A-1), Decimal(1)/(A*A+A-... if False else 1)]:
    pass
