#!/usr/bin/env python3
"""Finer cubic search: 3-phase offsets c0,c1,c2, recurrence u(n+1)=floor(α(u(n)+c_{n mod 3})), α=2^{1/3}.
Check whether u(3j+r)-2u(3(j-1)+r) ∈ {0,1} for all j (a bitstream) at some phase r."""
from decimal import Decimal, getcontext
getcontext().prec = 150
def cbrt2():
    x=Decimal(1.26)
    for _ in range(300): x=x-(x**3-2)/(3*x*x)
    return x
A=cbrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def orbit(m, cs, N=70):
    u=[Decimal(m)]
    for n in range(3*N+6):
        u.append(Decimal(fl(A*(u[-1]+cs[n%3]))))
    return u
def bitphases(m, cs, N=60):
    u=orbit(m,cs,N)
    good=[]
    for r in range(3):
        ok=all((int(u[3*j+r])-2*int(u[3*(j-1)+r])) in (0,1) for j in range(2,N))
        if ok: good.append(r)
    return good
# search c_i over k/6 grid
from itertools import product
hits=0
for c0,c1,c2 in product([Decimal(k)/6 for k in range(0,13)], repeat=3):
    g=bitphases(1,(c0,c1,c2))
    if g:
        print(f"c=({float(c0):.3f},{float(c1):.3f},{float(c2):.3f}) bitstream phases {g}")
        hits+=1
        if hits>15: break
if hits==0:
    print("No clean bitstream found over the k/6 grid (3 phases, m=1).")
    # report the BEST: max consecutive bits before a non-bit appears
    best=0;bestc=None
    for c0,c1,c2 in product([Decimal(k)/6 for k in range(0,13)], repeat=3):
        u=orbit(1,(c0,c1,c2),60)
        for r in range(3):
            run=0
            for j in range(2,60):
                d=int(u[3*j+r])-2*int(u[3*(j-1)+r])
                if d in (0,1): run+=1
                else: break
            if run>best: best=run;bestc=(float(c0),float(c1),float(c2),r)
    print(f"best run of consecutive bits: {best} at c,phase={bestc}")
