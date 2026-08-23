#!/usr/bin/env python3
"""St06 Cor 3.5 — reverse-engineer the exact statement numerically.

The GP recurrence (a=b=√2, ε=½) started at u(1)=m:
    u(n+1) = floor(√2 (u(n) + 1/2)).
Claim: u read as digit-differences reproduces the binary digits of a w=w(m)
determined by m via Beatty, with an index shift M=floor(log2 w).

Strategy: be empirical. Run the orbit, recover w as lim u(2j+1)/2^j, then check
which binary digits the differences give and at what offset.
"""
from decimal import Decimal, getcontext
getcontext().prec = 200

def sqrt2():
    x = Decimal(1.5)
    for _ in range(400):
        x = (x + 2 / x) / 2
    return x
S2 = sqrt2()

def fl(x):
    return int(x.to_integral_value(rounding='ROUND_FLOOR'))

def orbit(m, N=60):
    u = [None, Decimal(m)]
    for n in range(1, 2*N+4):
        u.append(Decimal(fl(S2*(u[n] + Decimal(1)/2))))
    return u

def recover_w(m, N=60):
    u = orbit(m, N)
    # u(2j+1) ~ w * 2^j  (for the right normalization). Take large j.
    j = N
    return (u[2*j+1]) / (Decimal(2)**j)

def bindig(w, n):  # n-th binary digit with d_1 = integer digit of w (d_n=floor(w 2^{n-1})-2 floor(w 2^{n-2}))
    return fl(w*Decimal(2)**(n-1)) - 2*fl(w*Decimal(2)**(n-2))

print("m :  recovered w = lim u(2j+1)/2^j   |  log2 w, M=floor(log2 w)")
import math
for m in range(1, 13):
    w = recover_w(m)
    wf = float(w)
    M = math.floor(math.log2(wf)) if wf>0 else None
    print(f"{m:2d} : {wf:.10f}   M={M}")

print()
print("Beatty correspondence: 1+1/√2 =", float(1+1/S2), " 1+√2 =", float(1+S2))
for r in range(1, 9):
    m1 = fl(Decimal(r)*(1+1/S2))   # first case
    m2 = fl(Decimal(r)*(1+S2))     # second case
    w1 = Decimal(r)*S2 - 2*fl(Decimal(r)/S2)
    w2 = 2*Decimal(r)*S2 - 2*fl(Decimal(r)*S2)
    print(f"r={r}: case1 m=floor(r(1+1/√2))={m1}, w1=r√2-2floor(r/√2)={float(w1):.6f} | "
          f"case2 m=floor(r(1+√2))={m2}, w2=2r√2-2floor(r√2)={float(w2):.6f}")

print()
print("=== Test closed form u(2j+1) = floor(W 2^j), u(2j) = floor(W 2^j / ? ) for W=recovered w ===")
for m in range(1, 11):
    u = orbit(m, 70)
    # high-j W from a very large index for accuracy
    jbig = 65
    W = u[2*jbig+1] / Decimal(2)**jbig
    # check u(2j+1) == floor(W 2^j) for a range of j
    ok_odd = all(int(u[2*j+1]) == fl(W*Decimal(2)**j) for j in range(1, 60))
    # check digit-diff identity: u(2j+1)-2u(2j-1) == jth binary digit of W
    ok_dig = all(int(u[2*j+1]-2*u[2*j-1]) == bindig(W, j) for j in range(2, 55))
    # also even index: u(2j) =? floor(W 2^j /2)+? ; try floor((W/2) 2^j)= floor(W 2^{j-1})
    ok_even = all(int(u[2*j]) == fl(W*Decimal(2)**(j-1)) for j in range(1, 55))
    print(f"m={m:2d} W={float(W):.8f}  u(2j+1)=floor(W2^j)?{ok_odd}  even u(2j)=floor(W2^(j-1))?{ok_even}  digdiff?{ok_dig}")
