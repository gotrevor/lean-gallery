#!/usr/bin/env python3
# HOST online-request check (2026-06-13): verify Thm 3.4 with the CORRECT recurrence
# from the St06 PDF (pages 93-94): n ODD -> floor(a*(u+eps)); n EVEN -> floor(b*(u+1/2)).
# a = 2k+1 + 2l/(t+2m), b = 2/a.   (NOTE: this is the OPPOSITE eps/half placement
# from the box's st06_thm34_verify.py, which used the Thm 3.3 shape.)
from decimal import Decimal, getcontext
getcontext().prec = 220

def sqrt2():
    x = Decimal(1.5)
    for _ in range(500):
        x = (x + 2 / x) / 2
    return x
S2 = sqrt2()

def fl(x):
    return int(x.to_integral_value(rounding='ROUND_FLOOR'))

def run(m, l, k, eps, t, N, swapped=False):
    a = Decimal(2 * k + 1) + Decimal(2 * l) / (t + 2 * m)
    b = Decimal(2) / a
    u = [None, Decimal(m)]
    for n in range(1, 2 * N + 4):
        if not swapped:
            # PAPER Thm 3.4: n odd -> a,eps ; n even -> b,1/2
            if n % 2 == 1:
                u.append(Decimal(fl(a * (u[n] + eps))))
            else:
                u.append(Decimal(fl(b * (u[n] + Decimal(1) / 2))))
        else:
            # box's swapped version (Thm 3.3 placement): n odd -> a,1/2 ; n even -> b,eps
            if n % 2 == 1:
                u.append(Decimal(fl(a * (u[n] + Decimal(1) / 2))))
            else:
                u.append(Decimal(fl(b * (u[n] + eps))))
    return u

def dig(t, n):
    return fl(t * Decimal(2) ** (n - 1)) - 2 * fl(t * Decimal(2) ** (n - 2))

def stoll_interval(m, l, k):
    # m>=1 symmetric interval [1/2 - r, 1/2 + r)
    r = (Decimal(m - l) + Decimal(1) / 2) / (Decimal((2 * k + 1) * (2 * m + 1)) + 2 * l)
    return (Decimal(1) / 2 - r, Decimal(1) / 2 + r)

def scan(m, l, k, t, Nmax, swapped=False, NN=8000):
    lo = hi = None
    for i in range(NN + 1):
        eps = Decimal(i) / NN
        u = run(m, l, k, eps, t, Nmax + 3, swapped=swapped)
        if all(int(u[2 * n + 1] - 2 * u[2 * n - 1]) == dig(t, n) for n in range(1, Nmax)):
            if lo is None:
                lo = eps
            hi = eps
    return lo, hi

t = S2
print("w = sqrt(2), t =", float(t))
for (m, l, k) in [(1, 1, 0), (2, 1, 0), (2, 2, 0), (2, 1, 1), (3, 2, 1), (4, 3, 2)]:
    plo, phi = stoll_interval(m, l, k)
    print(f"\n(m,l,k)=({m},{l},{k})  Stoll printed interval = [{float(plo):.5f}, {float(phi):.5f})")
    for Nmax in [20, 40, 80]:
        lo, hi = scan(m, l, k, t, Nmax, swapped=False)
        lo_s = f"{float(lo):.5f}" if lo is not None else "none"
        hi_s = f"{float(hi):.5f}" if hi is not None else "none"
        print(f"   PAPER recurrence  Nmax={Nmax}: digits-correct eps in [{lo_s}, {hi_s}]")
    # show the box's swapped version for contrast at Nmax=40
    blo, bhi = scan(m, l, k, t, 40, swapped=True)
    blo_s = f"{float(blo):.5f}" if blo is not None else "none"
    bhi_s = f"{float(bhi):.5f}" if bhi is not None else "none"
    print(f"   box SWAPPED recur Nmax=40: digits-correct eps in [{blo_s}, {bhi_s}]")
