#!/usr/bin/env python3
"""Verify Stoll St06 (Acta Arith 125, 2006) Theorem 3.3 — the binary (g=2) family.
NOT covered by Theorem 3.1 (which excludes g=2).  De-risks Tier 3 before formalizing.

Setup (m ≥ 1 branch):  t = w/2^M ∈ [1,2) the binary mantissa; m,l,k ∈ ℤ, m ∉ {−1,0}, k ≥ 0,
0 ≤ l ≤ m−1.  u₁ = m,
  u_{n+1} = ⌊a (uₙ + ½)⌋   (n odd),
  u_{n+1} = ⌊b (uₙ + ε)⌋   (n even),
with  a = 2k+1 + (t+2l)/(t+2m),  b = 2/a,  and  ½ − (2l+1)/(2(2m+1)) ≤ ε < ½ + (2l+1)/(2(2m+1)).
TWO conclusions:
  (1)  u_{2n+1} − 2 u_{2n−1} = dₙ                       (the n-th binary digit of w)
  (2)  u_{2n+2} − 2 u_{2n}   = d_{n+1} + k(2dₙ − 1)
where dₙ is indexed with d₁ = the INTEGER digit (d_n = ⌊t·2^{n−1}⌋ − 2⌊t·2^{n−2}⌋), the SAME
convention as `General/Cor13e.lean`.  `w=√2,(m,l,k)=(1,0,0),ε=½` → Graham–Pollak.

RESULT (this script): both conclusions hold for w=√2 across many (m,l,k) at ε = ½ and at BOTH
ε-interval endpoints (the interval is independent of k, as Stoll notes).  Verified to n≈28.
"""
from decimal import Decimal, getcontext
getcontext().prec = 120


def sqrt2():
    x = Decimal(1.5)
    for _ in range(200):
        x = (x + 2 / x) / 2
    return x


S2 = sqrt2()


def fl(x):
    return int(x.to_integral_value(rounding='ROUND_FLOOR'))


def test(m, l, k, eps, t, N=28):
    a = Decimal(2 * k + 1) + (t + 2 * l) / (t + 2 * m)
    b = Decimal(2) / a
    u = [None, Decimal(m)]  # 1-indexed, u₁ = m
    for n in range(1, 2 * N + 4):
        if n % 2 == 1:
            u.append(Decimal(fl(a * (u[n] + Decimal(1) / 2))))
        else:
            u.append(Decimal(fl(b * (u[n] + eps))))

    def dig(n):  # d₁ = integer digit
        return fl(t * Decimal(2) ** (n - 1)) - 2 * fl(t * Decimal(2) ** (n - 2))

    c1 = all(int(u[2 * n + 1] - 2 * u[2 * n - 1]) == dig(n) for n in range(1, N))
    c2 = all(int(u[2 * n + 2] - 2 * u[2 * n]) == dig(n + 1) + k * (2 * dig(n) - 1)
             for n in range(1, N))
    return c1, c2


print('Graham–Pollak  (m,l,k)=(1,0,0), ε=½ :', test(1, 0, 0, Decimal(1) / 2, S2))
print()
for (m, l, k) in [(1, 0, 0), (2, 1, 0), (2, 0, 1), (3, 2, 2), (2, 1, 3), (5, 3, 2)]:
    half = Decimal(2 * l + 1) / (2 * (2 * m + 1))  # ε-interval half-width (independent of k)
    mid = test(m, l, k, Decimal(1) / 2, S2)
    lo = test(m, l, k, Decimal(1) / 2 - half, S2)            # inclusive lower endpoint
    hi = test(m, l, k, Decimal(1) / 2 + half - Decimal('1e-9'), S2)  # just below exclusive upper
    print(f'(m,l,k)=({m},{l},{k})  ε∈½±{float(half):.3f} : '
          f'mid={mid} lo={lo} hi={hi}')
