"""Numerically verify St05 Theorem 1.2 (binary, two families, parameter j) closed forms +
digit extraction, BEFORE formalizing (Stoll's printed forms have been wrong — pair 5)."""
import math, decimal
from fractions import Fraction
decimal.getcontext().prec = 200
D = decimal.Decimal

def fl(x): return int(x.to_integral_value(rounding=decimal.ROUND_FLOOR))

def mantissa(w, g=2):
    m = math.floor(math.log(float(w))/math.log(g))
    t = w/(D(g)**m)
    while t < 1: m -= 1; t = w/(D(g)**m)
    while t >= g: m += 1; t = w/(D(g)**m)
    return t

def run(case, w, j, eps, N=45):
    w = D(w); g = 2; t = mantissa(w, g); eps = D(eps.numerator)/D(eps.denominator)
    if case == 'I':
        a = 2*(j - 1/(t+2))
    else:  # II
        a = 2*j - t/(t+2)
    b = D(2)/a
    half = D(1)/2
    # recurrence: u1=1; u_{n+1} = floor(a(u_n+1/2)) if n odd, floor(b(u_n+eps)) if n even
    u = {1:1}; n = 1
    while n < 2*N+3:
        if n % 2 == 1: u[n+1] = fl(a*(D(u[n])+half))
        else:          u[n+1] = fl(b*(D(u[n])+eps))
        n += 1
    ok_cf = True
    for k in range(1, N):
        u2k1 = 2**k + fl(t*(D(2)**(k-1)))                 # same both cases
        if case == 'I':
            u2k = 2**(k-1) + fl(t*(D(2)**(k-1))) + (j-1)*(2**k + 2*fl(t*(D(2)**(k-2))) + 1)
        else:
            u2k = 2**k + fl(t*(D(2)**(k-2))) + (j-1)*(2**k + 2*fl(t*(D(2)**(k-2))) + 1)
        if u.get(2*k) != u2k: ok_cf=False; print(f"  CASE {case} u_{2*k}: actual={u.get(2*k)} cf={u2k} MISMATCH"); break
        if u.get(2*k+1) != u2k1: ok_cf=False; print(f"  CASE {case} u_{2*k+1}: actual={u.get(2*k+1)} cf={u2k1} MISMATCH"); break
    ok_dig = True
    for n in range(1, N):
        d = u[2*n+1] - 2*u[2*n-1]
        dn = fl(t*(D(2)**(n-1))) - 2*fl(t*(D(2)**(n-2)))
        if d != dn or not (0 <= d < 2): ok_dig=False; print(f"  CASE {case} n={n} d={d} dn={dn} MISMATCH"); break
    print(f"CASE {case} w={float(w):.6f} j={j} eps={eps} t={float(t):.6f} a={float(a):.6f}: cf={'OK' if ok_cf else 'FAIL'} dig={'OK' if ok_dig else 'FAIL'}")

W2 = '1.4142135623730950488016887242096980785696718753769480731766797379907'
W3 = '1.7320508075688772935274463415058723669428052538103806280558069794519'
PI = '3.1415926535897932384626433832795028841971693993751058209749445923078'
# Case II: eps = 1/2 forced; j = 1,2,3,4
for j in (1,2,3,4):
    run('II', W2, j, Fraction(1,2)); run('II', W3, j, Fraction(1,2)); run('II', PI, j, Fraction(1,2))
# Case I: 1/3 <= eps < 2/3 ; test endpoints and interior; j=1,2,3
for j in (1,2,3):
    for eps in (Fraction(1,3), Fraction(1,2), Fraction(599,900)):  # 599/900 ~ just under 2/3
        run('I', W2, j, eps); run('I', PI, j, eps)
