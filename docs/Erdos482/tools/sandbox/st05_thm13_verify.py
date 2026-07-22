import math
from fractions import Fraction

def isqrt_floor_mul(t_num, t_den, k):
    # floor(t * g^... ) handled by caller; here generic floor of real via high-precision
    pass

def verify(w, g, eps, N=60, prec=200):
    # use Fraction-free high precision via Decimal-like: use mpmath if available else float with care
    import decimal
    decimal.getcontext().prec = prec
    D = decimal.Decimal
    w = D(w) if not isinstance(w,(int,)) else D(w)
    g = int(g)
    # mantissa: m = floor(log_g w); t = w/g^m in [1,g)
    m = math.floor(math.log(float(w))/math.log(g))
    # adjust via decimal
    t = w / (D(g)**m)
    while t < 1:
        m -= 1; t = w/(D(g)**m)
    while t >= g:
        m += 1; t = w/(D(g)**m)
    a = D(g)/((D(g)-1)*(t+g))
    b = D(g)/a
    eps = D(eps.numerator)/D(eps.denominator)
    inv = D(1)/(D(g)-1)
    def fl(x): return int(x.to_integral_value(rounding=decimal.ROUND_FLOOR))
    u = {1:1}
    n = 1
    while n < 2*N+3:
        if n % 2 == 1:
            u[n+1] = fl(a*(D(u[n])+eps))
        else:
            u[n+1] = fl(b*(D(u[n])+inv))
        n += 1
    # closed forms
    ok_cf = True
    for k in range(1, N):
        u2k_cf = (g**(k-1) - 1)//(g-1)
        u2k1_cf = g**k + fl(t*(D(g)**(k-1)))
        if u.get(2*k) != u2k_cf: ok_cf=False; print(f"  u_{2*k} actual={u.get(2*k)} cf={u2k_cf} MISMATCH"); break
        if u.get(2*k+1) != u2k1_cf: ok_cf=False; print(f"  u_{2*k+1} actual={u.get(2*k+1)} cf={u2k1_cf} MISMATCH"); break
    # digit extraction
    ok_dig = True
    for n in range(1, N):
        d = u[2*n+1] - g*u[2*n-1]
        # true n-th g-ary digit of w: floor(t*g^(n-1)) - g*floor(t*g^(n-2)); for n=1, floor(t)-g*floor(t/g)
        dn = fl(t*(D(g)**(n-1))) - g*fl(t*(D(g)**(n-2)))
        if d != dn: ok_dig=False; print(f"  n={n} d={d} dn={dn} MISMATCH"); break
        if not (0 <= d < g): ok_dig=False; print(f"  n={n} digit out of range {d}"); break
    print(f"w={w!s:.10}.. g={g} eps={eps} t={t!s:.8}.. a={a!s:.6}.. : closedform={'OK' if ok_cf else 'FAIL'} digits={'OK' if ok_dig else 'FAIL'}")

import decimal
# g=3 w=sqrt2 (Cor 1.2), eps range -1/g <= eps < (g+1)(g-2)/g = 4*1/3=4/3
verify('1.4142135623730950488016887242096980785696718753769480731766797379907', 3, Fraction(0), N=40)
verify('1.4142135623730950488016887242096980785696718753769480731766797379907', 3, Fraction(-1,3), N=40)
verify('1.4142135623730950488016887242096980785696718753769480731766797379907', 3, Fraction(1), N=40)
# g=2 w=sqrt3, eps in [-1/2, 0)
verify('1.7320508075688772935274463415058723669428052538103806280558069794519', 2, Fraction(-1,4), N=40)
verify('1.7320508075688772935274463415058723669428052538103806280558069794519', 2, Fraction(-1,2), N=40)
# g=10 w=pi
verify('3.1415926535897932384626433832795028841971693993751058209749445923078', 10, Fraction(0), N=30)
