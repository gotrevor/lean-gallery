#!/usr/bin/env python3
"""Cor 3.5 — confirm w(m)=r*alpha (Beatty real) and the two-step crux for w=r*alpha.

Tracked number w(m) = r*(1+1/√2) [case1] or r*(1+√2) [case2], m=floor(w).
Closed form claim: su(2j) = floor(w * 2^j).  Two-step GP crux needed:
   floor(√2(floor(√2(floor(w2^j)+1/2))+1/2)) = floor(w 2^{j+1}).
Question: does this crux hold for ALL w (no Diophantine condition), or only for w=r*alpha?
"""
from decimal import Decimal, getcontext
getcontext().prec = 300
def sqrt2():
    x = Decimal(1.5)
    for _ in range(600): x=(x+2/x)/2
    return x
S2 = sqrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))

def two_step(V):  # V integer
    V1 = fl(S2*(Decimal(V)+Decimal(1)/2))
    return fl(S2*(Decimal(V1)+Decimal(1)/2))

def crux_holds_for(w, J=120):
    for j in range(0, J):
        V = fl(w*Decimal(2)**j)
        if two_step(V) != fl(w*Decimal(2)**(j+1)):
            return False, j
    return True, None

# Test w = r*alpha (Beatty reals)
alpha1 = 1 + 1/S2
alpha2 = 1 + S2
print("=== two-step crux for w = r*alpha (Beatty reals) ===")
for r in range(1, 12):
    for (nm, a) in [("1+1/√2", alpha1), ("1+√2", alpha2)]:
        w = Decimal(r)*a
        ok, jf = crux_holds_for(w)
        print(f"r={r} a={nm}: w={float(w):.6f} m=floor(w)={fl(w)}  crux_all_j={ok}" + (f" (fails j={jf})" if not ok else ""))

print()
print("=== two-step crux for ARBITRARY w (does it fail?) ===")
for nm, w in [("pi", Decimal('3.14159265358979')), ("sqrt3", Decimal(3).sqrt()),
              ("2.7", Decimal('2.7')), ("e", Decimal('2.71828182845905')),
              ("5.3", Decimal('5.3')), ("1.9", Decimal('1.9'))]:
    ok, jf = crux_holds_for(w)
    print(f"w={nm} ({float(w):.4f}): crux_all_j={ok}" + (f" (fails j={jf})" if not ok else ""))

print()
print("=== confirm su(2j)=floor(w 2^j) for the actual recurrence, w=r*alpha ===")
def orbit(m, N=130):
    u=[None, Decimal(m)]
    for n in range(1,2*N+4):
        u.append(Decimal(fl(S2*(u[n]+Decimal(1)/2))))
    return u
allok=True
for r in range(1,10):
    for (nm,a) in [("1+1/√2",alpha1),("1+√2",alpha2)]:
        w=Decimal(r)*a; m=fl(w)
        u=orbit(m,120)
        # python u[2j+1] = su(2j) in 0-indexed Lean (u_{2j+1}); check == floor(w 2^j)
        ok=all(int(u[2*j+1])==fl(w*Decimal(2)**j) for j in range(0,115))
        allok = allok and ok
print("su(2j)=floor(w 2^j) for all tested r,alpha,j:", allok)
