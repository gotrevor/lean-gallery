#!/usr/bin/env python3
"""Cor 3.5 — confirm the EXACT closed forms to formalize (generalized gp_pair, factor r)."""
from decimal import Decimal, getcontext
getcontext().prec = 400
def sqrt2():
    x=Decimal(1.5)
    for _ in range(800): x=(x+2/x)/2
    return x
S2=sqrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def orbit(m,N=200):
    u=[None,Decimal(m)]
    for n in range(1,2*N+5): u.append(Decimal(fl(S2*(u[n]+Decimal(1)/2))))
    return u
# Lean su(n)=u_{n+1}: su0=u[1]=m. So su(k)=u[k+1].
def su(u,k): return int(u[k+1])
def f2(e): return fl(S2*Decimal(e))  # floor(sqrt2 * e)

def binDigit(t,n):  # repo: floor(t 2^n)-2 floor(t 2^{n-1})
    return fl(t*Decimal(2)**n)-2*fl(t*Decimal(2)**(n-1))

J=180
print("CASE 1: start m=floor(r(1+1/√2))=r+floor(r√2/2). Closed: su(2j+1)=floor(r√2 2^j)+r2^j, su(2j+2)=floor(r√2 2^j)+r2^{j+1}")
allok=True
for r in range(1,14):
    m=r+fl(Decimal(r)*S2/2)
    assert m==fl(Decimal(r)*(1+1/S2)), (r,m)
    u=orbit(m,J+5)
    c_odd =all(su(u,2*j+1)==fl(Decimal(r)*S2*Decimal(2)**j)+r*2**j     for j in range(0,J))
    c_even=all(su(u,2*j+2)==fl(Decimal(r)*S2*Decimal(2)**j)+r*2**(j+1) for j in range(0,J))
    c_base= su(u,0)==m
    c_dig =all(su(u,2*j+1)-2*su(u,2*j-1)==binDigit(Decimal(r)*S2,j) for j in range(1,J))
    allok = allok and c_odd and c_even and c_base and c_dig
print("  all case1 (odd,even closed + digit=binDigit(r√2)):", allok)

print("CASE 2: start m=floor(r(1+√2))=r+floor(r√2). Closed: su(2j)=floor(r√2 2^j)+r2^j, su(2j+1)=floor(r√2 2^j)+r2^{j+1}")
allok2=True
for r in range(1,14):
    m=r+fl(Decimal(r)*S2)
    assert m==fl(Decimal(r)*(1+S2)),(r,m)
    u=orbit(m,J+5)
    c_ev=all(su(u,2*j)  ==fl(Decimal(r)*S2*Decimal(2)**j)+r*2**j     for j in range(0,J))
    c_od=all(su(u,2*j+1)==fl(Decimal(r)*S2*Decimal(2)**j)+r*2**(j+1) for j in range(0,J))
    c_dig=all(su(u,2*j+1)-2*su(u,2*j-1)==binDigit(Decimal(r)*S2,j) for j in range(1,J))
    allok2=allok2 and c_ev and c_od and c_dig
print("  all case2 (closed + digit=binDigit(r√2)):", allok2)

# base-case facts to prove:
print()
print("Base facts: su(1) for case1 = floor(sqrt2(m+1/2)) =? r+floor(r√2):")
for r in range(1,8):
    m=r+fl(Decimal(r)*S2/2)
    print(f"  r={r}: floor(√2(m+1/2))={fl(S2*(Decimal(m)+Decimal(1)/2))}, r+floor(r√2)={r+fl(Decimal(r)*S2)}, floor(r√2 2^0)+r2^0={fl(Decimal(r)*S2)+r}")
