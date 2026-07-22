#!/usr/bin/env python3
"""For the cubic bitstream c=(1/6,1/3,4/3), phase 0: recover the number whose binary digits it reads."""
from decimal import Decimal, getcontext
getcontext().prec=200
def cbrt2():
    x=Decimal(1.26)
    for _ in range(400): x=x-(x**3-2)/(3*x*x)
    return x
A=cbrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def orbit(m,cs,N=120):
    u=[Decimal(m)]
    for n in range(3*N+9): u.append(Decimal(fl(A*(u[-1]+cs[n%3]))))
    return u
cs=(Decimal(1)/6,Decimal(1)/3,Decimal(4)/3)
u=orbit(1,cs,110)
# phase 0: u[3j] ~ W*2^j ; recover W
for r in range(3):
    j=100
    W=Decimal(u[3*j+r])/Decimal(2)**j
    print(f"phase {r}: W=lim u(3j+{r})/2^j = {float(W):.10f}")
# check u[3j+0] == floor(W*2^j) exactly?
W0=Decimal(u[300])/Decimal(2)**100
def bindig(x,n): return fl(x*Decimal(2)**n)-2*fl(x*Decimal(2)**(n-1))
ok_floor=all(int(u[3*j])==fl(W0*Decimal(2)**j) for j in range(1,100))
ok_dig=all(int(u[3*j])-2*int(u[3*(j-1)])==bindig(W0,j) for j in range(2,100))
print(f"u(3j)=floor(W*2^j)? {ok_floor}; diff=binDigit(W)? {ok_dig}")
print(f"W0 = {float(W0):.12f}")
# is W0 algebraic in A=2^(1/3)? try W0 = p + q*A + s*A^2 small rationals
from fractions import Fraction
# brute: W0 ≈ a + b*A + c*A^2
import itertools
best=None
for a in range(-3,4):
  for b in range(-3,4):
    for c in range(-3,4):
      val=Decimal(a)+Decimal(b)*A+Decimal(c)*A*A
      if abs(val-W0)<Decimal('1e-8'):
        best=(a,b,c)
print("W0 = a + b*2^(1/3) + c*2^(2/3) with (a,b,c)=",best)
