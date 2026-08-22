#!/usr/bin/env python3
"""Thm 3.4 general-ε b-step: verify the exact value formula and the lands-iff band.
b(E'+ε) = 2(ms+B) + 1 - frac, frac = (2Nq - 2(t+2m)ε)/Da,
  Nq=(t+2m)/2 + l(1-ts+2B), Da=(2k+1)(t+2m)+2l.
Lands on 2ms+C  iff  -d < frac <= 1-d,  d=C-2B in {0,1}.
"""
from fractions import Fraction as F
import math
def fl(x): return math.floor(x)
def check(t,m,l,k,s,eps):
    B=fl(F(t*s)/2 if isinstance(t,F) else t*s/2)
    C=fl(t*s)
    a=(2*k+1)+F(2*l, (t+2*m)) if isinstance(t,F) else (2*k+1)+2*l/(t+2*m)
    b=2/a if not isinstance(t,F) else F(2,1)/a
    Eprime=(2*k+1)*(m*s+B)+k+l*s
    val=b*(Eprime+eps)
    Nq=(t+2*m)/2+l*(1-t*s+2*B)
    Da=(2*k+1)*(t+2*m)+2*l
    frac=(2*Nq-2*(t+2*m)*eps)/Da
    rhs=2*(m*s+B)+1-frac
    ok_val=abs(float(val)-float(rhs))<1e-9
    d=C-2*B
    lands = (fl(val)==2*m*s+C)
    band = (-d < frac <= 1-d)
    return ok_val, lands, band, d
# random rational t in [1,2)
import random
random.seed(1)
allv=allb=True
for _ in range(2000):
    t=F(random.randint(100,199),100)
    m=random.randint(1,4); l=random.randint(1,m); k=random.randint(0,3)
    s=2**random.randint(0,6)
    eps=F(random.randint(30,70),100)
    okv,lands,band,d=check(t,m,l,k,s,eps)
    allv=allv and okv
    allb=allb and (lands==band)
print("value formula correct (2000 rational trials):",allv)
print("lands-on-2ms+C  iff  -d<frac<=1-d :",allb)
