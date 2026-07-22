# WARNING: SWAPPED RECURRENCE — NOT Stoll's Theorem 3.4.  This script puts eps on the
# b-step (n even) and 1/2 on the a-step (n odd), which is Theorem 3.3's placement.  Stoll's
# actual Theorem 3.4 has eps on the a-step; see st06_thm34_HOSTCHECK.py for the CORRECT
# (paper) recurrence and the full-interval confirmation that backs the Lean theorems
# st06_thm34_{astep,closed,digits,isBit}_eps in src/.../St06Thm34.lean.  Kept for the record.
from decimal import Decimal, getcontext
import random
getcontext().prec=80
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def run(m,l,k,eps,t,N=24):
    a=Decimal(2*k+1)+Decimal(2*l)/(t+2*m); b=Decimal(2)/a
    u=[None,Decimal(m)]
    for n in range(1,2*N+4):
        if n%2==1: u.append(Decimal(fl(a*(u[n]+Decimal(1)/2))))
        else: u.append(Decimal(fl(b*(u[n]+eps))))
    return u
def dig(t,n): return fl(t*Decimal(2)**(n-1))-2*fl(t*Decimal(2)**(n-2))
random.seed(5)
bad=0;tested=0
for _ in range(4000):
    t=Decimal(1)+Decimal(random.random())*Decimal('0.999999')
    m=random.randint(1,7); l=random.randint(1,m); k=random.randint(0,5)
    u=run(m,l,k,Decimal(1)/2,t)
    # conclusion (1): odd closed form / digit
    c1=all(int(u[2*n+1]-2*u[2*n-1])==dig(t,n) for n in range(1,20))
    # even closed form E'=(2k+1)A+k+l*2^j  (su(2j+1)=u[2j+2])
    cE=all(int(u[2*j+2])==(2*k+1)*(m*2**j+fl(t*Decimal(2)**(j-1)))+k+l*2**j for j in range(0,20))
    tested+=1
    if not(c1 and cE): bad+=1; 
    if not(c1 and cE) and bad<=5: print("BAD",float(t),m,l,k,c1,cE)
print(f"thm3.4 eps=1/2 universal: tested={tested} bad={bad}")
