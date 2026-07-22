from decimal import Decimal, getcontext
getcontext().prec=80
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
import itertools, random
random.seed(1)
bad=0; tested=0
for _ in range(200000):
    t=Decimal(1)+Decimal(random.random())*Decimal('0.999999')
    s=random.randint(1,40)
    m=random.randint(1,8); l=random.randint(0,m-1); k=random.randint(0,6)
    B=fl(t*s/2); C=fl(t*s)
    half=Decimal(2*l+1)/(2*(2*m+1))
    # sample eps across the interval incl endpoints
    for eps in [Decimal('0.5')-half, Decimal('0.5')+half-Decimal('1e-20'), Decimal('0.5'),
                Decimal('0.5')-half+Decimal(random.random())*2*half]:
        a=Decimal(2*k+1)+(t+2*l)/(t+2*m); b=Decimal(2)/a
        val=b*(Decimal(2*k*(m*s+B)+(m+l)*s+C+k)+eps)-Decimal(2*m*s+C)
        tested+=1
        if not (Decimal(0)<=val<Decimal(1)):
            bad+=1
            if bad<=8: print(f"BAD t={float(t):.6f} s={s} m={m} l={l} k={k} eps={float(eps):.6f} val={float(val):.8f}")
print(f"tested={tested} bad={bad}")
