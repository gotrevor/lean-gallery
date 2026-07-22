from decimal import Decimal, getcontext
getcontext().prec=300
def cbrt2():
    x=Decimal(1.26)
    for _ in range(500): x=x-(x**3-2)/(3*x*x)
    return x
A=cbrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def orbit(m,cs,N=200):
    u=[Decimal(m)]
    for n in range(3*N+9): u.append(Decimal(fl(A*(u[-1]+cs[n%3]))))
    return u
cs=(Decimal(1)/6,Decimal(1)/3,Decimal(4)/3)
u=orbit(1,cs,180)
for r in range(3):
    firstbad=None
    for j in range(1,178):
        d=int(u[3*j+r])-2*int(u[3*(j-1)+r])
        if d not in (0,1): firstbad=(j,d); break
    print(f"phase {r}: first non-bit at j={firstbad}")
