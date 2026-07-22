from decimal import Decimal, getcontext
getcontext().prec=200
def sqrt2():
    x=Decimal(1.5)
    for _ in range(400): x=(x+2/x)/2
    return x
S2=sqrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def run(m,l,k,eps,t,N):
    a=Decimal(2*k+1)+Decimal(2*l)/(t+2*m); b=Decimal(2)/a
    u=[None,Decimal(m)]
    for n in range(1,2*N+4):
        if n%2==1: u.append(Decimal(fl(a*(u[n]+Decimal(1)/2))))
        else: u.append(Decimal(fl(b*(u[n]+eps))))
    return u
def dig(t,n): return fl(t*Decimal(2)**(n-1))-2*fl(t*Decimal(2)**(n-2))
t=S2
m,l,k=1,1,0
for Nmax in [10,20,40,80,160]:
    lo=None;hi=None;NN=4000
    for i in range(NN+1):
        eps=Decimal(i)/NN
        u=run(m,l,k,eps,t,Nmax+3)
        if all(int(u[2*n+1]-2*u[2*n-1])==dig(t,n) for n in range(1,Nmax)):
            if lo is None: lo=eps
            hi=eps
    print(f"Nmax={Nmax}: c1 eps∈[{float(lo):.5f},{float(hi):.5f}] width={float(hi-lo):.5f}")
