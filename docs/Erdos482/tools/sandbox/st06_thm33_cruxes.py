from decimal import Decimal, getcontext
getcontext().prec=120
def sqrt2():
    x=Decimal(1.5)
    for _ in range(200): x=(x+2/x)/2
    return x
S2=sqrt2()
def fl(x): return int(x.to_integral_value(rounding='ROUND_FLOOR'))
def run(m,l,k,eps,t,N=20):
    a=Decimal(2*k+1)+(t+2*l)/(t+2*m); b=Decimal(2)/a
    u=[None,Decimal(m)]
    for n in range(1,2*N+4):
        if n%2==1: u.append(Decimal(fl(a*(u[n]+Decimal(1)/2))))
        else: u.append(Decimal(fl(b*(u[n]+eps))))
    return u,a,b
t=S2
allok=True
for (m,l,k) in [(1,0,0),(2,0,1),(3,2,2),(5,3,2),(2,1,3),(4,1,5),(3,1,0),(7,2,4)]:
  for epslabel,eps in [("half",Decimal(1)/2),
                       ("lo",Decimal(1)/2-Decimal(2*l+1)/(2*(2*m+1))),
                       ("hi",Decimal(1)/2+Decimal(2*l+1)/(2*(2*m+1))-Decimal('1e-15'))]:
    u,a,b=run(m,l,k,eps,t)
    for n in range(0,18):
        A=m*2**n+fl(t*Decimal(2)**(n-1))         # su(2n)
        E=2*k*A+(m+l)*2**n+fl(t*Decimal(2)**n)+k  # su(2n+1) closed
        # check odd closed form
        if int(u[2*n+1])!=A: allok=False; print("ODD fail",m,l,k,n)
        # a-crux: floor(a(A+1/2))=E
        if fl(a*(Decimal(A)+Decimal(1)/2))!=E: allok=False; print("A-CRUX fail",m,l,k,epslabel,n)
        # b-crux: floor(b(E+eps))=A_{n+1}
        Anext=m*2**(n+1)+fl(t*Decimal(2)**n)
        if fl(b*(Decimal(E)+eps))!=Anext: allok=False; print("B-CRUX fail",m,l,k,epslabel,n)
print("ALL CRUXES OK" if allok else "SOME FAILED")
