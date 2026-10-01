#!/usr/bin/env python3
"""Verify Stoll pair-5 (i=5, t5=sqrt2) claims for erdos-482 online request.
EXACT integer arithmetic via math.isqrt (no float error), Decimal for diagnostics.

Key identities used:
  floor(x*sqrt2)        = isqrt(2*x*x)            for integer x>=0
                        = -(isqrt(2*x*x)+1)       for integer x<0   (2x^2 never a square, x!=0)
  floor(sqrt2*2^k)      = isqrt(2**(2k+1))
  floor(sqrt2*(v+1/2))  = isqrt(2*(2v+1)**2)//2
  eps = (c/2)*sqrt2 - d (c,d in Z):
     floor(sqrt2*(v+eps)) = floor(sqrt2*v + c - d*sqrt2) = c + floor((v-d)*sqrt2)
"""
from math import isqrt
from decimal import Decimal, getcontext
getcontext().prec = 120
S2 = Decimal(2).sqrt()
HALF = Decimal(1) / 2

def floor_x_sqrt2(x: int) -> int:
    if x >= 0:
        return isqrt(2 * x * x)
    return -(isqrt(2 * x * x) + 1)

def floor_sqrt2_pow(k: int) -> int:
    # floor(sqrt2 * 2^k), k>=0
    return isqrt(2 ** (2 * k + 1))

def step_half(v: int) -> int:
    return isqrt(2 * (2 * v + 1) ** 2) // 2

def step_eps(v: int, c: int, d: int) -> int:
    # eps = (c/2)sqrt2 - d ; floor(sqrt2*(v+eps)) = c + floor((v-d)*sqrt2)
    return c + floor_x_sqrt2(v - d)

def vseq(c: int, d: int, n: int):
    """Def 3.1 with eps=(c/2)sqrt2-d. v1=1; m odd -> eps-step, m even -> half-step."""
    v = [None, 1]  # 1-indexed
    for m in range(1, n):
        v.append(step_eps(v[m], c, d) if m % 2 == 1 else step_half(v[m]))
    return v

def vseq_half(n: int):
    """eps = 1/2 exactly (original Graham-Pollak): every step is a half-step."""
    v = [None, 1]
    for m in range(1, n):
        v.append(step_half(v[m]))
    return v

def sqrt2_bit(k: int) -> int:  # k=0 -> integer bit '1'; k>=1 fractional bits
    return floor_sqrt2_pow(k) % 2

print("sqrt2 binary bits k=0..14:", [sqrt2_bit(k) for k in range(15)])
print("  (sqrt2 = 1.0110101000001...)\n")

# === eps = 1/2: the printed-vs-corrected formula showdown ===
v = vseq_half(40)
print("=== eps=1/2: v_1..v_16 ===")
print([v[n] for n in range(1, 17)])

print(f"\n{'k':>2} | {'actual v_2k':>11} | {'PRINTED ⌊t2^(k-2)⌋+2^(k-2)':>28} | {'CORRECTED ⌊t2^(k-1)⌋+2^(k-1)':>30}")
for k in range(1, 9):
    actual = v[2 * k]
    # PRINTED: for k>=2 these are integers; k=1 gives 1/2 (non-integer!) -> compute as Decimal
    printed = (S2 * Decimal(2) ** (k - 2)).to_integral_value(rounding='ROUND_FLOOR') + Decimal(2) ** (k - 2)
    corrected = floor_sqrt2_pow(k - 1) + 2 ** (k - 1)
    pmark = 'OK' if printed == actual else 'WRONG'
    cmark = 'OK' if corrected == actual else 'WRONG'
    print(f"{k:>2} | {actual:>11} | {str(printed):>20} {pmark:>7} | {corrected:>22} {cmark:>7}")

print(f"\n{'k':>2} | {'actual v_2k+1':>13} | {'PRINTED ⌊t2^(k-1)⌋+2^k':>24}")
for k in range(1, 9):
    actual = v[2 * k + 1]
    printed = floor_sqrt2_pow(k - 1) + 2 ** k
    print(f"{k:>2} | {actual:>13} | {printed:>16} {'OK' if printed==actual else 'WRONG':>6}")

# === digit extraction (corrected) ===
print("\n=== d_n = v_{2n+1} - 2 v_{2n-1}  vs sqrt2 bits (eps=1/2) ===")
allok = True
for n in range(1, 13):
    d = v[2 * n + 1] - 2 * v[2 * n - 1]
    bit = sqrt2_bit(n - 1)
    m = 'OK' if d == bit else 'MISMATCH'
    allok &= (d == bit)
    print(f"  n={n:>2}: d_n={d}  sqrt2_bit({n-1})={bit}  {m}")
print("alignment:", "ALL OK (d_n is the (n-1)-th bit; d_1=integer '1')" if allok else "PROBLEM")

# === pair-5 interval ===
c1, d1 = 309, 218
c2, d2 = 1296121037, 916495974
xi1 = Decimal(c1) / 2 * S2 - d1
xi2 = Decimal(c2) / 2 * S2 - d2
print(f"\n=== pair-5 interval [xi1, xi2) ===")
print(f"  xi1 = 309/2 sqrt2 - 218                  = {xi1:.12f}")
print(f"  xi2 = 1296121037/2 sqrt2 - 916495974     = {xi2:.12f}")
print(f"  width = {xi2 - xi1:.10f} ;  1/2 interior: {xi1 <= HALF < xi2}")

# === does the CORRECTED formula reproduce the exact recurrence for all k? ===
def first_fail(c, d, kmax):
    v = vseq(c, d, 2 * kmax + 5)
    for k in range(1, kmax + 1):
        we = floor_sqrt2_pow(k - 1) + 2 ** (k - 1)
        wo = floor_sqrt2_pow(k - 1) + 2 ** k
        if v[2 * k] != we or v[2 * k + 1] != wo:
            return k
    return None

KMAX = 400
print(f"\n=== exact-recurrence check of corrected formula, k=1..{KMAX} ===")
tests = [
    ("xi1 endpoint (included)", c1, d1),
    ("xi2 endpoint (EXCLUDED)", c2, d2),
]
for label, c, d in tests:
    print(f"  eps={label:28} first-fail k = {first_fail(c, d, KMAX) or f'NONE up to {KMAX}'}")
# eps=1/2 separately (every step half)
vh = vseq_half(2 * KMAX + 5)
ff = None
for k in range(1, KMAX + 1):
    if vh[2 * k] != floor_sqrt2_pow(k - 1) + 2 ** (k - 1) or vh[2 * k + 1] != floor_sqrt2_pow(k - 1) + 2 ** k:
        ff = k; break
print(f"  eps={'1/2 (GP)':28} first-fail k = {ff or f'NONE up to {KMAX}'}")

# === the eps-step bracket margin (***): 0 <= {x} - sqrt2*{x/2} + sqrt2*eps < 1, x=sqrt2*2^k ===
def fracD(x: Decimal) -> Decimal:
    return x - x.to_integral_value(rounding='ROUND_FLOOR')

print(f"\n=== eps-step bracket B_k = {{x}} - sqrt2*{{x/2}} + sqrt2*eps, x=sqrt2*2^k (k=0..200) ===")
print("    report min(B_k) and min(1-B_k) = margins to the [0,1) walls, per eps")
for label, eps in [("xi1", xi1), ("1/2", HALF), ("xi2 (excl)", xi2),
                   ("xi2 + 1e-7 (outside)", xi2 + Decimal('1e-7'))]:
    lo = Decimal(10); hi = Decimal(10); arg_lo = arg_hi = -1
    for k in range(0, 201):
        x = S2 * (Decimal(2) ** k)
        B = fracD(x) - S2 * fracD(x / 2) + S2 * eps
        if B < lo: lo, arg_lo = B, k
        if (1 - B) < hi: hi, arg_hi = 1 - B, k
    status = "OK (stays in [0,1))" if lo >= 0 and hi > 0 else ">>> LEAVES [0,1) <<<"
    print(f"  eps={label:22} min B={lo:+.3e}@k={arg_lo:<4} min(1-B)={hi:+.3e}@k={arg_hi:<4} {status}")

# === closest approach of {sqrt2*2^m} to 1/2 (the Diophantine binding) ===
print("\n=== closest {sqrt2*2^m} to 1/2, m=0..210 (drives the interval endpoints) ===")
rows = []
for m in range(0, 211):
    f = fracD(S2 * (Decimal(2) ** m))
    rows.append((abs(f - HALF), m, f))
rows.sort()
for dist, m, f in rows[:10]:
    side = "below" if f < HALF else "above"
    print(f"  m={m:>3}  {{sqrt2*2^m}}={f:.12f} ({side} 1/2)  |.-1/2|={dist:.3e}")
