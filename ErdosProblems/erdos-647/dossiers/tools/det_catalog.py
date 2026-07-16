from math import gcd
from sympy import factorint
# Master-parameter (N) affine forms: (name, a, b) representing a*N + b
base_forms = [
    ("s1:2520N-1", 2520, -1), ("s2:1260N-1", 1260, -1), ("s3:840N-1", 840, -1),
    ("s4:630N-1", 630, -1), ("s5:504N-1", 504, -1), ("s6:420N-1", 420, -1),
    ("s8:315N-1", 315, -1), ("s9:280N-1", 280, -1), ("s10:252N-1", 252, -1),
    ("s12:210N-1", 210, -1), ("s18:140N-1", 140, -1), ("s20:126N-1", 126, -1),
    ("s24:105N-1", 105, -1),
    ("s14:180N-1", 180, -1), ("s15:168N-1", 168, -1), ("s16:315N-2", 315, -2),
    ("s11:2520N-11", 2520, -11), ("s13:2520N-13", 2520, -13),
]
def classify(forms, label):
    zero, unit, rest = [], [], []
    for i in range(len(forms)):
        for j in range(i+1, len(forms)):
            n1,a,b = forms[i]; n2,c,d = forms[j]
            D = a*d - c*b
            if D == 0: zero.append((n1,n2))
            elif abs(D) == 1: unit.append((n1,n2))
            else:
                f = factorint(abs(D))
                # shared primes must divide D AND not divide gcd-killing: prime q viable only if q does not divide a (else q | b... q|aN+b and q|a -> q|b)
                viable = sorted(q for q in f if a % q != 0 or b % q != 0)
                viable = [q for q in f if (a % q != 0 or abs(b) % q == 0)]  # crude; report all factors
                rest.append((n1,n2,D,dict(f)))
    print(f"### {label}: {len(zero)} zero-det, {len(unit)} unit-det (auto-coprime), {len(rest)} finite-interaction")
    for z in zero: print("  ZERO-DET (proportional!):", z)
    for u in unit: print("  UNIT-DET:", u)
    # summarize prime spectrum
    spec = {}
    for n1,n2,D,f in rest:
        for q in f: spec.setdefault(q, []).append((n1,n2))
    print("  shared-prime spectrum (prime -> #pairs):", {q: len(v) for q,v in sorted(spec.items())})
    return rest

rest = classify(base_forms, "BASE FORMS (master parameter N)")
print()
# Shift-16 residual branch A: N = 32Q + 22 (M=16Q+11, N=2M). Forced prime: 630Q+433 = (315N-2)/16
branchA = [("leafA:630Q+433", 630, 433)]
for name,a,b in base_forms:
    branchA.append((name+"|Q", a*32, a*22 + b))
print("=== BRANCH A (N=32Q+22): leaf prime 630Q+433 vs re-parameterized shifts ===")
la = branchA[0]
for name,c,d in branchA[1:]:
    D = la[1]*d - c*la[2]
    if D == 0: print(f"  ZERO-DET: {la[0]} vs {name}")
    elif abs(D) == 1: print(f"  UNIT-DET: {la[0]} vs {name}")
    else:
        f = factorint(abs(D))
        small = {q:e for q,e in f.items() if q < 100}
        print(f"  {la[0]} vs {name}: det={D}, small primes {small}")
print()
# Branch B: N = 2M, M = 32R+3 -> N = 64R+6; leaf prime 630R+59 = (315N-2)/32
branchB = [("leafB:630R+59", 630, 59)]
for name,a,b in base_forms:
    branchB.append((name+"|R", a*64, a*6 + b))
print("=== BRANCH B (N=64R+6): leaf prime 630R+59 vs re-parameterized shifts ===")
lb = branchB[0]
for name,c,d in branchB[1:]:
    D = lb[1]*d - c*lb[2]
    if D == 0: print(f"  ZERO-DET: {lb[0]} vs {name}")
    elif abs(D) == 1: print(f"  UNIT-DET: {lb[0]} vs {name}")
    else:
        f = factorint(abs(D))
        small = {q:e for q,e in f.items() if q < 100}
        print(f"  {lb[0]} vs {name}: det={D}, small primes {small}")
