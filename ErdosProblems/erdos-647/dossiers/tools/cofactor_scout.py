from math import gcd
# Pure/near-prime shift rows k | 2520 with verified classifications, cofactor c_k*N - 1, c_k = 2520/k
divisor_shifts = {1:2520, 2:1260, 3:840, 4:630, 5:504, 6:420, 8:315, 9:280, 10:252, 12:210, 18:140, 20:126, 24:105}
# Non-divisor shifts formalized so far: 16 -> 2520N-16 = 8*(315N-2); 14 -> 2520N-14 = 2*(1260N-7)=14*(180N-1); 15 -> 15*(168N-1); 11,13 prime demands on 2520N-k itself
extra = {14:(14,180,1), 15:(15,168,1), 16:(8,315,2)}
print("=== pairwise gcd bound of cofactors c_a*N-1 vs c_b*N-1: gcd | (c_a - c_b) ===")
ks = sorted(divisor_shifts)
for i,a in enumerate(ks):
    for b in ks[i+1:]:
        ca, cb = divisor_shifts[a], divisor_shifts[b]
        d = abs(ca-cb)
        # actual common prime factors possible: primes p | d with p ∤ c_a (else p | 1)
        ps = set()
        dd = d
        for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73]:
            while dd % p == 0: dd //= p; ps.add(p)
        viable = sorted(p for p in ps if ca % p != 0)
        if viable:
            print(f"shifts ({a},{b}): coeffs ({ca},{cb}), diff {d}, shared primes possible: {viable}")
print()
print("=== collisions with non-divisor-shift cofactors (c*N - d form) ===")
for k,(g,c,d0) in extra.items():
    for a,ca in divisor_shifts.items():
        # gcd(c*N-d0, ca*N-1) | (ca*d0 - c) resultant
        r = abs(ca*d0 - c)
        if r == 0:
            print(f"!!! EXACT COLLISION shift {k} cofactor {c}N-{d0} vs shift {a} cofactor {ca}N-1")
            continue
        ps = sorted(set(p for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47] if r%p==0 and c%p!=0))
        if ps and r < 5000:
            print(f"shift {k} ({c}N-{d0}) vs shift {a} ({ca}N-1): resultant {r}, shared primes possible {ps}")
print()
print("=== identical-value collisions: does c_a*N-1 = c_b*M-1 force structure? trivial. Check divisibility c_a | c_b cases ===")
for i,a in enumerate(ks):
    for b in ks[i+1:]:
        ca, cb = divisor_shifts[a], divisor_shifts[b]
        if cb % ca == 0 or ca % cb == 0:
            big, small, kb, ks_ = (ca,cb,a,b) if ca>cb else (cb,ca,b,a)
            m = big//small
            print(f"shift {kb} coeff {big} = {m} * {small} (shift {ks_}): {big}N-1 ≡ -1 mod {m}? relation: {big}N-1 = {m}*({small}N) - 1 -> gcd({small}N-1, {big}N-1) | {m-1}... m={m}")
