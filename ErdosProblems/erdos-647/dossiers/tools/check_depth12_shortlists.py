"""Exactly factor scanner shortlists; computational evidence, not a proof."""

import re
import sys
from sympy import factorint, divisor_count, isprime

count = 0
pass7 = 0
pass11 = 0
for line in sys.stdin:
    m = re.search(r"SHORTLIST N=(\d+)", line)
    if not m:
        continue
    count += 1
    N = int(m.group(1))
    n = 2520 * N
    f7 = factorint(n - 7)
    t7 = int(divisor_count(n - 7))
    if t7 > 9:
        continue
    pass7 += 1
    f11 = factorint(n - 11)
    t11 = int(divisor_count(n - 11))
    print(f"PASS7 N={N} n={n} f7={f7} tau7={t7} f11={f11} tau11={t11}")
    if t11 > 13:
        continue
    pass11 += 1
    rows = []
    good = True
    for k in range(1, 13):
        x = n - k
        fac = factorint(x)
        tau = int(divisor_count(x))
        rows.append((k, x, fac, tau, k + 2, tau <= k + 2))
        good &= tau <= k + 2
    forms = [(c, c * N - 1, bool(isprime(c * N - 1)))
             for c in [210, 315, 420, 630, 840, 1260, 2520]]
    print(f"FULL N={N} n={n} good={good} forms={forms}")
    for row in rows:
        print("ROW", row)

print(f"CHECKED shortlists={count} pass7={pass7} pass11={pass11}")
