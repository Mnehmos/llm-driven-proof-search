"""Independent check that TURYN_HEX in generate_hadamard_428.js decodes to a
genuine Turyn-type quadruple T(36,36,36,35).

Defining property (Turyn-type sequences X, Y, Z, W of lengths n, n, n, n-1):
the nonperiodic autocorrelations satisfy
    N_X(s) + N_Y(s) + 2 N_Z(s) + 2 N_W(s) = 0   for every shift s >= 1.
This is exactly the seed family used by Kharaghani and Tayfeh-Rezaie for the
first Hadamard matrix of order 428 (J. Combin. Des. 13 (2005) 435-440):
T(36,36,36,35) -> T-sequences of length 107 -> Goethals-Seidel array -> H(428).

Because this script verifies the defining identity and build/verify code
downstream checks the full 428x428 Gram matrix, the certificate chain does not
depend on trusting the transcription of the hex constant.
"""
import re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE / "generate_hadamard_428.js").read_text(encoding="utf-8")
hex_s = re.search(r"TURYN_HEX = '([0-9a-f]+)'", src).group(1)

seqs = [[], [], [], []]
for c in hex_s[:-1]:
    bits = bin(int(c, 16))[2:].zfill(4)
    for s in range(4):
        seqs[s].append(1 if bits[s] == "0" else -1)
last = bin(int(hex_s[-1], 16))[2:].zfill(3)
for s in range(3):
    seqs[s].append(1 if last[s] == "0" else -1)
X, Y, Z, W = seqs

assert [len(q) for q in seqs] == [36, 36, 36, 35], [len(q) for q in seqs]

def npaf(a, s):
    return sum(a[i] * a[i + s] for i in range(len(a) - s))

bad = [s for s in range(1, 36)
       if npaf(X, s) + npaf(Y, s) + 2 * npaf(Z, s) + 2 * (npaf(W, s) if s < 35 else 0) != 0]
if bad:
    print("FAIL: Turyn-type identity violated at shifts", bad)
    sys.exit(1)
print("PASS: TURYN_HEX decodes to a Turyn-type quadruple T(36,36,36,35); "
      "N_X + N_Y + 2N_Z + 2N_W = 0 at every shift 1..35")
