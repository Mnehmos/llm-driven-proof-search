"""Create and exactly score a two-Paley GS(167) heuristic seed."""
import argparse
import json
from pathlib import Path

N = 167


def chi(i):
    return 0 if i == 0 else (1 if pow(i, 83, N) == 1 else -1)


p = argparse.ArgumentParser()
p.add_argument("--input", required=True)
p.add_argument("--output", default="agent_gspec_two_paley_seed.json")
q = p.parse_args()
src = json.loads(Path(q.input).read_text(encoding="utf8"))["sequences"]
if [sum(src[0]), sum(src[1])] != [21, 15]:
    raise ValueError("first two hint rows must have sums 21 and 15")
paley = [1 if i == 0 else chi(i) for i in range(N)]
seq = [src[0], src[1], paley, paley]
r = [sum(seq[k][i] * seq[k][(i+d) % N] for k in range(4) for i in range(N)) for d in range(1, 84)]
out = {"construction":"cyclic Goethals-Seidel order 167, two Paley rows","search":"agent deterministic seed","solved":not any(r),"independently_recomputed":True,"energy":sum(x*x for x in r),"l1":sum(abs(x) for x in r),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r)),"row_sums":[sum(x) for x in seq],"residual":r,"sequences":seq}
Path(q.output).write_text(json.dumps(out,separators=(",", ":"))+"\n",encoding="utf8")
print(json.dumps({k:out[k] for k in ("energy","l1","nonzero","maxabs","row_sums")} | {"output":q.output}))
