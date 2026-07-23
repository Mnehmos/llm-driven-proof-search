"""Create a deterministic GS(167) seed with the final block fixed to Paley."""
import argparse, json, random
from pathlib import Path

N = 167


def chi(i):
    return 0 if i == 0 else (1 if pow(i, (N-1)//2, N) == 1 else -1)


def main():
    p=argparse.ArgumentParser();p.add_argument("--output",default="gs_167_paley_seed.json");p.add_argument("--seed",type=int,default=167668);p.add_argument("--rows",type=int,nargs=3,default=(19,15,9));q=p.parse_args()
    rng=random.Random(q.seed);seq=[]
    if sum(x*x for x in q.rows)!=667 or any(x<=0 or x%2==0 or x>N for x in q.rows):raise ValueError("variable row sums must be positive odd squares summing to 667")
    for total in q.rows:
        a=[1]*((N+total)//2)+[-1]*((N-total)//2);rng.shuffle(a);seq.append(a)
    paley=[1 if i==0 else chi(i) for i in range(N)];seq.append(paley)
    residual=[sum(a[i]*a[(i+d)%N] for a in seq for i in range(N)) for d in range(1,(N-1)//2+1)]
    payload={"construction":"cyclic Goethals-Seidel order 167, final Paley block fixed","solved":not any(residual),"energy":sum(x*x for x in residual),"row_sums":[sum(a) for a in seq],"residual":residual,"sequences":seq}
    assert payload["row_sums"]==list(q.rows)+[1]
    assert all(sum(paley[i]*paley[(i+d)%N] for i in range(N))==-1 for d in range(1,N))
    Path(q.output).write_text(json.dumps(payload,separators=(",",":"))+"\n",encoding="utf8")
    print(json.dumps({k:payload[k] for k in ("energy","row_sums","solved")}|{"output":q.output}))


if __name__=="__main__":main()
