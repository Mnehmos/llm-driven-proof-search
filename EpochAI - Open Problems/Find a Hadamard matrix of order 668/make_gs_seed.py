"""Create a deterministic random cyclic GS(167) seed for a valid row tuple."""
import argparse,json,random
from pathlib import Path
N=167
def main():
    p=argparse.ArgumentParser();p.add_argument("--rows",type=int,nargs=4,required=True);p.add_argument("--seed",type=int,default=668167);p.add_argument("--output",required=True);q=p.parse_args()
    if sum(x*x for x in q.rows)!=4*N or any(x<=0 or x%2==0 or x>N for x in q.rows):raise ValueError("positive odd row squares must sum to 668")
    rng=random.Random(q.seed);seq=[]
    for total in q.rows:
        a=[1]*((N+total)//2)+[-1]*((N-total)//2);rng.shuffle(a);seq.append(a)
    residual=[sum(a[i]*a[(i+d)%N] for a in seq for i in range(N)) for d in range(1,(N-1)//2+1)]
    out={"construction":"cyclic Goethals-Seidel order 167","solved":not any(residual),"energy":sum(x*x for x in residual),"row_sums":q.rows,"residual":residual,"sequences":seq}
    Path(q.output).write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf8");print(json.dumps({"energy":out["energy"],"row_sums":q.rows,"output":q.output}))
if __name__=="__main__":main()
