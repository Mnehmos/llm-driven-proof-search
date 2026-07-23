"""Exact MiniCard search for the p=37,q=3 quadratic-character uncompression."""
import argparse,json,time
from pathlib import Path
from pysat.solvers import Minicard

N,H,P,Q=333,166,37,9
COL=[[16,19,17,15,20,15,27,21,17],[18,17,20,21,18,17,22,18,16]]
def chi(x):
    x%=P
    if not x:return 0
    return 1 if pow(x,(P-1)//2,P)==1 else -1
def target(s,r): return 1 if r==0 else (3*chi(r) if s==0 else -3*chi(r))
def xv(s,i):return 1+s*N+i
def crt(r,c):return r+P*((c-r)%Q)

def load_hint(path):
    if not path or not Path(path).exists():return None
    z=json.loads(Path(path).read_text())
    a=z.get("sequences")
    return a if a and len(a)==2 and all(len(x)==N for x in a) else None

def main():
    global COL
    ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=1800)
    ap.add_argument("--hint",default="lp333_native_live.json")
    ap.add_argument("--compression9")
    ap.add_argument("--output",default="lp333_minicard_candidate.json")
    a=ap.parse_args();
    if a.compression9:COL=json.loads(Path(a.compression9).read_text())["column_plus_counts"]
    t0=time.time();next_var=2*N+1;clauses=0;native=0
    with Minicard(use_timer=True) as slv:
        # Fixed 37-compression: exact plus counts in every residue class.
        for s in range(2):
            for r in range(P):
                lits=[xv(s,r+P*k) for k in range(Q)];k=(Q+target(s,r))//2
                slv.add_atmost(lits,k);slv.add_atmost([-x for x in lits],Q-k);native+=2
            # Exact length-9 compression: column sums in the 37-by-9 CRT grid.
            for c in range(Q):
                lits=[xv(s,crt(r,c)) for r in range(P)];k=COL[s][c]
                slv.add_atmost(lits,k);slv.add_atmost([-x for x in lits],P-k);native+=2
        # LP equations: exactly 334 disagreements among the 666 paired entries.
        for h in range(1,H+1):
            ys=[]
            for s in range(2):
                for i in range(N):
                    x=xv(s,i);z=xv(s,(i+h)%N);y=next_var;next_var+=1;ys.append(y)
                    slv.add_clause([-x,-z,-y]);slv.add_clause([x,z,-y])
                    slv.add_clause([x,-z,y]);slv.add_clause([-x,z,y]);clauses+=4
            slv.add_atmost(ys,334);slv.add_atmost([-y for y in ys],332);native+=2
        hint=load_hint(a.hint)
        if hint:
            phases=[xv(s,i) if hint[s][i]==1 else -xv(s,i) for s in range(2) for i in range(N)]
            slv.set_phases(phases)
        print(json.dumps({"event":"model","variables":next_var-1,"clauses":clauses,"native_atmost":native,"build_s":time.time()-t0}),flush=True)
        slv.conf_budget(2_000_000_000)
        # Minicard exposes no portable wall-clock interrupt; the host owns timeout.
        sat=slv.solve_limited(expect_interrupt=True)
        elapsed=time.time()-t0
        event={"event":"result","sat":sat,"elapsed_s":elapsed,"accum_stats":slv.accum_stats()}
        if sat:
            model=set(x for x in slv.get_model() if x>0)
            seq=[[1 if xv(s,i) in model else -1 for i in range(N)] for s in range(2)]
            residual=[2+sum(seq[s][i]*seq[s][(i+h)%N] for s in range(2) for i in range(N)) for h in range(1,H+1)]
            comp=[[sum(seq[s][r+P*k] for k in range(Q)) for r in range(P)] for s in range(2)]
            comp9=[[sum(seq[s][crt(r,c)] for r in range(P)) for c in range(Q)] for s in range(2)]
            out={"construction":"Legendre pair length 333","fixed_compressions":["quadratic-character length 37","exact length 9"],
                 "solved":not any(residual),"energy":sum(x*x for x in residual),"sums":[sum(x) for x in seq],
                 "residual_paf_plus_2":residual,"compression37":comp,"compression9":comp9,"sequences":seq}
            assert not any(residual) and all(comp[s][r]==target(s,r) for s in range(2) for r in range(P)) and all((comp9[s][c]+P)//2==COL[s][c] for s in range(2) for c in range(Q))
            Path(a.output).write_text(json.dumps(out,separators=(",",":"))+"\n");event["output"]=a.output
        print(json.dumps(event),flush=True)
if __name__=="__main__":main()
