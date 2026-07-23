"""Exact CP-SAT uncompression of the p=37,q=3 character candidate."""
import argparse,json,time
from pathlib import Path
from ortools.sat.python import cp_model
N,H,P,Q=333,166,37,9
COL=[[16,19,17,15,20,15,27,21,17],[18,17,20,21,18,17,22,18,16]]
def chi(x):
    x%=P
    return 0 if not x else (1 if pow(x,(P-1)//2,P)==1 else -1)
def target(s,r):return 1 if r==0 else (3*chi(r) if s==0 else -3*chi(r))
def crt(r,c):return r+P*((c-r)%Q)
def hint(path):
    if not path or not Path(path).exists():return None
    z=json.loads(Path(path).read_text());x=z.get("sequences")
    return x if x and len(x)==2 and all(len(y)==N for y in x) else None
def main():
    global COL
    ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=900)
    ap.add_argument("--workers",type=int,default=3);ap.add_argument("--seed",type=int,default=333)
    ap.add_argument("--hint",default="lp333_native_live.json");ap.add_argument("--max-changes",type=int,default=36)
    ap.add_argument("--optimize-l1",action="store_true");ap.add_argument("--compression9")
    ap.add_argument("--output",default="lp333_cpsat_candidate.json");a=ap.parse_args()
    if a.compression9:COL=json.loads(Path(a.compression9).read_text())["column_plus_counts"]
    m=cp_model.CpModel();x=[[m.NewBoolVar(f"x_{s}_{i}") for i in range(N)] for s in range(2)]
    for s in range(2):
        for r in range(P):m.Add(sum(x[s][r+P*k] for k in range(Q))==(Q+target(s,r))//2)
        for c in range(Q):m.Add(sum(x[s][crt(r,c)] for r in range(P))==COL[s][c])
    deviations=[]
    for h in range(1,H+1):
        ys=[]
        for s in range(2):
            for i in range(N):
                y=m.NewBoolVar(f"xor_{s}_{h}_{i}");ys.append(y)
                m.AddBoolXOr([x[s][i],x[s][(i+h)%N],y.Not()])
        if a.optimize_l1:
            d=m.NewIntVar(0,334,f"dev_{h}");m.AddAbsEquality(d,sum(ys)-334);deviations.append(d)
        else:m.Add(sum(ys)==334)
    if deviations:m.Minimize(sum(deviations))
    hh=hint(a.hint);changes=[]
    if hh:
        for s in range(2):
            for i in range(N):
                m.AddHint(x[s][i],1 if hh[s][i]==1 else 0)
                if a.max_changes:
                    c=m.NewBoolVar(f"change_{s}_{i}");m.Add(x[s][i]!=(1 if hh[s][i]==1 else 0)).OnlyEnforceIf(c);m.Add(x[s][i]==(1 if hh[s][i]==1 else 0)).OnlyEnforceIf(c.Not());changes.append(c)
        if changes:m.Add(sum(changes)<=a.max_changes)
    slv=cp_model.CpSolver();slv.parameters.max_time_in_seconds=a.seconds;slv.parameters.num_search_workers=a.workers;slv.parameters.random_seed=a.seed
    slv.parameters.log_search_progress=True;t=time.time();st=slv.Solve(m);elapsed=time.time()-t;name=slv.StatusName(st)
    ev={"event":"result","status":name,"elapsed_s":elapsed,"max_changes":a.max_changes,"optimize_l1":a.optimize_l1,"conflicts":slv.NumConflicts(),"branches":slv.NumBranches(),"wall_time":slv.WallTime()}
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        seq=[[1 if slv.Value(x[s][i]) else -1 for i in range(N)] for s in range(2)]
        rr=[2+sum(seq[s][i]*seq[s][(i+h)%N] for s in range(2) for i in range(N)) for h in range(1,H+1)]
        comp=[[sum(seq[s][r+P*k] for k in range(Q)) for r in range(P)] for s in range(2)]
        comp9=[[sum(seq[s][crt(r,c)] for r in range(P)) for c in range(Q)] for s in range(2)]
        out={"construction":"Legendre pair length 333","fixed_compressions":["quadratic-character length 37","exact length 9"],"solved":not any(rr),"energy":sum(z*z for z in rr),"sums":[sum(z) for z in seq],"residual_paf_plus_2":rr,"compression37":comp,"compression9":comp9,"sequences":seq}
        assert all(comp[s][r]==target(s,r) for s in range(2) for r in range(P)) and all((comp9[s][c]+P)//2==COL[s][c] for s in range(2) for c in range(Q))
        if not a.optimize_l1:assert not any(rr)
        Path(a.output).write_text(json.dumps(out,separators=(",",":"))+"\n");ev.update(output=a.output,energy=out["energy"],l1=sum(map(abs,rr)),nonzero=sum(z!=0 for z in rr))
    print(json.dumps(ev),flush=True)
if __name__=="__main__":main()
