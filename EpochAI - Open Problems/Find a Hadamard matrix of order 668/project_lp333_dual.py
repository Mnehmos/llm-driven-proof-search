"""Project a fixed-37 LP(333) state onto the exact length-9 CRT margins."""
import argparse, json
from pathlib import Path
from ortools.sat.python import cp_model

N,P,Q=333,37,9
COL=[[16,19,17,15,20,15,27,21,17],[18,17,20,21,18,17,22,18,16]]
def chi(r): return 0 if r==0 else (1 if pow(r,18,37)==1 else -1)
def target(s,r): return 1 if r==0 else (3*chi(r) if s==0 else -3*chi(r))
def crt(r,c): return r+P*((c-r)%Q)

def project(old,s,seconds):
    m=cp_model.CpModel();x=[[m.NewBoolVar(f"x_{r}_{c}") for c in range(Q)] for r in range(P)]
    for r in range(P):m.Add(sum(x[r])==(Q+target(s,r))//2)
    for c in range(Q):m.Add(sum(x[r][c] for r in range(P))==COL[s][c])
    change=[]
    for r in range(P):
        for c in range(Q):
            was=old[crt(r,c)]==1
            change.append(x[r][c].Not() if was else x[r][c])
    m.Minimize(sum(change));slv=cp_model.CpSolver();slv.parameters.max_time_in_seconds=seconds
    slv.parameters.num_search_workers=1;status=slv.Solve(m)
    assert status in (cp_model.OPTIMAL,cp_model.FEASIBLE),slv.StatusName(status)
    seq=[-1]*N
    for r in range(P):
        for c in range(Q):seq[crt(r,c)]=1 if slv.Value(x[r][c]) else -1
    return seq,int(slv.ObjectiveValue()),slv.StatusName(status)

def residual(seq):
    return [2+sum(seq[s][i]*seq[s][(i+h)%N] for s in range(2) for i in range(N)) for h in range(1,167)]
def main():
    p=argparse.ArgumentParser();p.add_argument("--input",default="lp333_native_live.json")
    p.add_argument("--output",default="lp333_dual_seed.json");p.add_argument("--raw",default="lp333_dual_seed.txt")
    p.add_argument("--seconds",type=float,default=30);a=p.parse_args()
    old=json.loads(Path(a.input).read_text())["sequences"]
    seq=[];dist=[];statuses=[]
    for s in range(2):
        z,d,st=project(old[s],s,a.seconds);seq.append(z);dist.append(d);statuses.append(st)
    rr=residual(seq);comp37=[[sum(seq[s][r+P*k] for k in range(Q)) for r in range(P)] for s in range(2)]
    comp9=[[sum(seq[s][crt(r,c)] for r in range(P)) for c in range(Q)] for s in range(2)]
    out={"construction":"LP(333) dual-margin projection seed","solved":not any(rr),"energy":sum(x*x for x in rr),
         "nonzero":sum(x!=0 for x in rr),"maxabs":max(map(abs,rr)),"hamming_from_input":dist,"statuses":statuses,
         "sums":[sum(z) for z in seq],"residual_paf_plus_2":rr,"compression37":comp37,"compression9":comp9,"sequences":seq}
    assert all(comp37[s][r]==target(s,r) for s in range(2) for r in range(P))
    assert all((comp9[s][c]+P)//2==COL[s][c] for s in range(2) for c in range(Q))
    Path(a.output).write_text(json.dumps(out,separators=(",",":"))+"\n")
    Path(a.raw).write_text(" ".join(map(str,seq[0]+seq[1]))+"\n")
    print(json.dumps({k:out[k] for k in ("solved","energy","nonzero","maxabs","hamming_from_input","statuses")}))
if __name__=="__main__":main()
