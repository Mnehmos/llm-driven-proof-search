"""Exact LP(333) search under cyclic multiplier invariance."""
import argparse,json,math,time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model
N,H,P,Q=333,166,37,9
def chi(r):return 0 if r==0 else (1 if pow(r,18,37)==1 else -1)
def target(s,r):return 1 if r==0 else (3*chi(r) if s==0 else -3*chi(r))
def order(h):
    x=1
    for k in range(1,217):
        x=x*h%N
        if x==1:return k
def subgroups():
    seen={};
    for h in range(1,N):
        if math.gcd(h,N)>1 or h%3!=1 or order(h) not in (6,9,12,18):continue
        x=1;g=[]
        for _ in range(order(h)):g.append(x);x=x*h%N
        seen[tuple(sorted(g))]=h
    return [(h,g) for g,h in seen.items()]
def orbits(group):
    todo=set(range(N));ans=[]
    while todo:
        i=min(todo);o=sorted({i*g%N for g in group});ans.append(o);todo.difference_update(o)
    owner=[0]*N
    for j,o in enumerate(ans):
        for i in o:owner[i]=j
    return ans,owner
def solve(h,group,seconds,workers,outpath):
    orb,own=orbits(group);m=cp_model.CpModel();x=[[m.NewBoolVar(f"x_{s}_{j}") for j in range(len(orb))] for s in range(2)]
    for s in range(2):
        for r in range(P):
            cnt=Counter(own[i] for i in range(r,N,P));m.Add(sum(v*x[s][j] for j,v in cnt.items())==(Q+target(s,r))//2)
    y={}
    for shift in range(1,H+1):
        terms=[]
        for s in range(2):
            cnt=Counter(tuple(sorted((own[i],own[(i+shift)%N]))) for i in range(N) if own[i]!=own[(i+shift)%N])
            for (u,v),coef in cnt.items():
                key=(s,u,v)
                if key not in y:
                    z=m.NewBoolVar(f"xor_{s}_{u}_{v}");m.AddBoolXOr([x[s][u],x[s][v],z.Not()]);y[key]=z
                terms.append(coef*y[key])
        m.Add(sum(terms)==334)
    slv=cp_model.CpSolver();slv.parameters.max_time_in_seconds=seconds;slv.parameters.num_search_workers=workers;slv.parameters.random_seed=h
    t=time.time();st=slv.Solve(m);elapsed=time.time()-t;name=slv.StatusName(st)
    ev={"generator":h,"order":len(group),"orbits":len(orb),"orbit_sizes":dict(Counter(map(len,orb))),"x_variables":2*len(orb),"xor_variables":len(y),"status":name,"elapsed_s":elapsed,"conflicts":slv.NumConflicts(),"branches":slv.NumBranches()}
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        seq=[[1 if slv.Value(x[s][own[i]]) else -1 for i in range(N)] for s in range(2)]
        rr=[2+sum(seq[s][i]*seq[s][(i+d)%N] for s in range(2) for i in range(N)) for d in range(1,H+1)]
        comp=[[sum(seq[s][r+P*k] for k in range(Q)) for r in range(P)] for s in range(2)]
        ans={"construction":"Legendre pair length 333 with cyclic multiplier subgroup","multiplier_generator":h,"multiplier_group":list(group),"solved":not any(rr),"energy":sum(z*z for z in rr),"sums":[sum(z) for z in seq],"residual_paf_plus_2":rr,"compression37":comp,"sequences":seq}
        assert not any(rr) and all(comp[s][r]==target(s,r) for s in range(2) for r in range(P));Path(outpath).write_text(json.dumps(ans,separators=(",",":"))+"\n");ev["output"]=outpath
    return ev
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=60);ap.add_argument("--workers",type=int,default=1);ap.add_argument("--output",default="lp333_multiplier_candidate.json");ap.add_argument("--generators",type=int,nargs="*");a=ap.parse_args()
    groups=subgroups()
    if a.generators:
        wanted=set(a.generators);groups=[(h,g) for h,g in groups if h in wanted]
        missing=sorted(wanted-{h for h,_ in groups})
        if missing:raise SystemExit(f"unknown subgroup generators: {missing}")
    print(json.dumps({"event":"groups","count":len(groups),"groups":[{"generator":h,"order":len(g)} for h,g in groups]}),flush=True)
    for j,(h,g) in enumerate(groups):
        ev=solve(h,g,a.seconds,a.workers,a.output);print(json.dumps({"event":"result",**ev}),flush=True)
        if ev["status"] in ("OPTIMAL","FEASIBLE"):break
if __name__=="__main__":main()
