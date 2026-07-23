"""Exact CP-SAT model for the 37-compression of an LP(333)."""
import argparse,json,time
from pathlib import Path
from ortools.sat.python import cp_model

N=37
def load_hint(path):
    if not path or not Path(path).exists(): return None
    z=json.loads(Path(path).read_text())
    d=z.get("compressed_sequences")
    if not d or len(d)!=2 or any(len(x)!=N for x in d): return None
    return [[(int(x)+9)//2 for x in row] for row in d]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--seconds",type=float,default=1800)
    ap.add_argument("--workers",type=int,default=4)
    ap.add_argument("--seed",type=int,default=333)
    ap.add_argument("--hint",default="legendre37_live.json")
    ap.add_argument("--max-changes",type=int,default=0,
                    help="if positive, exact LNS radius around the normalized hint")
    ap.add_argument("--output",default="legendre37_cpsat_candidate.json")
    a=ap.parse_args()
    m=cp_model.CpModel()
    v=[[m.NewIntVar(0,9,f"v_{s}_{i}") for i in range(N)] for s in range(2)]
    for s in range(2):
        m.Add(sum(v[s])==167)
        # Independent cyclic rotation and reflection normalizations.
        for i in range(1,N): m.Add(v[s][0]>=v[s][i])
        m.Add(v[s][1]>=v[s][N-1])
    m.Add(v[0][0]>=v[1][0]) # pair-exchange normalization
    squares=[]
    for s in range(2):
        for i in range(N):
            q=m.NewIntVar(0,81,f"sq_{s}_{i}")
            m.AddMultiplicationEquality(q,[v[s][i],v[s][i]])
            squares.append(q)
    m.Add(sum(squares)==1670)
    pair_count=0
    for h in range(1,19):
        ps=[]
        for s in range(2):
            for i in range(N):
                q=m.NewIntVar(0,81,f"p_{s}_{h}_{i}")
                m.AddMultiplicationEquality(q,[v[s][i],v[s][(i+h)%N]])
                ps.append(q);pair_count+=1
        m.Add(sum(ps)==1503)
    hint=load_hint(a.hint)
    if hint:
        # Rotate each hinted sequence so a maximum is at zero, orient it, then
        # order the pair to satisfy the exact model symmetries.
        norm=[]
        for row in hint:
            j=max(range(N),key=row.__getitem__);row=row[j:]+row[:j]
            if row[1]<row[-1]: row=[row[0]]+list(reversed(row[1:]))
            norm.append(row)
        if norm[0][0]<norm[1][0]: norm.reverse()
        changed=[]
        for s in range(2):
            for i in range(N):
                m.AddHint(v[s][i],norm[s][i])
                if a.max_changes:
                    ch=m.NewBoolVar(f"changed_{s}_{i}")
                    m.Add(v[s][i]==norm[s][i]).OnlyEnforceIf(ch.Not())
                    changed.append(ch)
        if changed: m.Add(sum(changed)<=a.max_changes)
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=a.seconds
    solver.parameters.num_search_workers=a.workers
    solver.parameters.random_seed=a.seed
    solver.parameters.log_search_progress=True
    t=time.time();status=solver.Solve(m);elapsed=time.time()-t
    name=solver.StatusName(status)
    event={"event":"result","status":name,"elapsed_s":elapsed,"pair_variables":pair_count,
           "max_changes":a.max_changes,
           "conflicts":solver.NumConflicts(),"branches":solver.NumBranches(),"wall_time":solver.WallTime()}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        vv=[[solver.Value(v[s][i]) for i in range(N)] for s in range(2)]
        d=[[2*x-9 for x in row] for row in vv]
        residual=[]
        for h in range(1,19):
            residual.append(18+sum(d[s][i]*d[s][(i+h)%N] for s in range(2) for i in range(N)))
        out={"construction":"Legendre pair length 333, 37-compression","solved_compression":not any(residual),
             "status":name,"elapsed_s":elapsed,"sums":[sum(x) for x in d],
             "square_norm":sum(x*x for row in d for x in row),"residual_paf_plus_18":residual,
             "compressed_sequences":d}
        Path(a.output).write_text(json.dumps(out,separators=(",",":"))+"\n")
        event["output"]=a.output;event["verified_zero"]=not any(residual)
    print(json.dumps(event),flush=True)

if __name__=="__main__": main()
