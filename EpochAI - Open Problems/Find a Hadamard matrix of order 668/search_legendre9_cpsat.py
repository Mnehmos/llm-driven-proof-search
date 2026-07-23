"""Enumerate exact length-9 compressions compatible with LP(333)."""
import argparse,json,time
from pathlib import Path
from ortools.sat.python import cp_model

def gale_ryser(cols):
    rows=sorted([5]+[6]*18+[3]*18,reverse=True);cols=sorted(cols,reverse=True)
    return sum(rows)==sum(cols) and all(sum(rows[:k])<=sum(min(k,c) for c in cols) for k in range(1,38))

class Grab(cp_model.CpSolverSolutionCallback):
    def __init__(self,w,limit,out):super().__init__();self.w=w;self.limit=limit;self.out=out
    def on_solution_callback(self):
        ww=[[self.Value(x) for x in row] for row in self.w]
        if gale_ryser(ww[0]) and gale_ryser(ww[1]):
            self.out.append({"column_plus_counts":ww,"compressed_sequences":[[2*x-37 for x in row] for row in ww]})
        if len(self.out)>=self.limit:self.StopSearch()

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=120);ap.add_argument("--limit",type=int,default=1000);ap.add_argument("--workers",type=int,default=1);ap.add_argument("--one",action="store_true");ap.add_argument("--output",default="legendre9_candidates.json");a=ap.parse_args()
    m=cp_model.CpModel();w=[[m.NewIntVar(0,37,f"w_{s}_{i}") for i in range(9)] for s in range(2)]
    for s in range(2):
        m.Add(sum(w[s])==167)
        for i in range(1,9):m.Add(w[s][0]>=w[s][i])
        m.Add(w[s][1]>=w[s][8])
    squares=[]
    for s in range(2):
        for i in range(9):q=m.NewIntVar(0,1369,f"sq_{s}_{i}");m.AddMultiplicationEquality(q,[w[s][i],w[s][i]]);squares.append(q)
    m.Add(sum(squares)==6346)
    for h in range(1,5):
        ps=[]
        for s in range(2):
            for i in range(9):q=m.NewIntVar(0,1369,f"p_{s}_{h}_{i}");m.AddMultiplicationEquality(q,[w[s][i],w[s][(i+h)%9]]);ps.append(q)
        m.Add(sum(ps)==6179)
    slv=cp_model.CpSolver();slv.parameters.max_time_in_seconds=a.seconds;slv.parameters.num_search_workers=a.workers;slv.parameters.random_seed=9
    out=[];t=time.time()
    if a.one:
        status=slv.Solve(m)
        if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
            ww=[[slv.Value(x) for x in row] for row in w]
            if gale_ryser(ww[0]) and gale_ryser(ww[1]):out.append({"column_plus_counts":ww,"compressed_sequences":[[2*x-37 for x in row] for row in ww]})
    else:
        cb=Grab(w,a.limit,out);status=slv.SearchForAllSolutions(m,cb)
    payload={"construction":"LP(333) exact length-9 compression candidates","status":slv.StatusName(status),"elapsed_s":time.time()-t,"count":len(out),"candidates":out}
    Path(a.output).write_text(json.dumps(payload,separators=(",",":"))+"\n");print(json.dumps({k:payload[k] for k in ("status","elapsed_s","count")}),flush=True)
if __name__=="__main__":main()
