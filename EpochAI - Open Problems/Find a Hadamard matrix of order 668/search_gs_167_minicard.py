"""Exact native-cardinality SAT search for cyclic GS(167)."""
import argparse, json, time
from pathlib import Path
from pysat.solvers import Minicard

N,H=167,83
def xv(k,i):return 1+k*N+i

def main():
    p=argparse.ArgumentParser();p.add_argument("--hint",required=True);p.add_argument("--max-changes",type=int,default=60);p.add_argument("--active",type=int,choices=(1,2,3,4),default=4);p.add_argument("--fix-zero",action="store_true");p.add_argument("--output",default="gs_167_minicard_candidate.json");q=p.parse_args()
    hint=json.loads(Path(q.hint).read_text(encoding="utf8"))["sequences"]
    if len(hint)!=4 or any(len(a)!=N for a in hint):raise ValueError("invalid hint")
    rows=[sum(a) for a in hint]
    if sum(x*x for x in rows)!=4*N:raise ValueError("row identity failure")
    started=time.time();next_var=4*N+1;clauses=0;native=0
    with Minicard(use_timer=True) as slv:
        for k in range(4):
            lits=[xv(k,i) for i in range(N)];ones=(N+rows[k])//2
            slv.add_atmost(lits,ones);slv.add_atmost([-x for x in lits],N-ones);native+=2
            if q.fix_zero:slv.add_clause([xv(k,0)]);clauses+=1
            if k>=q.active:
                for i in range(N):slv.add_clause([xv(k,i) if hint[k][i]==1 else -xv(k,i)]);clauses+=1
        for d in range(1,H+1):
            ys=[]
            for k in range(4):
                for i in range(N):
                    x=xv(k,i);z=xv(k,(i+d)%N);y=next_var;next_var+=1;ys.append(y)
                    slv.add_clause([-x,-z,-y]);slv.add_clause([x,z,-y]);slv.add_clause([x,-z,y]);slv.add_clause([-x,z,y]);clauses+=4
            slv.add_atmost(ys,334);slv.add_atmost([-y for y in ys],4*N-334);native+=2
        phases=[];changes=[]
        for k in range(4):
            for i in range(N):
                x=xv(k,i);positive=hint[k][i]==1;phases.append(x if positive else -x);changes.append(-x if positive else x)
        slv.set_phases(phases)
        if q.max_changes:slv.add_atmost(changes,q.max_changes);native+=1
        print(json.dumps({"event":"model","variables":next_var-1,"clauses":clauses,"native_atmost":native,"max_changes":q.max_changes,"active":q.active,"fix_zero":q.fix_zero,"build_s":time.time()-started}),flush=True)
        slv.conf_budget(2_000_000_000);sat=slv.solve_limited(expect_interrupt=True)
        event={"event":"result","sat":sat,"elapsed_s":time.time()-started,"accum_stats":slv.accum_stats()}
        if sat:
            model=set(x for x in slv.get_model() if x>0);seq=[[1 if xv(k,i) in model else -1 for i in range(N)] for k in range(4)]
            residual=[sum(seq[k][i]*seq[k][(i+d)%N] for k in range(4) for i in range(N)) for d in range(1,H+1)]
            out={"construction":"cyclic Goethals-Seidel order 167","solver":"MiniCard exact","solved":not any(residual),"energy":sum(x*x for x in residual),"row_sums":[sum(a) for a in seq],"residual":residual,"sequences":seq}
            assert out["solved"] and out["row_sums"]==rows
            Path(q.output).write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf8");event["output"]=q.output
        print(json.dumps(event),flush=True)

if __name__=="__main__":main()
