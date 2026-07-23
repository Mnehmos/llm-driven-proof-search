"""Compressed exact parity repair using the 83 column-syndrome classes."""
from __future__ import annotations
import argparse,hashlib,json,time
from collections import defaultdict
from pathlib import Path
from ortools.sat.python import cp_model
L=(84,84,83,83)
def residual(a):return [sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in a) for d in range(1,84)]
def margins(a):
 rows=[sum(x) for x in a];alts=[sum(v if i%2==0 else -v for i,v in enumerate(x)) for x in a];q=[]
 for x in a:q += [sum(v for i,v in enumerate(x) if i%4==0)-sum(v for i,v in enumerate(x) if i%4==2),sum(v for i,v in enumerate(x) if i%4==1)-sum(v for i,v in enumerate(x) if i%4==3)]
 return rows,alts,q
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=120);p.add_argument('--workers',type=int,default=8);p.add_argument('--feasible',action='store_true');p.add_argument('--output',type=Path,default=Path('agent_bsd_repair_grouped_pb0.json'));g=p.parse_args();st=time.time();a=json.loads(g.input.read_text())['sequences'];r0=residual(a);before=margins(a)
 groups=defaultdict(list)
 for k,n in enumerate(L):
  for i in range(n):
   sig=0
   for d in range(1,84):
    if (i<d)^(i>=n-d):sig|=1<<(d-1)
   groups[sig].append((k,i))
 zero=groups.pop(0,[]);sigs=list(groups);assert len(sigs)==83 and all(len(groups[x])==4 for x in sigs),(len(sigs),{len(v) for v in groups.values()},zero)
 target=sum((((r0[d-1]//2)&1)<<(d-1)) for d in range(1,84))
 # Solve the nonsingular 83x83 syndrome-class system for required class parity.
 rows=[]
 for bit in range(83):rows.append([sum(((sig>>bit)&1)<<j for j,sig in enumerate(sigs)),(target>>bit)&1])
 piv=[];rr=0
 for col in range(83):
  hit=next(j for j in range(rr,83) if (rows[j][0]>>col)&1);rows[rr],rows[hit]=rows[hit],rows[rr]
  for j in range(83):
   if j!=rr and ((rows[j][0]>>col)&1):rows[j][0]^=rows[rr][0];rows[j][1]^=rows[rr][1]
  piv.append(col);rr+=1
 assert rr==83
 want=[0]*83
 for j,col in enumerate(piv):want[col]=rows[j][1]
 check=0
 for j,v in enumerate(want):
  if v:check^=sigs[j]
 assert check==target
 m=cp_model.CpModel();f=[[m.new_bool_var(f'f_{k}_{i}') for i in range(n)] for k,n in enumerate(L)];one=m.new_bool_var('one');m.add(one==1)
 for j,sig in enumerate(sigs):
  lits=[f[k][i] for k,i in groups[sig]];m.add_bool_xor(lits if want[j] else lits+[one])
 for k,x in enumerate(a):
  for c in range(4):
   plus=[f[k][i] for i in range(c,len(x),4) if x[i]==1];minus=[f[k][i] for i in range(c,len(x),4) if x[i]==-1];m.add(sum(plus)==sum(minus))
 changes=sum(v for row in f for v in row)
 if not g.feasible:m.minimize(changes)
 for row in f:
  for v in row:m.add_hint(v,0)
 s=cp_model.CpSolver();s.parameters.max_time_in_seconds=g.seconds;s.parameters.num_search_workers=g.workers;s.parameters.random_seed=668
 print(json.dumps({'event':'built','classes':83,'class_size':4,'zero_columns':zero,'target_weight':target.bit_count(),'required_odd_classes':sum(want),'elapsed_s':time.time()-st}),flush=True);status=s.solve(m);print(json.dumps({'event':'result','status':s.status_name(status),'objective':s.objective_value,'bound':s.best_objective_bound,'conflicts':s.num_conflicts,'branches':s.num_branches,'wall_time':s.wall_time}),flush=True)
 if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):return 2
 b=[[-x if s.value(f[k][i]) else x for i,x in enumerate(row)] for k,row in enumerate(a)];out_r=residual(b);after=margins(b);chg=[(k,i) for k,row in enumerate(f) for i,v in enumerate(row) if s.value(v)]
 if before!=after or any(x%4 for x in out_r):raise RuntimeError((before,after,out_r))
 out={'construction':'base sequences BS(84,83)','search':'agent compressed syndrome-class exact parity repair','solved':not any(out_r),'independently_recomputed':True,'energy':sum(x*x for x in out_r),'l1':sum(map(abs,out_r)),'parity_bad':0,'changes':len(chg),'changed_positions':chg,'elapsed_s':time.time()-st,'row_sums':after[0],'alternating_sums':after[1],'z4_components':after[2],'residual':out_r,'sequences':b};raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'event':'verified_parity0','energy':out['energy'],'l1':out['l1'],'changes':len(chg),'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
