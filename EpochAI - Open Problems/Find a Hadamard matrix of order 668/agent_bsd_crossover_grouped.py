"""Minimum-Hamming projection into a fixed row/alt/z=i and parity-zero fibre."""
from __future__ import annotations
import argparse,hashlib,json,time
from collections import defaultdict
from pathlib import Path
from ortools.sat.python import cp_model
L=(84,84,83,83)
def residual(a):return [sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in a) for d in range(1,84)]
def margins(a):
 r=[sum(x) for x in a];al=[sum(v if i%2==0 else -v for i,v in enumerate(x)) for x in a];q=[]
 for x in a:q += [sum(x[0::4])-sum(x[2::4]),sum(x[1::4])-sum(x[3::4])]
 return r,al,q
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--rows',required=True);p.add_argument('--alts',required=True);p.add_argument('--z4',required=True);p.add_argument('--seconds',type=float,default=300);p.add_argument('--workers',type=int,default=8);p.add_argument('--output',type=Path,default=Path('agent_bsd_crossover_grouped.json'));g=p.parse_args();st=time.time();seed=json.loads(g.input.read_text())['sequences'];rows=list(map(int,g.rows.split(',')));alts=list(map(int,g.alts.split(',')));z4=list(map(int,g.z4.split(',')));assert sum(x*x for x in rows)==sum(x*x for x in alts)==sum(x*x for x in z4)==334
 groups=defaultdict(list);target=0
 for d in range(1,84):target|=((sum(max(0,n-d) for n in L)//2)&1)<<(d-1)
 for k,n in enumerate(L):
  for i in range(n):
   sig=sum((((i<d)^(i>=n-d))<<(d-1)) for d in range(1,84));groups[sig].append((k,i))
 zero=groups.pop(0,[]);sigs=list(groups);assert len(sigs)==83 and all(len(groups[s])==4 for s in sigs)
 erows=[]
 for bit in range(83):erows.append([sum(((s>>bit)&1)<<j for j,s in enumerate(sigs)),(target>>bit)&1])
 rr=0;piv=[]
 for col in range(83):
  h=next(j for j in range(rr,83) if erows[j][0]>>col&1);erows[rr],erows[h]=erows[h],erows[rr]
  for j in range(83):
   if j!=rr and erows[j][0]>>col&1:erows[j][0]^=erows[rr][0];erows[j][1]^=erows[rr][1]
  piv.append(col);rr+=1
 want=[0]*83
 for j,c in enumerate(piv):want[c]=erows[j][1]
 m=cp_model.CpModel();x=[[m.new_bool_var(f'x_{k}_{i}') for i in range(n)] for k,n in enumerate(L)];one=m.new_bool_var('one');m.add(one==1)
 for j,sig in enumerate(sigs):
  lits=[x[k][i] for k,i in groups[sig]];m.add_bool_xor(lits if want[j] else lits+[one])
 targets=[]
 for k,n in enumerate(L):
  ev=(rows[k]+alts[k])//2;od=(rows[k]-alts[k])//2;u,v=z4[2*k:2*k+2];sums=((ev+u)//2,(od+v)//2,(ev-u)//2,(od-v)//2);lens=[len(range(c,n,4)) for c in range(4)];neg=[(lens[c]-sums[c])//2 for c in range(4)];targets.append(neg)
  for c in range(4):m.add(sum(x[k][c::4])==neg[c])
 changed=[x[k][i] if seed[k][i]==1 else x[k][i].Not() for k,n in enumerate(L) for i in range(n)];m.minimize(sum(changed))
 for k,n in enumerate(L):
  for i in range(n):m.add_hint(x[k][i],int(seed[k][i]==-1))
 s=cp_model.CpSolver();s.parameters.max_time_in_seconds=g.seconds;s.parameters.num_search_workers=g.workers;s.parameters.random_seed=668;print(json.dumps({'event':'built','classes':83,'zero_columns':zero,'target_negative_counts':targets,'elapsed_s':time.time()-st}),flush=True);status=s.solve(m);print(json.dumps({'event':'result','status':s.status_name(status),'objective':s.objective_value,'bound':s.best_objective_bound,'conflicts':s.num_conflicts,'branches':s.num_branches,'wall_time':s.wall_time}),flush=True)
 if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):return 2
 a=[[-1 if s.value(v) else 1 for v in row] for row in x];res=residual(a);mar=margins(a);chg=sum(a[k][i]!=seed[k][i] for k,n in enumerate(L) for i in range(n));assert mar==(rows,alts,z4) and not any(v%4 for v in res)
 out={'construction':'base sequences BS(84,83)','search':'agent compressed-class minimum-Hamming crossover','solved':not any(res),'independently_recomputed':True,'energy':sum(v*v for v in res),'l1':sum(map(abs,res)),'parity_bad':0,'hamming_changes':chg,'elapsed_s':time.time()-st,'row_sums':rows,'alternating_sums':alts,'z4_components':z4,'residual':res,'sequences':a};raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'event':'verified_projection','energy':out['energy'],'l1':out['l1'],'changes':chg,'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
