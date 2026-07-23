"""Minimum-Hamming TT(56) projection to exact z=1,-1,i and mod-4 fibres."""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
from ortools.sat.python import cp_model
L=(56,56,56,55);W=(1,1,2,2)
def read(path):
 q=json.loads(path.read_text())['sequences'];return [list(map(int,q[k][:L[k]])) for k in range(4)]
def residual(a):return [sum(W[k]*sum(a[k][i]*a[k][i+d] for i in range(L[k]-d)) for k in range(4)) for d in range(1,56)]
def margins(a):
 rows=[sum(x) for x in a];alts=[sum(v if i%2==0 else-v for i,v in enumerate(x)) for x in a];z=[v for x in a for v in(sum(x[0::4])-sum(x[2::4]),sum(x[1::4])-sum(x[3::4]))];return rows,alts,z
def norm4(x):return sum(W[k]*x[k]*x[k] for k in range(4))
def norm8(x):return sum(W[k]*(x[2*k]**2+x[2*k+1]**2) for k in range(4))
def main():
 p=argparse.ArgumentParser();p.add_argument('seed',type=Path);p.add_argument('--compatibility',type=Path,default=Path('agent_btt_fourier_compatibility.json'));p.add_argument('--target-index',type=int,default=0);p.add_argument('--seconds',type=float,default=300);p.add_argument('--workers',type=int,default=8);p.add_argument('--feasible',action='store_true');p.add_argument('--output',type=Path,default=Path('agent_btt_parity_projection.json'));g=p.parse_args();started=time.time();a0=read(g.seed);data=json.loads(g.compatibility.read_text());target=data['top_targets'][g.target_index];neg=target['negative_counts'];z_target=target['z4'];rows,alts,_=margins(a0)
 m=cp_model.CpModel();x=[[m.new_bool_var(f'x_{k}_{i}') for i in range(L[k])]for k in range(4)];one=m.new_bool_var('one');m.add(one==1)
 for k in range(4):
  for c in range(4):m.add(sum(x[k][c::4])==neg[k][c])
 for d in range(1,56):
  lits=[]
  for k in range(2):
   for i in range(L[k]):
    if (i<d)^(i>=L[k]-d):lits.append(x[k][i])
  constant=2*(56-d)+2*((56-d)+max(0,55-d));rhs=(constant//2)&1;m.add_bool_xor(lits if rhs else lits+[one])
 changed=[]
 for k in range(4):
  for i in range(L[k]):changed.append(x[k][i] if a0[k][i]==1 else x[k][i].Not());m.add_hint(x[k][i],int(a0[k][i]<0))
 if not g.feasible:m.minimize(sum(changed))
 s=cp_model.CpSolver();s.parameters.max_time_in_seconds=g.seconds;s.parameters.num_search_workers=g.workers;s.parameters.random_seed=560334;status=s.solve(m);print(json.dumps({'event':'solve','status':s.status_name(status),'objective':s.objective_value,'bound':s.best_objective_bound,'wall_s':s.wall_time}),flush=True)
 if status not in(cp_model.OPTIMAL,cp_model.FEASIBLE):return 2
 a=[[-1 if s.value(v)else 1 for v in row]for row in x];r=residual(a);mar=margins(a);assert mar==(rows,alts,z_target);assert norm4(rows)==norm4(alts)==norm8(z_target)==334;assert all(v%4==0 for v in r);chg=sum(a[k][i]!=a0[k][i] for k in range(4)for i in range(L[k]));out={'construction':'TT(56)','search':'agent exact three-Fourier-margin GF(2) projection','solved':not any(r),'independently_recomputed':True,'weights':W,'lengths':L,'energy':sum(v*v for v in r),'l1':sum(map(abs,r)),'parity_bad':0,'hamming_changes':chg,'target_index':g.target_index,'elapsed_s':time.time()-started,'row_sums':rows,'alternating_row_sums':alts,'z4_components':z_target,'row_norm':norm4(rows),'alternating_norm':norm4(alts),'z4_norm':norm8(z_target),'residual':r,'sequences':a};raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'event':'verified','energy':out['energy'],'l1':out['l1'],'changes':chg,'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}));return 0
if __name__=='__main__':raise SystemExit(main())
