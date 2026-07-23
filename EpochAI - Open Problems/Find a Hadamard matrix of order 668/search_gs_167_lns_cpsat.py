"""Exact CP-SAT disjoint-swap neighborhoods for four cyclic GS sequences."""
from __future__ import annotations
import argparse,json,random,time
from pathlib import Path
import numpy as np
from ortools.sat.python import cp_model
N=167;H=83
def corr(x):
 y=x.astype(np.int16,copy=False);return np.asarray([int(y@np.roll(y,-d)) for d in range(1,H+1)],dtype=np.int64)
def residual(a):return sum((corr(x) for x in a),np.zeros(H,dtype=np.int64))
def moves_for(a,seed):
 r=random.Random(seed);out=[]
 for k,x in enumerate(a):
  p=np.flatnonzero(x==1).tolist();m=np.flatnonzero(x==-1).tolist();r.shuffle(p);r.shuffle(m);out.extend((k,(i,j)) for i,j in zip(p,m))
 return out
def flip(x,pos):y=x.copy();y[list(pos)]*=-1;return y
def solve_round(a,seconds,workers,seed):
 started=time.time();r0=residual(a);moves=moves_for(a,seed);base=[corr(x) for x in a];single=[]
 for k,pos in moves:single.append(corr(flip(a[k],pos))-base[k])
 inter=[]
 for i,(ki,pi) in enumerate(moves):
  for j in range(i+1,len(moves)):
   kj,pj=moves[j]
   if ki!=kj:continue
   c=corr(flip(flip(a[ki],pi),pj))-base[ki]-single[i]-single[j]
   if np.any(c):inter.append((i,j,c))
 model=cp_model.CpModel();z=[model.new_bool_var(f'z{i}') for i in range(len(moves))];pairs=[]
 for i,j,c in inter:
  w=model.new_bool_var(f'w{i}_{j}');model.add_multiplication_equality(w,[z[i],z[j]]);pairs.append((w,c))
 for d in range(H):model.add(int(r0[d])+sum(int(single[i][d])*z[i] for i in range(len(z)) if single[i][d])+sum(int(c[d])*w for w,c in pairs if c[d])==0)
 for v in z:model.add_hint(v,0)
 s=cp_model.CpSolver();s.parameters.max_time_in_seconds=seconds;s.parameters.num_search_workers=workers;s.parameters.random_seed=seed;status=s.solve(model);name=s.status_name(status);st={'status':name,'moves':len(moves),'pair_variables':len(pairs),'elapsed_s':time.time()-started,'conflicts':s.num_conflicts,'branches':s.num_branches,'wall_time':s.wall_time};print(json.dumps({'event':'round','seed':seed,**st}),flush=True)
 if status not in(cp_model.OPTIMAL,cp_model.FEASIBLE):return None,st
 b=[x.copy() for x in a];sel=[]
 for i,(k,pos) in enumerate(moves):
  if s.value(z[i]):b[k][list(pos)]*=-1;sel.append(i)
 if np.any(residual(b)):raise RuntimeError('quadratic model drift')
 if [int(x.sum()) for x in b]!=[int(x.sum()) for x in a]:raise RuntimeError('row drift')
 return b,{**st,'selected_moves':sel}
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=900);p.add_argument('--round-seconds',type=float,default=300);p.add_argument('--workers',type=int,default=8);p.add_argument('--seed',type=int,default=6680);p.add_argument('--output',type=Path,default=Path('gs_167_lns_candidate.json'));q=p.parse_args();data=json.loads(q.input.read_text(encoding='utf8'));a=[np.asarray(x,dtype=np.int8) for x in data['sequences']];rows=[int(x.sum()) for x in a]
 if len(a)!=4 or any(len(x)!=N for x in a) or sum(x*x for x in rows)!=668:raise ValueError('cyclic GS row identity failure')
 deadline=time.time()+q.seconds;hist=[];round_no=0
 while time.time()<deadline:
  b,st=solve_round(a,min(q.round_seconds,max(1,deadline-time.time())),q.workers,q.seed+round_no);hist.append(st);round_no+=1
  if b is None:continue
  rr=residual(b);payload={'construction':'cyclic Goethals-Seidel order 167','solver':'CP-SAT exact disjoint-swap LNS','solved':True,'row_sums':[int(x.sum()) for x in b],'residual':rr.tolist(),'history':hist,'sequences':[x.astype(int).tolist() for x in b]};q.output.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf8');print(json.dumps({'event':'verified_witness','output':str(q.output)}),flush=True);return 0
 print(json.dumps({'event':'result','solved':False,'rounds':round_no,'history':hist}),flush=True);return 2
if __name__=='__main__':raise SystemExit(main())
