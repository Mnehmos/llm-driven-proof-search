"""Reduced exact CP-SAT model for the parity-feasible special Golay space.

The 167 signs are parameterized by 85 local nullspace generators (82 mirrored
pairs and three centers). Pair-XOR variables are shared by generator pair, so
repeated correlation terms do not create repeated Boolean variables.
"""

from __future__ import annotations
import argparse,json,time
from pathlib import Path
from ortools.sat.python import cp_model

def expand(runs):return [1 if j%2==0 else -1 for j,n in enumerate(runs) for _ in range(n)]
Q=expand([83,2,81,1]);F=[1]*84+[-1]*83
def exact(s):return [sum(s[i]*s[i+d] for i in range(167-d) if F[i]==F[i+d] and Q[i]==Q[i+d]) for d in range(1,84)]

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=900);p.add_argument('--workers',type=int,default=4);p.add_argument('--seed',type=int,default=672);p.add_argument('--input',type=Path,default=Path('Find a Hadamard matrix of order 668/special_golay_167_native_summary.json'));p.add_argument('--output',type=Path,default=Path('Find a Hadamard matrix of order 668/special_golay_167_candidate.json'));a=p.parse_args();started=time.time()
 base=json.loads(a.input.read_text(encoding='utf-8'))['s']
 if base[0]==-1:base[:84]=[-x for x in base[:84]]
 if base[84]==-1:base[84:]=[-x for x in base[84:]]
 group=[-1]*167;g=0
 for i in range(41):group[i]=group[82-i]=g;g+=1
 for i in range(41):group[84+i]=group[166-i]=g;g+=1
 for i in (41,83,125):group[i]=g;g+=1
 assert g==85 and min(group)>=0 and all(x%4==0 for x in exact(base))
 m=cp_model.CpModel();u=[m.new_bool_var(f'u_{i}') for i in range(85)];m.add(u[group[0]]==0);m.add(u[group[84]]==0);pair={}
 def pair_xor(x,y):
  if x>y:x,y=y,x
  key=(x,y)
  if key not in pair:
   v=m.new_bool_var(f'p_{x}_{y}');m.add_bool_xor([u[x],u[y],v.Not()]);pair[key]=v
  return pair[key]
 for d in range(1,84):
  terms=[];fixed=0
  for i in range(167-d):
   j=i+d
   if F[i]!=F[j] or Q[i]!=Q[j]:continue
   c=base[i]!=base[j];x,y=group[i],group[j]
   if x==y:fixed+=int(c)
   else:
    v=pair_xor(x,y);terms.append(v.Not() if c else v)
  m.add(sum(terms)==(sum(1 for i in range(167-d) if F[i]==F[i+d] and Q[i]==Q[i+d])//2-fixed))
 # Only eight row-sum tuples survive q's three negative positions and the two
 # canonical half-sign normalizations.
 def sign_sum(indices,extra=None):
  return sum((base[i] if extra is None else base[i]*extra[i])*(1-2*u[group[i]]) for i in indices)
 sl=m.new_int_var(-84,84,'sl');sr=m.new_int_var(-83,83,'sr');tl=m.new_int_var(-84,84,'tl');tr=m.new_int_var(-83,83,'tr')
 m.add(sl==sign_sum(range(84)));m.add(sr==sign_sum(range(84,167)));m.add(tl==sign_sum(range(84),Q));m.add(tr==sign_sum(range(84,167),Q))
 tuples=[(x,y,z,w) for x in range(-18,19,2) for y in range(-17,18,2) for z in range(-18,19,2) for w in range(-17,18,2) if x*x+y*y+z*z+w*w==334 and abs(z-x)==2 and w-y in (-4,0)]
 m.add_allowed_assignments([sl,sr,tl,tr],tuples)
 for v in u:m.add_hint(v,0)
 solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=a.seconds;solver.parameters.num_workers=a.workers;solver.parameters.random_seed=a.seed;solver.parameters.symmetry_level=3;solver.parameters.log_search_progress=True
 print(json.dumps({'event':'built','generator_variables':85,'shared_pair_xors':len(pair),'row_sum_tuples':len(tuples),'elapsed_s':time.time()-started}),flush=True)
 status=solver.solve(m);print(json.dumps({'event':'result','status':solver.status_name(status),'elapsed_s':time.time()-started,'conflicts':solver.num_conflicts,'branches':solver.num_branches}),flush=True)
 if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):return 2
 vals=[solver.value(v) for v in u];s=[base[i]*(-1 if vals[group[i]] else 1) for i in range(167)];r=exact(s)
 if any(r):raise RuntimeError(r)
 seqs=[s,[x*f for x,f in zip(s,F)],[x*q for x,q in zip(s,Q)],[x*q*f for x,q,f in zip(s,Q,F)]];a.output.write_text(json.dumps({'construction':'special Golay quadruple length 167','solver':'OR-Tools CP-SAT reduced parity model','elapsed_s':time.time()-started,'residual':[0]*166,'sequences':seqs},indent=2)+'\n',encoding='utf-8');print(json.dumps({'event':'verified_witness','output':str(a.output),'row_sums':[sum(x) for x in seqs]}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
