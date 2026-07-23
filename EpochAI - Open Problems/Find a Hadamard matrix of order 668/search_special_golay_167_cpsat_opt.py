"""Optimize L1 correlation error in the reduced 85-generator special family."""
from __future__ import annotations
import argparse,json,time
from pathlib import Path
from ortools.sat.python import cp_model
def expand(r):return [1 if j%2==0 else -1 for j,n in enumerate(r) for _ in range(n)]
Q=expand([83,2,81,1]);F=[1]*84+[-1]*83
def exact(s):return [sum(s[i]*s[i+d] for i in range(167-d) if F[i]==F[i+d] and Q[i]==Q[i+d]) for d in range(1,84)]
def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=900);p.add_argument('--workers',type=int,default=4);p.add_argument('--seed',type=int,default=675);p.add_argument('--input',type=Path,default=Path('Find a Hadamard matrix of order 668/special_golay_167_native_summary.json'));p.add_argument('--output',type=Path,default=Path('Find a Hadamard matrix of order 668/special_golay_167_cpsat_opt_summary.json'));a=p.parse_args();started=time.time();base=json.loads(a.input.read_text(encoding='utf8'))['s']
 if base[0]==-1:base[:84]=[-x for x in base[:84]]
 if base[84]==-1:base[84:]=[-x for x in base[84:]]
 group=[-1]*167;g=0
 for i in range(41):group[i]=group[82-i]=g;g+=1
 for i in range(41):group[84+i]=group[166-i]=g;g+=1
 for i in (41,83,125):group[i]=g;g+=1
 m=cp_model.CpModel();u=[m.new_bool_var(f'u_{i}') for i in range(85)];m.add(u[group[0]]==0);m.add(u[group[84]]==0);pair={}
 def px(x,y):
  if x>y:x,y=y,x
  if (x,y) not in pair:
   v=m.new_bool_var(f'p_{x}_{y}');m.add_bool_xor([u[x],u[y],v.Not()]);pair[x,y]=v
  return pair[x,y]
 errors=[]
 for d in range(1,84):
  terms=[];fixed=0;count=0
  for i in range(167-d):
   j=i+d
   if F[i]!=F[j] or Q[i]!=Q[j]:continue
   count+=1;c=base[i]!=base[j];x,y=group[i],group[j]
   if x==y:fixed+=int(c)
   else:
    v=px(x,y);terms.append(v.Not() if c else v)
  if terms:
   delta=m.new_int_var(-count,count,f'd_{d}');err=m.new_int_var(0,count,f'e_{d}');m.add(delta==sum(terms)+fixed-count//2);m.add_abs_equality(err,delta);errors.append(err)
 def signs(indices,qq=False):return sum(base[i]*(Q[i] if qq else 1)*(1-2*u[group[i]]) for i in indices)
 sl=m.new_int_var(-84,84,'sl');sr=m.new_int_var(-83,83,'sr');tl=m.new_int_var(-84,84,'tl');tr=m.new_int_var(-83,83,'tr');m.add(sl==signs(range(84)));m.add(sr==signs(range(84,167)));m.add(tl==signs(range(84),True));m.add(tr==signs(range(84,167),True))
 tuples=[(x,y,z,w) for x in range(-18,19,2) for y in range(-17,18,2) for z in range(-18,19,2) for w in range(-17,18,2) if x*x+y*y+z*z+w*w==334 and abs(z-x)==2 and w-y in (-4,0)];m.add_allowed_assignments([sl,sr,tl,tr],tuples);m.minimize(sum(errors));
 for v in u:m.add_hint(v,0)
 class SaveBest(cp_model.CpSolverSolutionCallback):
  def __init__(self):super().__init__();self.best=10**9
  def on_solution_callback(self):
   objective=int(self.objective_value)
   if objective>=self.best:return
   self.best=objective;uv=[self.value(v) for v in u];ss=[base[i]*(-1 if uv[group[i]] else 1) for i in range(167)];rr=exact(ss);payload={'construction':'special Golay quadruple length 167','solver':'OR-Tools CP-SAT reduced L1 optimization','solved':not any(rr),'objective_l1_difference':sum(abs(x)//2 for x in rr),'energy_normalized':sum(x*x for x in rr),'elapsed_s':time.time()-started,'residual_divided_by_4':rr,'s':ss};a.output.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf8')
 solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=a.seconds;solver.parameters.num_workers=a.workers;solver.parameters.random_seed=a.seed;solver.parameters.symmetry_level=3;solver.parameters.log_search_progress=True
 print(json.dumps({'event':'built','generator_variables':85,'shared_pair_xors':len(pair),'error_variables':len(errors),'row_sum_tuples':len(tuples)}),flush=True);status=solver.solve(m,SaveBest());print(json.dumps({'event':'result','status':solver.status_name(status),'objective':solver.objective_value if status in (cp_model.OPTIMAL,cp_model.FEASIBLE) else None,'bound':solver.best_objective_bound,'elapsed_s':time.time()-started}),flush=True)
 if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):return 2
 uv=[solver.value(v) for v in u];s=[base[i]*(-1 if uv[group[i]] else 1) for i in range(167)];r=exact(s);energy=sum(x*x for x in r);payload={'construction':'special Golay quadruple length 167','solver':'OR-Tools CP-SAT reduced L1 optimization','solved':energy==0,'objective_l1_difference':sum(abs(x)//2 for x in r),'energy_normalized':energy,'elapsed_s':time.time()-started,'residual_divided_by_4':r,'s':s};a.output.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf8');print(json.dumps({'event':'checked_candidate','energy':energy,'l1':sum(abs(x) for x in r),'output':str(a.output)}),flush=True);return 0 if energy==0 else 2
if __name__=='__main__':raise SystemExit(main())
