"""Reduced 85-generator Z3/PB model for the special Golay H668 route."""
from __future__ import annotations
import argparse,json,time
from collections import Counter
from pathlib import Path
import z3
def expand(r):return [1 if j%2==0 else -1 for j,n in enumerate(r) for _ in range(n)]
Q=expand([83,2,81,1]);F=[1]*84+[-1]*83
def exact(s):return [sum(s[i]*s[i+d] for i in range(167-d) if F[i]==F[i+d] and Q[i]==Q[i+d]) for d in range(1,84)]
def main():
 p=argparse.ArgumentParser();p.add_argument('--timeout-ms',type=int,default=900000);p.add_argument('--threads',type=int,default=4);p.add_argument('--seed',type=int,default=673);p.add_argument('--input',type=Path,default=Path('Find a Hadamard matrix of order 668/special_golay_167_native_summary.json'));p.add_argument('--output',type=Path,default=Path('Find a Hadamard matrix of order 668/special_golay_167_candidate.json'));a=p.parse_args();started=time.time();base=json.loads(a.input.read_text(encoding='utf8'))['s']
 if base[0]==-1:base[:84]=[-x for x in base[:84]]
 if base[84]==-1:base[84:]=[-x for x in base[84:]]
 group=[-1]*167;g=0
 for i in range(41):group[i]=group[82-i]=g;g+=1
 for i in range(41):group[84+i]=group[166-i]=g;g+=1
 for i in (41,83,125):group[i]=g;g+=1
 u=[z3.Bool(f'u_{i}') for i in range(85)];solver=z3.Solver();solver.set('timeout',a.timeout_ms);solver.set('threads',a.threads);solver.set('random_seed',a.seed);solver.set('phase_selection',5);solver.add(z3.Not(u[group[0]]),z3.Not(u[group[84]]))
 active=0
 for d in range(1,84):
  terms=Counter();fixed=0;count=0
  for i in range(167-d):
   j=i+d
   if F[i]!=F[j] or Q[i]!=Q[j]:continue
   count+=1;c=base[i]!=base[j];x,y=sorted((group[i],group[j]))
   if x==y:fixed+=int(c)
   else:terms[(x,y,c)]+=1
  pairs={(x,y) for x,y,_ in terms};constant=fixed+sum(terms[(x,y,True)] for x,y in pairs);pb=[]
  for x,y in pairs:
   coeff=terms[(x,y,False)]-terms[(x,y,True)];v=z3.Xor(u[x],u[y])
   if coeff>0:pb.append((v,coeff))
   elif coeff<0:pb.append((z3.Not(v),-coeff));constant+=coeff
  if pb:solver.add(z3.PbEq(pb,count//2-constant));active+=1
 def sign_expr(indices,with_q=False):return z3.Sum([base[i]*(Q[i] if with_q else 1)*(1-2*z3.If(u[group[i]],1,0)) for i in indices])
 rows=[sign_expr(range(84)),sign_expr(range(84,167)),sign_expr(range(84),True),sign_expr(range(84,167),True)]
 tuples=[(x,y,z,w) for x in range(-18,19,2) for y in range(-17,18,2) for z in range(-18,19,2) for w in range(-17,18,2) if x*x+y*y+z*z+w*w==334 and abs(z-x)==2 and w-y in (-4,0)]
 solver.add(z3.Or([z3.And([rows[i]==t[i] for i in range(4)]) for t in tuples]));print(json.dumps({'event':'built','generator_variables':85,'active_correlations':active,'row_sum_tuples':len(tuples),'assertions':len(solver.assertions()),'elapsed_s':time.time()-started}),flush=True)
 result=solver.check();print(json.dumps({'event':'result','result':str(result),'elapsed_s':time.time()-started,'reason_unknown':solver.reason_unknown() if result==z3.unknown else None}),flush=True)
 if result!=z3.sat:return 2 if result==z3.unknown else 1
 model=solver.model();uv=[z3.is_true(model.eval(v,model_completion=True)) for v in u];s=[base[i]*(-1 if uv[group[i]] else 1) for i in range(167)];r=exact(s)
 if any(r):raise RuntimeError(r)
 seq=[s,[x*f for x,f in zip(s,F)],[x*q for x,q in zip(s,Q)],[x*q*f for x,q,f in zip(s,Q,F)]];a.output.write_text(json.dumps({'construction':'special Golay quadruple length 167','solver':'Z3 reduced parity model','elapsed_s':time.time()-started,'residual':[0]*166,'sequences':seq},indent=2)+'\n',encoding='utf8');print(json.dumps({'event':'verified_witness','output':str(a.output),'row_sums':[sum(x) for x in seq]}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
