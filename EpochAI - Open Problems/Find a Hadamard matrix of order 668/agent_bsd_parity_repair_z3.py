"""Z3 parity/cardinality repair for fixed-margin BS(84,83) checkpoints."""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import z3

L=(84,84,83,83)
def residual(a):return [sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in a) for d in range(1,84)]
def margins(a):
 rows=[sum(x) for x in a];alts=[sum(v if i%2==0 else -v for i,v in enumerate(x)) for x in a];q=[]
 for x in a:q += [sum(v for i,v in enumerate(x) if i%4==0)-sum(v for i,v in enumerate(x) if i%4==2),sum(v for i,v in enumerate(x) if i%4==1)-sum(v for i,v in enumerate(x) if i%4==3)]
 return rows,alts,q
def xor_many(xs):
 xs=list(xs)
 while len(xs)>1:
  xs=[z3.Xor(xs[i],xs[i+1]) if i+1<len(xs) else xs[i] for i in range(0,len(xs),2)]
 return xs[0]
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=120);p.add_argument('--max-changes',type=int);p.add_argument('--output',type=Path,default=Path('agent_bsd_repair_z3_pb0.json'));g=p.parse_args();st=time.time();a=json.loads(g.input.read_text())['sequences'];r0=residual(a);before=margins(a)
 f=[[z3.Bool(f'f_{k}_{i}') for i in range(n)] for k,n in enumerate(L)];s=z3.Solver();s.set(timeout=int(g.seconds*1000))
 for k,x in enumerate(a):
  for c in range(4):
   pos=list(range(c,len(x),4));finalneg=[f[k][i] if x[i]==1 else z3.Not(f[k][i]) for i in pos];s.add(z3.PbEq([(v,1) for v in finalneg],sum(x[i]==-1 for i in pos)))
 for d in range(1,84):
  odd=set()
  for k,n in enumerate(L):
   for i in range(n-d):
    for key in ((k,i),(k,i+d)):
     if key in odd:odd.remove(key)
     else:odd.add(key)
  lits=[f[k][i] for k,i in sorted(odd)];want=bool((r0[d-1]//2)&1);s.add(xor_many(lits)==want)
 flat=[v for x in f for v in x]
 if g.max_changes is not None:s.add(z3.PbLe([(v,1) for v in flat],g.max_changes))
 print(json.dumps({'event':'built','max_changes':g.max_changes,'seed_pb':sum(x%4!=0 for x in r0),'assertions':len(s.assertions()),'elapsed_s':time.time()-st}),flush=True);status=s.check();print(json.dumps({'event':'result','status':str(status),'reason':s.reason_unknown(),'stats':str(s.statistics()),'elapsed_s':time.time()-st}),flush=True)
 if status!=z3.sat:return 2
 m=s.model();b=[[-x if z3.is_true(m.eval(f[k][i],model_completion=True)) else x for i,x in enumerate(row)] for k,row in enumerate(a)];rr=residual(b);after=margins(b);chg=[(k,i) for k,row in enumerate(f) for i,v in enumerate(row) if z3.is_true(m.eval(v,model_completion=True))]
 if before!=after or any(x%4 for x in rr):raise RuntimeError((before,after,rr))
 out={'construction':'base sequences BS(84,83)','search':'agent Z3 exact parity repair','solved':not any(rr),'independently_recomputed':True,'energy':sum(x*x for x in rr),'l1':sum(map(abs,rr)),'parity_bad':0,'changes':len(chg),'changed_positions':chg,'elapsed_s':time.time()-st,'row_sums':after[0],'alternating_sums':after[1],'z4_components':after[2],'residual':rr,'sequences':b};raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'event':'verified_parity0','energy':out['energy'],'l1':out['l1'],'changes':len(chg),'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
