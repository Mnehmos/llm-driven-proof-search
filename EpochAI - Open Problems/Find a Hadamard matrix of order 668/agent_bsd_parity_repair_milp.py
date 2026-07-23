"""HiGHS MILP for minimum-change parity repair in a fixed quartic BS fibre."""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import lil_matrix
L=(84,84,83,83);N=sum(L)
def residual(a):return [sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in a) for d in range(1,84)]
def margins(a):
 rows=[sum(x) for x in a];alts=[sum(v if i%2==0 else -v for i,v in enumerate(x)) for x in a];q=[]
 for x in a:q += [sum(v for i,v in enumerate(x) if i%4==0)-sum(v for i,v in enumerate(x) if i%4==2),sum(v for i,v in enumerate(x) if i%4==1)-sum(v for i,v in enumerate(x) if i%4==3)]
 return rows,alts,q
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=300);p.add_argument('--max-changes',type=int);p.add_argument('--output',type=Path,default=Path('agent_bsd_repair_milp_pb0.json'));g=p.parse_args();st=time.time();a=json.loads(g.input.read_text())['sequences'];r0=residual(a);before=margins(a);off=np.cumsum([0,*L[:-1]])
 # 83 parity equations plus 16 exact residue-balance equations.
 mat=lil_matrix((99,N+83),dtype=float);rhs=np.zeros(99);row=0
 for d in range(1,84):
  odd=set()
  for k,n in enumerate(L):
   for i in range(n-d):
    for key in (int(off[k]+i),int(off[k]+i+d)):
     if key in odd:odd.remove(key)
     else:odd.add(key)
  for j in odd:mat[row,j]=1
  mat[row,N+d-1]=-2;rhs[row]=(r0[d-1]//2)&1;row+=1
 for k,x in enumerate(a):
  for c4 in range(4):
   for i in range(c4,len(x),4):mat[row,int(off[k]+i)]=1 if x[i]==1 else -1
   row+=1
 assert row==99
 c=np.r_[np.ones(N),np.zeros(83)];lo=np.r_[np.zeros(N),np.zeros(83)];hi=np.r_[np.ones(N),np.full(83,N/2)]
 cons=[LinearConstraint(mat.tocsr(),rhs,rhs)]
 if g.max_changes is not None:
  cap=lil_matrix((1,N+83));cap[0,:N]=1;cons.append(LinearConstraint(cap.tocsr(),-np.inf,g.max_changes))
 print(json.dumps({'event':'built','variables':N+83,'binary':N,'integer_slack':83,'constraints':99+(g.max_changes is not None),'seed_pb':sum(x%4!=0 for x in r0),'elapsed_s':time.time()-st}),flush=True)
 res=milp(c,integrality=np.ones(N+83),bounds=Bounds(lo,hi),constraints=cons,options={'time_limit':g.seconds,'mip_rel_gap':0.0,'presolve':True})
 print(json.dumps({'event':'result','success':bool(res.success),'status':int(res.status),'message':str(res.message),'objective':None if res.fun is None else float(res.fun),'bound':getattr(res,'mip_dual_bound',None),'gap':getattr(res,'mip_gap',None),'nodes':getattr(res,'mip_node_count',None),'elapsed_s':time.time()-st}),flush=True)
 if res.x is None:return 2
 flips=np.rint(res.x[:N]).astype(int);b=[]
 for k,x in enumerate(a):b.append([-v if flips[int(off[k]+i)] else v for i,v in enumerate(x)])
 rr=residual(b);after=margins(b);chg=[(k,i) for k,x in enumerate(a) for i in range(len(x)) if flips[int(off[k]+i)]]
 if before!=after or any(x%4 for x in rr):raise RuntimeError((before,after,rr,mat@np.rint(res.x)-rhs))
 out={'construction':'base sequences BS(84,83)','search':'agent HiGHS MILP exact parity repair','solved':not any(rr),'independently_recomputed':True,'energy':sum(x*x for x in rr),'l1':sum(map(abs,rr)),'parity_bad':0,'changes':len(chg),'changed_positions':chg,'elapsed_s':time.time()-st,'row_sums':after[0],'alternating_sums':after[1],'z4_components':after[2],'residual':rr,'sequences':b};raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'event':'verified_parity0','energy':out['energy'],'l1':out['l1'],'changes':len(chg),'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
