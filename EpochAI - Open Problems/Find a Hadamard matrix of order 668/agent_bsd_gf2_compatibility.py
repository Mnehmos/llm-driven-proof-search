"""Enumerate z=i fibres and classify exact residual-mod-4 compatibility."""
from __future__ import annotations
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
L=(84,84,83,83)
def feasible_pairs(n,row,alt):
 lens=[len(range(c,n,4)) for c in range(4)];even=(row+alt)//2;odd=(row-alt)//2;out=[]
 for u in range(-n,n+1):
  if (even+u)%2:continue
  s0=(even+u)//2;s2=(even-u)//2
  if abs(s0)>lens[0] or abs(s2)>lens[2] or (lens[0]-s0)%2 or (lens[2]-s2)%2:continue
  for v in range(-n,n+1):
   if (odd+v)%2:continue
   s1=(odd+v)//2;s3=(odd-v)//2
   if abs(s1)>lens[1] or abs(s3)>lens[3] or (lens[1]-s1)%2 or (lens[3]-s3)%2:continue
   out.append((u,v,u*u+v*v,(s0,s1,s2,s3),lens))
 return out
def main():
 p=argparse.ArgumentParser();p.add_argument('--rows',default='10,8,-1,-13');p.add_argument('--alts',default='-2,-4,5,17');p.add_argument('--probe',default='-2,0,4,-4,-8,-11,8,-7');p.add_argument('--output',type=Path,default=Path('agent_bsd_gf2_compatibility.json'));g=p.parse_args();rows=tuple(map(int,g.rows.split(',')));alts=tuple(map(int,g.alts.split(',')));probe=tuple(map(int,g.probe.split(',')));assert len(rows)==len(alts)==4 and sum(x*x for x in rows)==sum(x*x for x in alts)==334
 # Absolute linear system: 83 autocorrelation parity rows + 16 residue-count parity rows.
 off=[];t=0
 for n in L:off.append(t);t+=n
 coeff=[];labels=[];base_rhs=0
 for d in range(1,84):
  m=0;terms=0
  for k,n in enumerate(L):
   for i in range(n-d):m^=1<<(off[k]+i);m^=1<<(off[k]+i+d);terms+=1
  coeff.append(m);labels.append(f'corr_shift_{d}');base_rhs|=((terms//2)&1)<<(d-1)
 for k,n in enumerate(L):
  for c in range(4):coeff.append(sum(1<<(off[k]+i) for i in range(c,n,4)));labels.append(f'residue_parity_{k}_{c}')
 work=[[m,1<<i] for i,m in enumerate(coeff)];rank=0
 for col in range(sum(L)):
  hit=next((j for j in range(rank,len(work)) if (work[j][0]>>col)&1),None)
  if hit is None:continue
  work[rank],work[hit]=work[hit],work[rank]
  for j in range(len(work)):
   if j!=rank and ((work[j][0]>>col)&1):work[j][0]^=work[rank][0];work[j][1]^=work[rank][1]
  rank+=1
 deps=[comb for m,comb in work if m==0];assert rank==95 and len(deps)==4
 opts=[feasible_pairs(n,r,a) for n,r,a in zip(L,rows,alts)]
 fibres=[]
 def rec(k,norm,z,negpar):
  if k==4:
   if norm!=334:return
   rhs=base_rhs
   for j,b in enumerate(negpar):rhs|=(b&1)<<(83+j)
   syn=sum(((rhs&dep).bit_count()&1)<<i for i,dep in enumerate(deps))
   fibres.append((tuple(z),syn));return
  for u,v,q,sums,lens in opts[k]:
   if norm+q>334:continue
   rec(k+1,norm+q,z+[u,v],negpar+[((lens[c]-sums[c])//2)&1 for c in range(4)])
 rec(0,0,[],[])
 fibres.sort();survivors=[list(z) for z,s in fibres if s==0];hist=Counter(s for z,s in fibres)
 def tuple_rhs(z):
  rhs=base_rhs
  for k in range(4):
   u,v=z[2*k:2*k+2];n=L[k];lens=[len(range(c,n,4)) for c in range(4)];ev=(rows[k]+alts[k])//2;od=(rows[k]-alts[k])//2;sums=((ev+u)//2,(od+v)//2,(ev-u)//2,(od-v)//2)
   for c in range(4):rhs|=(((lens[c]-sums[c])//2)&1)<<(83+4*k+c)
  return rhs
 prhs=tuple_rhs(probe);checks=[(prhs&d).bit_count()&1 for d in deps];contr=[]
 for slot,(dep,b) in enumerate(zip(deps,checks)):
  if b:contr.append({'reduced_zero_row':rank+slot,'rhs':1,'dependency_equations':[labels[j] for j in range(99) if (dep>>j)&1]})
 canonical=sorted(survivors,key=lambda z:(max(map(abs,z)),sum(map(abs,z)),z))[:64]
 out={'construction':'BS(84,83) GF(2) quartic-fibre filter','row_sums':rows,'alternating_sums':alts,'matrix_dimensions':[99,334],'coefficient_rank':rank,'dependency_count':len(deps),'z4_norm':334,'feasible_z4_fibres':len(fibres),'parity_compatible_fibres':len(survivors),'parity_incompatible_fibres':len(fibres)-len(survivors),'compatibility_syndrome_histogram':{str(k):v for k,v in sorted(hist.items())},'canonical_survivors':canonical,'all_survivors':survivors,'probe':{'z4':probe,'compatibility_syndrome':sum(b<<i for i,b in enumerate(checks)),'coefficient_rank':rank,'augmented_rank':rank+(1 if any(checks) else 0),'reduced_dependency_rhs':checks,'contradictory_reduced_rows':contr}}
 raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'event':'gf2_compatibility','matrix':[99,334],'rank':rank,'feasible':len(fibres),'compatible':len(survivors),'probe_syndrome':out['probe']['compatibility_syndrome'],'probe_augmented_rank':out['probe']['augmented_rank'],'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}));return 0
if __name__=='__main__':raise SystemExit(main())
