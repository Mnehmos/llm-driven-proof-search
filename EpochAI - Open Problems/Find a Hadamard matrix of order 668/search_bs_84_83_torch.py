"""CUDA-parallel row-preserving annealing for BS(84,83)."""

from __future__ import annotations
import argparse,json,time
from pathlib import Path
import torch

L=(84,84,83,83);OFF=(0,84,168,251)

def exact(a):return [sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in a) for d in range(1,84)]

def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=900);p.add_argument('--batch',type=int,default=4096);p.add_argument('--seed',type=int,default=671);p.add_argument('--input',type=Path,default=Path('Find a Hadamard matrix of order 668/bs_84_83_row_summary.json'));p.add_argument('--output',type=Path,default=Path('Find a Hadamard matrix of order 668/bs_84_83_torch_live.json'));p.add_argument('--strict-output',type=Path);p.add_argument('--strict-weight',type=float,default=16.0);a=p.parse_args()
 if not torch.cuda.is_available():raise RuntimeError('CUDA unavailable')
 torch.manual_seed(a.seed);torch.cuda.manual_seed_all(a.seed);data=json.loads(a.input.read_text(encoding='utf8'));seed=data['sequences'];rows=tuple(map(sum,seed));assert tuple(map(len,seed))==L and sum(x*x for x in rows)==334
 dev='cuda';flat=torch.tensor([v for x in seed for v in x],device=dev,dtype=torch.int8);pop=flat.repeat(a.batch,1);chain=torch.arange(a.batch,device=dev);guided=torch.arange(a.batch,device=dev)>=a.batch//2
 # Diversify every chain by row-preserving random swaps.
 for _ in range(32):
  k=torch.randint(4,(a.batch,),device=dev);n=torch.where(k<2,84,83);i=torch.randint(84,(a.batch,),device=dev)%n;j=torch.randint(84,(a.batch,),device=dev)%n;u=torch.tensor(OFF,device=dev)[k]+i;v=torch.tensor(OFF,device=dev)[k]+j;opp=pop[chain,u]!=pop[chain,v];pop[chain[opp],u[opp]]*=-1;pop[chain[opp],v[opp]]*=-1
 pop[0]=flat;pop[a.batch//2]=flat
 def evaluate(x):
  padded=torch.zeros((x.shape[0],4,256),device=dev,dtype=torch.float32)
  for k,(off,n) in enumerate(zip(OFF,L)):padded[:,k,:n]=x[:,off:off+n]
  spectrum=torch.fft.rfft(padded,dim=2);auto=torch.fft.irfft(spectrum.conj()*spectrum,n=256,dim=2)
  r=auto[:,:,1:84].sum(dim=1).round();e=(r*r).sum(dim=1);bad=(torch.remainder(r,4)!=0).sum(dim=1).float();alt=[];z4=[]
  for off,n in zip(OFF,L):
   q=x[:,off:off+n].float();alt.append((q*torch.where(torch.arange(n,device=dev)%2==0,1.0,-1.0)).sum(dim=1));z4.extend([q[:,0::4].sum(dim=1)-q[:,2::4].sum(dim=1),q[:,1::4].sum(dim=1)-q[:,3::4].sum(dim=1)])
  an=torch.stack(alt,dim=1).square().sum(dim=1);zn=torch.stack(z4,dim=1).square().sum(dim=1);penalty=64.0*bad+a.strict_weight*((an-334).abs()+(zn-334).abs());return e+torch.where(guided,penalty,torch.zeros_like(penalty)),e,r,bad,an,zn
 fit,energy,res,bad,altnorm,z4norm=evaluate(pop);best_raw=sum(x*x for x in exact(seed));seed_r=exact(seed);seed_alt=[sum((1 if i%2==0 else -1)*v for i,v in enumerate(s)) for s in seed];seed_z4=[v for s in seed for v in (sum(s[0::4])-sum(s[2::4]),sum(s[1::4])-sum(s[3::4]))];best_strict=sum(x*x for x in seed_r) if all(x%4==0 for x in seed_r) and sum(x*x for x in seed_alt)==334 and sum(x*x for x in seed_z4)==334 else 10**18;best_parity=10**18;started=time.time();gen=0
 while time.time()-started<a.seconds:
  proposal=pop.clone();swaps=1+(gen//500)%4
  for _ in range(swaps):
   k=torch.randint(4,(a.batch,),device=dev);n=torch.where(k<2,84,83);i=torch.randint(84,(a.batch,),device=dev)%n;j=torch.randint(84,(a.batch,),device=dev)%n;u=torch.tensor(OFF,device=dev)[k]+i;v=torch.tensor(OFF,device=dev)[k]+j;opp=proposal[chain,u]!=proposal[chain,v];proposal[chain[opp],u[opp]]*=-1;proposal[chain[opp],v[opp]]*=-1
  pf,pe,pr,pb,pan,pzn=evaluate(proposal);phase=(gen%2000)/2000;temp=1800*(.001**phase)+.5;delta=pf-fit;accept=(delta<=0)|(torch.rand(a.batch,device=dev)<torch.exp(-delta/temp));pop=torch.where(accept[:,None],proposal,pop);fit=torch.where(accept,pf,fit);energy=torch.where(accept,pe,energy);res=torch.where(accept[:,None],pr,res);bad=torch.where(accept,pb,bad);altnorm=torch.where(accept,pan,altnorm);z4norm=torch.where(accept,pzn,z4norm)
  value,idx=energy.min(dim=0);candidate=int(value.item())
  if candidate<best_raw:
   signs=pop[int(idx.item())].cpu().tolist();seq=[signs[0:84],signs[84:168],signs[168:251],signs[251:334]];rr=exact(seq);checked=sum(x*x for x in rr);assert checked==candidate and tuple(map(sum,seq))==rows;best_raw=checked;a.output.write_text(json.dumps({'construction':'base sequences BS(84,83)','solver':'CUDA row annealing','solved':checked==0,'energy':checked,'parity_bad':sum(x%4!=0 for x in rr),'row_sums':rows,'generation':gen,'elapsed_s':time.time()-started,'residual':rr,'sequences':seq},indent=2)+'\n',encoding='utf8');print(json.dumps({'event':'best_raw','energy':checked,'bad':sum(x%4!=0 for x in rr),'gen':gen,'elapsed_s':time.time()-started}),flush=True)
   if checked==0:return 0
  mask=bad==0
  if bool(mask.any()):
   vals=torch.where(mask,energy,torch.full_like(energy,float('inf')));value,idx=vals.min(dim=0);candidate=int(value.item())
   if candidate<best_parity:best_parity=candidate;print(json.dumps({'event':'best_parity','energy':candidate,'gen':gen,'elapsed_s':time.time()-started}),flush=True)
  strict=mask&(altnorm==334)&(z4norm==334)
  if bool(strict.any()):
   vals=torch.where(strict,energy,torch.full_like(energy,float('inf')));value,idx=vals.min(dim=0);candidate=int(value.item())
   if candidate<best_strict:
    signs=pop[int(idx.item())].cpu().tolist();seq=[signs[0:84],signs[84:168],signs[168:251],signs[251:334]];rr=exact(seq);aa=[sum((1 if i%2==0 else -1)*v for i,v in enumerate(s)) for s in seq];zz=[v for s in seq for v in (sum(s[0::4])-sum(s[2::4]),sum(s[1::4])-sum(s[3::4]))];checked=sum(x*x for x in rr);assert checked==candidate and all(x%4==0 for x in rr) and sum(x*x for x in aa)==334 and sum(x*x for x in zz)==334;best_strict=checked;target=a.strict_output or a.output;target.write_text(json.dumps({'construction':'base sequences BS(84,83)','solver':'CUDA strict-Fourier row annealing','solved':checked==0,'independently_recomputed':True,'energy':checked,'l1':sum(map(abs,rr)),'parity_bad':0,'row_sums':rows,'alternating_sums':aa,'z4_components':zz,'generation':gen,'elapsed_s':time.time()-started,'residual':rr,'sequences':seq},indent=2)+'\n',encoding='utf8');print(json.dumps({'event':'best_strict','energy':checked,'gen':gen,'elapsed_s':time.time()-started}),flush=True)
  if gen%500==499:
   torch.cuda.synchronize();print(json.dumps({'event':'progress','gen':gen+1,'best_raw':best_raw,'best_parity':best_parity,'best_strict':best_strict,'elapsed_s':time.time()-started}),flush=True)
  gen+=1
 print(json.dumps({'event':'result','solved':False,'best_raw':best_raw,'best_parity':best_parity,'best_strict':best_strict,'generations':gen,'elapsed_s':time.time()-started}),flush=True);return 2
if __name__=='__main__':raise SystemExit(main())
