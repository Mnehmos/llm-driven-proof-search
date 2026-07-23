"""Multiobjective/multi-swap hard-cap search for SDS(167;73,76;66)."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch
from agent_gspec_pair_psd_gpu import exact,proposal

N,H=167,83
def measures(x):
 f=torch.fft.rfft(x,dim=2);ps=f.real.square()+f.imag.square();ac=torch.fft.irfft(ps.sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]-2).long();over=torch.relu(ps[:,:,1:]-332.0);return r,(r*r).sum(1),over.amax((1,2))
def objective(r,w,alpha):
 z=r.float();return (w*z.square()).sum(1)+alpha*(w*z.abs()).sum(1)
def profiles(batch,dev):
 m=64;w=torch.exp(.7*torch.randn(m,H,device=dev));
 for j in range(m//2):w[j,torch.randperm(H,device=dev)[:8+j%13]]*=4
 w/=w.mean(1,keepdim=True);ids=torch.arange(batch,device=dev)%m;alpha=torch.tensor([0.,1.,2.,4.,8.,16.,24.,32.],device=dev)[torch.arange(batch,device=dev)%8];return w[ids],alpha
def main():
 p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('--seconds',type=float,default=300);p.add_argument('--batch',type=int,default=8192);p.add_argument('--steps',type=int,default=10000);p.add_argument('--temp-high',type=float,default=5000);p.add_argument('--temp-low',type=float,default=.02);p.add_argument('--seed',type=int,default=332169);p.add_argument('--prefix',default='agent_gspec_pair_hardcap_multi');q=p.parse_args()
 if not torch.cuda.is_available():raise SystemExit('CUDA unavailable')
 torch.manual_seed(q.seed);dev=torch.device('cuda');src=np.asarray(json.loads(Path(q.input).read_text())['sequences'],np.int8)[:2];best=src.copy();start=time.time();rep=exact(best,0,0,0,'hardcap_multi');
 if rep['psd_over_count']:raise ValueError('input violates PSD cap')
 key=(rep['energy'],rep['l1'],rep['nonzero']);samples=0;cycles=0;print(json.dumps({'event':'seed','key':key,'rows':rep['row_sums']}),flush=True)
 while key[0] and time.time()-start<q.seconds:
  cycles+=1;x=torch.from_numpy(best).to(dev).float()[None].expand(q.batch,-1,-1).clone();w,alpha=profiles(q.batch,dev);r,e,mx=measures(x);score=objective(r,w,alpha)
  for step in range(q.steps):
   if step%64==0 and time.time()-start>=q.seconds:break
   roll=int(torch.randint(1000,(1,),device=dev));arity=1 if roll<750 else 2 if roll<950 else 4;y=x
   for _ in range(arity):y=proposal(y)
   nr,ne,nmx=measures(y);ns=objective(nr,w,alpha);samples+=q.batch;phase=step/max(1,q.steps-1);temp=q.temp_high*(q.temp_low/q.temp_high)**phase;delta=ns-score;acc=(nmx<.02)&((delta<=0)|(torch.rand(q.batch,device=dev)<torch.exp(-delta/temp)));x[acc]=y[acc];r[acc]=nr[acc];e[acc]=ne[acc];score[acc]=ns[acc]
   ce=int(e.min())
   if ce<=key[0]:
    ids=torch.nonzero(e==ce).flatten();l1=r[ids].abs().sum(1);j=int(ids[int(l1.argmin())]);cand=x[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-start,samples,cycles,'hardcap_multi');nk=(chk['energy'],chk['l1'],chk['nonzero']);assert chk['psd_over_count']==0 and nk[0]==ce
    if nk<key:
     best,key,rep=cand,nk,chk;Path(q.prefix+'_live.json').write_text(json.dumps(chk,separators=(',',':'))+'\n');print(json.dumps({'event':'best','key':key,'maxabs':chk['maxabs'],'cycle':cycles,'step':step,'samples':samples,'elapsed_s':chk['elapsed_s']}),flush=True)
     if not key[0]:break
 out=exact(best,time.time()-start,samples,cycles,'hardcap_multi');name=q.prefix+('_candidate.json' if out['solved'] else '_summary.json');Path(name).write_text(json.dumps(out,separators=(',',':'))+'\n');print(json.dumps({'event':'result','solved':out['solved'],'key':(out['energy'],out['l1'],out['nonzero']),'cycles':cycles,'samples':samples,'output':name}),flush=True)
if __name__=='__main__':main()
