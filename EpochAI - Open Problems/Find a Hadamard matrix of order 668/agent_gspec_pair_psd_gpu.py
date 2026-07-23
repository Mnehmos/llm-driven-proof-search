"""PSD-cap-aware population annealing for SDS(167;73,76;66)."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch

N,H=167,83
def chi(i):return 0 if i==0 else (1 if pow(i,83,N)==1 else -1)
PAL=np.array([1 if i==0 else chi(i) for i in range(N)],np.int8)

def exact(pair,elapsed,samples,cycles,tag):
 a=np.vstack((np.asarray(pair,np.int8),PAL,PAL));r=[sum(sum(int(x[i])*int(x[(i+d)%N]) for i in range(N)) for x in a) for d in range(1,H+1)];ps=np.abs(np.fft.fft(a[:2],axis=1))**2;over=np.maximum(ps[:,1:H+1]-332.0,0)
 return {"construction":"cyclic Goethals-Seidel order 167, two Paley rows","search":"agent PSD-cap-aware two-block population annealing","tag":tag,"solved":not any(r),"independently_recomputed":True,"energy":sum(x*x for x in r),"l1":sum(abs(x) for x in r),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r),default=0),"row_sums":[int(x.sum()) for x in a],"psd_over_count":int((over>1e-7).sum()),"psd_max_overshoot":float(over.max(initial=0)),"psd_overshoot_sq":float((over*over).sum()),"residual":r,"elapsed_s":elapsed,"samples":samples,"cycles":cycles,"sequences":a.astype(int).tolist()}

def measures(x):
 f=torch.fft.rfft(x,dim=2);ps=f.real.square()+f.imag.square();ac=torch.fft.irfft(ps.sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]-2).long();e=(r*r).sum(1);over=torch.relu(ps[:,:,1:]-332.0);pen=over.square().sum((1,2));mx=over.amax((1,2));cnt=(over>.05).sum((1,2));return e,pen,mx,cnt

def proposal(x):
 b=x.shape[0];dev=x.device;ids=torch.arange(b,device=dev);k=torch.randint(2,(b,),device=dev);p=torch.randint(N,(b,),device=dev);bad=x[ids,k,p]!=1
 while bool(bad.any()):p[bad]=torch.randint(N,(int(bad.sum()),),device=dev);bad=x[ids,k,p]!=1
 q=torch.randint(N,(b,),device=dev);bad=x[ids,k,q]!=-1
 while bool(bad.any()):q[bad]=torch.randint(N,(int(bad.sum()),),device=dev);bad=x[ids,k,q]!=-1
 y=x.clone();y[ids,k,p]=-1;y[ids,k,q]=1;return y

def main():
 p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('--seconds',type=float,default=300);p.add_argument('--batch',type=int,default=8192);p.add_argument('--cycle-steps',type=int,default=5000);p.add_argument('--init-swaps',type=int,default=40);p.add_argument('--temp-high',type=float,default=5000);p.add_argument('--temp-low',type=float,default=.05);p.add_argument('--seed',type=int,default=167332);p.add_argument('--prefix',default='agent_gspec_pair_psd');q=p.parse_args()
 if not torch.cuda.is_available():raise SystemExit('CUDA unavailable')
 torch.manual_seed(q.seed);dev=torch.device('cuda');src=np.asarray(json.loads(Path(q.input).read_text())['sequences'],np.int8)[:2];best=src.copy();start=time.time();rep=exact(best,0,0,0,'canonical');best_e=rep['energy'];feasible=None;feasible_e=10**18;samples=0;cycles=0
 print(json.dumps({'event':'seed','energy':best_e,'psd_over_count':rep['psd_over_count'],'psd_max_overshoot':rep['psd_max_overshoot'],'rows':rep['row_sums']}),flush=True)
 lambdas=torch.tensor([.1,.25,.5,1.,2.,4.,8.,16.],device=dev)[torch.arange(q.batch,device=dev)%8]
 while best_e and time.time()-start<q.seconds:
  cycles+=1;base=feasible if feasible is not None and cycles%3==0 else best;x=torch.from_numpy(base).to(dev).float()[None].expand(q.batch,-1,-1).clone()
  for _ in range(q.init_swaps):x=proposal(x)
  e,pen,mx,cnt=measures(x);score=e.float()+lambdas*pen;samples+=q.batch
  for step in range(q.cycle_steps):
   if step%64==0 and time.time()-start>=q.seconds:break
   y=proposal(x);ne,npn,nmx,ncnt=measures(y);ns=ne.float()+lambdas*npn;samples+=q.batch;phase=step/max(1,q.cycle_steps-1);temp=q.temp_high*(q.temp_low/q.temp_high)**phase;delta=ns-score;acc=(delta<=0)|(torch.rand(q.batch,device=dev)<torch.exp(-delta/temp));x[acc]=y[acc];e[acc]=ne[acc];pen[acc]=npn[acc];mx[acc]=nmx[acc];cnt[acc]=ncnt[acc];score[acc]=ns[acc]
   ce=int(e.min())
   if ce<best_e:
    j=int(e.argmin());cand=x[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-start,samples,cycles,'canonical');assert chk['energy']==ce and chk['row_sums']==[21,15,1,1];best,best_e,rep=cand,ce,chk;Path(q.prefix+'_live.json').write_text(json.dumps(chk,separators=(',',':'))+'\n');print(json.dumps({'event':'best','energy':ce,'l1':chk['l1'],'psd_over_count':chk['psd_over_count'],'psd_max_overshoot':chk['psd_max_overshoot'],'cycle':cycles,'step':step,'samples':samples,'elapsed_s':chk['elapsed_s']}),flush=True)
    if not ce:break
   good=torch.nonzero(mx<.02).flatten()
   if len(good):
    ge=e[good];jj=int(good[int(ge.argmin())]);g=int(e[jj])
    if g<feasible_e:
     cand=x[jj].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-start,samples,cycles,'psd_feasible');
     if chk['psd_over_count']==0:feasible,feasible_e=cand,chk['energy'];Path(q.prefix+'_feasible_live.json').write_text(json.dumps(chk,separators=(',',':'))+'\n');print(json.dumps({'event':'psd_feasible','energy':feasible_e,'l1':chk['l1'],'cycle':cycles,'step':step,'samples':samples,'elapsed_s':chk['elapsed_s']}),flush=True)
 out=exact(best,time.time()-start,samples,cycles,'canonical');name=q.prefix+('_candidate.json' if out['solved'] else '_summary.json');Path(name).write_text(json.dumps(out,separators=(',',':'))+'\n');event={'event':'result','solved':out['solved'],'energy':out['energy'],'psd_over_count':out['psd_over_count'],'cycles':cycles,'samples':samples,'output':name}
 if feasible is not None:event['best_psd_feasible_energy']=feasible_e
 print(json.dumps(event),flush=True)
if __name__=='__main__':main()
