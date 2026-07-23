"""Hard-PSD-cap annealing inside the feasible SDS(167;73,76;66) region."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch
from agent_gspec_pair_psd_gpu import exact,measures,proposal

def main():
 p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('--seconds',type=float,default=300);p.add_argument('--batch',type=int,default=8192);p.add_argument('--steps',type=int,default=12000);p.add_argument('--temp-high',type=float,default=3000);p.add_argument('--temp-low',type=float,default=.03);p.add_argument('--seed',type=int,default=332167);p.add_argument('--prefix',default='agent_gspec_pair_hardcap');q=p.parse_args()
 if not torch.cuda.is_available():raise SystemExit('CUDA unavailable')
 torch.manual_seed(q.seed);dev=torch.device('cuda');src=np.asarray(json.loads(Path(q.input).read_text())['sequences'],np.int8)[:2];best=src.copy();start=time.time();rep=exact(best,0,0,0,'hardcap');
 if rep['psd_over_count']:raise ValueError('input is not PSD-cap feasible')
 best_e=rep['energy'];samples=0;cycles=0;print(json.dumps({'event':'seed','energy':best_e,'l1':rep['l1'],'rows':rep['row_sums']}),flush=True)
 while best_e and time.time()-start<q.seconds:
  cycles+=1;x=torch.from_numpy(best).to(dev).float()[None].expand(q.batch,-1,-1).clone();e,pen,mx,cnt=measures(x)
  for step in range(q.steps):
   if step%64==0 and time.time()-start>=q.seconds:break
   y=proposal(x);ne,npn,nmx,ncnt=measures(y);samples+=q.batch;phase=step/max(1,q.steps-1);temp=q.temp_high*(q.temp_low/q.temp_high)**phase;de=ne-e;acc=(nmx<.02)&((de<=0)|(torch.rand(q.batch,device=dev)<torch.exp(-de.float()/temp)));x[acc]=y[acc];e[acc]=ne[acc]
   ce=int(e.min())
   if ce<best_e:
    j=int(e.argmin());cand=x[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-start,samples,cycles,'hardcap');assert chk['energy']==ce and chk['psd_over_count']==0;best,best_e,rep=cand,ce,chk;Path(q.prefix+'_live.json').write_text(json.dumps(chk,separators=(',',':'))+'\n');print(json.dumps({'event':'best','energy':ce,'l1':chk['l1'],'nonzero':chk['nonzero'],'maxabs':chk['maxabs'],'cycle':cycles,'step':step,'samples':samples,'elapsed_s':chk['elapsed_s']}),flush=True)
    if not ce:break
 out=exact(best,time.time()-start,samples,cycles,'hardcap');name=q.prefix+('_candidate.json' if out['solved'] else '_summary.json');Path(name).write_text(json.dumps(out,separators=(',',':'))+'\n');print(json.dumps({'event':'result','solved':out['solved'],'energy':out['energy'],'l1':out['l1'],'cycles':cycles,'samples':samples,'output':name}),flush=True)
if __name__=='__main__':main()
