"""Exact GPU single/pair and sampled triple hard-cap neighborhoods."""
import argparse,itertools,json,time
from pathlib import Path
import numpy as np
import torch
from agent_gspec_pair_psd_gpu import exact

N,H=167,83
def compatible(ms):
 seen=set()
 for k,p,q in ms:
  if (k,p) in seen or (k,q) in seen:return False
  seen|={(k,p),(k,q)}
 return True
def evaluate(base,sets,batch,dev):
 best=None;be=10**18;valid=[]
 for lo in range(0,len(sets),batch):
  c=sets[lo:lo+batch];b=len(c);x=torch.from_numpy(base).to(dev).float()[None].expand(b,-1,-1).clone();ids=torch.arange(b,device=dev)
  for t in range(len(c[0])):
   k=torch.tensor([z[t][0] for z in c],device=dev);p=torch.tensor([z[t][1] for z in c],device=dev);q=torch.tensor([z[t][2] for z in c],device=dev);x[ids,k,p]*=-1;x[ids,k,q]*=-1
  f=torch.fft.rfft(x,dim=2);ps=f.real.square()+f.imag.square();cap=(ps[:,:,1:]<=332.02).all((1,2));ac=torch.fft.irfft(ps.sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]-2).long();e=(r*r).sum(1);e[~cap]=10**18
  for j,z in enumerate(e.cpu().tolist()):
   if z<10**18:valid.append((z,lo+j))
  cur=int(e.min())
  if cur<be:j=int(e.argmin());be=cur;best=x[j].cpu().numpy().astype(np.int8)
 return best,be,valid
def main():
 p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('--top',type=int,default=512);p.add_argument('--triples',type=int,default=2000000);p.add_argument('--batch',type=int,default=32768);p.add_argument('--seed',type=int,default=332170);p.add_argument('--prefix',default='agent_gspec_pair_hardcap_topmoves');q=p.parse_args();
 if not torch.cuda.is_available():raise SystemExit('CUDA unavailable')
 dev=torch.device('cuda');rng=np.random.default_rng(q.seed);base=np.asarray(json.loads(Path(q.input).read_text())['sequences'],np.int8)[:2];start=time.time();initial=exact(base,0,0,0,'hardcap_topmoves');assert initial['psd_over_count']==0;moves=[]
 for k in range(2):
  plus=np.flatnonzero(base[k]==1);minus=np.flatnonzero(base[k]==-1);moves += [(k,int(i),int(j)) for i in plus for j in minus]
 singles=[(m,) for m in moves];sb,se,valid=evaluate(base,singles,q.batch,dev);valid.sort();top=[moves[i] for _,i in valid[:q.top]];best=base.copy();be=initial['energy'];tested=len(singles);print(json.dumps({'event':'singles','tested':len(singles),'feasible':len(valid),'best':se,'seed_energy':be,'top':len(top)}),flush=True)
 if se<be:best,be=sb,se
 pairs=[(top[i],top[j]) for i in range(len(top)) for j in range(i+1,len(top)) if compatible((top[i],top[j]))];pb,pe,_=evaluate(base,pairs,q.batch,dev);tested+=len(pairs);print(json.dumps({'event':'pairs','tested':len(pairs),'best':pe}),flush=True)
 if pe<be:best,be=pb,pe
 done=0
 while done<q.triples and be:
  want=min(q.batch,q.triples-done);sets=[]
  while len(sets)<want:
   for ids in rng.integers(len(top),size=(want,3)):
    z=tuple(top[int(i)] for i in ids)
    if len(set(z))==3 and compatible(z):sets.append(z)
    if len(sets)>=want:break
  tb,te,_=evaluate(base,sets,q.batch,dev);done+=want;tested+=want
  if te<be:best,be=tb,te;chk=exact(best,time.time()-start,tested,1,'hardcap_topmoves');Path(q.prefix+'_live.json').write_text(json.dumps(chk,separators=(',',':'))+'\n');print(json.dumps({'event':'best','energy':be,'l1':chk['l1'],'arity':3,'tested':tested,'elapsed_s':chk['elapsed_s']}),flush=True)
 out=exact(best,time.time()-start,tested,1,'hardcap_topmoves');name=q.prefix+('_candidate.json' if out['solved'] else '_summary.json');Path(name).write_text(json.dumps(out,separators=(',',':'))+'\n');print(json.dumps({'event':'result','solved':out['solved'],'energy':out['energy'],'l1':out['l1'],'tested':tested,'output':name}),flush=True)
if __name__=='__main__':main()
