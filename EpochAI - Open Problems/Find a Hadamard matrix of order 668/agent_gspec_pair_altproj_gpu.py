"""Douglas--Rachford Fourier projection for SDS(167;73,76;66)."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch

N,H=167,83
def chi(i):return 0 if i==0 else (1 if pow(i,83,N)==1 else -1)
PALEY=np.array([1 if i==0 else chi(i) for i in range(N)],np.int8)

def exact(pair,elapsed,projections,restarts):
    a=np.vstack((np.asarray(pair,np.int8),PALEY,PALEY));r=[sum(sum(int(x[i])*int(x[(i+d)%N]) for i in range(N)) for x in a) for d in range(1,H+1)]
    return {"construction":"cyclic Goethals-Seidel order 167, two Paley rows","search":"agent two-block Fourier Douglas-Rachford projection","solved":not any(r),"independently_recomputed":True,"energy":sum(x*x for x in r),"l1":sum(abs(x) for x in r),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r),default=0),"row_sums":[int(x.sum()) for x in a],"residual":r,"elapsed_s":elapsed,"projections":projections,"restarts":restarts,"sequences":a.astype(int).tolist()}

def binary(z):
    out=torch.full_like(z,-1.0)
    for k,c in enumerate((94,91)):out[:,k].scatter_(1,z[:,k].topk(c,dim=1).indices,1.0)
    return out

def spectral(z,zero):
    f=torch.fft.fft(z,dim=2);norm=(f.real.square()+f.imag.square()).sum(1,keepdim=True).clamp_min(1e-12);f*=torch.sqrt(torch.tensor(332.0,device=z.device)/norm);f[:,:,0]=zero;return torch.fft.ifft(f,dim=2).real

def metrics(x):
    f=torch.fft.rfft(x,dim=2);ac=torch.fft.irfft((f.real.square()+f.imag.square()).sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]-2).long();return r,(r*r).sum(1),r.abs().sum(1)

def perturb(x,n):
    b=x.shape[0];dev=x.device;ids=torch.arange(b,device=dev)
    for _ in range(n):
        k=torch.randint(2,(b,),device=dev);p=torch.randint(N,(b,),device=dev);bad=x[ids,k,p]!=1
        while bool(bad.any()):p[bad]=torch.randint(N,(int(bad.sum()),),device=dev);bad=x[ids,k,p]!=1
        q=torch.randint(N,(b,),device=dev);bad=x[ids,k,q]!=-1
        while bool(bad.any()):q[bad]=torch.randint(N,(int(bad.sum()),),device=dev);bad=x[ids,k,q]!=-1
        x[ids,k,p]=-1;x[ids,k,q]=1
    return x

def main():
    p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('--seconds',type=float,default=300);p.add_argument('--batch',type=int,default=4096);p.add_argument('--steps',type=int,default=1200);p.add_argument('--beta',type=float,default=.84);p.add_argument('--noise',type=float,default=.4);p.add_argument('--seed',type=int,default=1677376);p.add_argument('--prefix',default='agent_gspec_pair_altproj');q=p.parse_args()
    if not torch.cuda.is_available():raise SystemExit('CUDA unavailable')
    torch.manual_seed(q.seed);dev=torch.device('cuda');src=np.asarray(json.loads(Path(q.input).read_text())['sequences'],np.int8)[:2];best=src.copy();started=time.time();rep=exact(best,0,0,0);key=(rep['energy'],rep['l1'],rep['nonzero']);projections=0;restarts=0;zero=torch.tensor([[21,15]],device=dev,dtype=torch.complex64)
    print(json.dumps({'event':'seed','key':key,'rows':rep['row_sums'],'batch':q.batch}),flush=True)
    while key[0] and time.time()-started<q.seconds:
        restarts+=1;z=torch.from_numpy(best).to(dev).float()[None].expand(q.batch,-1,-1).clone();z=perturb(z,2+restarts%31);z+=q.noise*torch.randn_like(z);split=q.batch//2
        for step in range(q.steps):
            if step%16==0 and time.time()-started>=q.seconds:break
            b=spectral(z,zero);a=binary(2*b-z);z[:split]=binary(b[:split]);z[split:]+=q.beta*(a[split:]-b[split:]);projections+=q.batch
            if step%5:continue
            disc=binary(z);r,e,l1=metrics(disc);ce=int(e.min())
            if ce<=key[0]:
                ids=torch.nonzero(e==ce).flatten();j=int(ids[int(l1[ids].argmin())]);cand=disc[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-started,projections,restarts);nk=(chk['energy'],chk['l1'],chk['nonzero']);assert nk[0]==ce and chk['row_sums']==[21,15,1,1]
                if nk<key:
                    best,key,rep=cand,nk,chk;Path(q.prefix+'_live.json').write_text(json.dumps(chk,separators=(',',':'))+'\n');print(json.dumps({'event':'best','key':key,'maxabs':chk['maxabs'],'restart':restarts,'step':step,'projections':projections,'elapsed_s':chk['elapsed_s']}),flush=True)
                    if not key[0]:break
    out=exact(best,time.time()-started,projections,restarts);name=q.prefix+('_candidate.json' if out['solved'] else '_summary.json');Path(name).write_text(json.dumps(out,separators=(',',':'))+'\n');print(json.dumps({'event':'result','solved':out['solved'],'key':(out['energy'],out['l1'],out['nonzero']),'projections':projections,'restarts':restarts,'output':name}),flush=True)
if __name__=='__main__':main()
