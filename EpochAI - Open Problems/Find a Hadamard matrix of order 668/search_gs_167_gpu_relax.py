"""Differentiable Fourier relaxation with exact-count projection for GS(167)."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch

N,H=167,83

def exact(a,elapsed,projections):
    a=np.asarray(a,np.int8);r=[sum(int(np.dot(x.astype(np.int32),np.roll(x,-d).astype(np.int32))) for x in a) for d in range(1,H+1)]
    return {"construction":"cyclic Goethals-Seidel order 167","search":"differentiable Fourier relaxation","solved":not any(r),"energy":sum(x*x for x in r),"l1":sum(map(abs,r)),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r)),"row_sums":[int(x.sum()) for x in a],"residual":r,"elapsed_s":elapsed,"projections":projections,"sequences":a.astype(int).tolist()}

def project(logits,counts):
    b=logits.shape[0];out=torch.full_like(logits,-1.0)
    for k,c in enumerate(counts):
        idx=logits[:,k].topk(c,dim=1).indices;out[:,k].scatter_(1,idx,1.0)
    return out

def discrete_energy(x):
    f=torch.fft.rfft(x,dim=2);ac=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]).long();return (r*r).sum(1)

def main():
    p=argparse.ArgumentParser();p.add_argument("input");p.add_argument("--seconds",type=float,default=180);p.add_argument("--batch",type=int,default=512);p.add_argument("--steps",type=int,default=2500);p.add_argument("--lr",type=float,default=.03);p.add_argument("--seed",type=int,default=668167);p.add_argument("--prefix",default="gs_167_gpu_relax");q=p.parse_args()
    if not torch.cuda.is_available():raise SystemExit("CUDA unavailable")
    torch.manual_seed(q.seed);dev=torch.device("cuda");base=np.asarray(json.loads(Path(q.input).read_text())["sequences"],np.int8);rows=base.sum(1).astype(int).tolist();counts=[(N+s)//2 for s in rows];best=base.copy();rep=exact(best,0,0);best_e=rep["energy"];started=time.time();projections=0;cycles=0
    print(json.dumps({"event":"seed","energy":best_e,"l1":rep["l1"],"rows":rows,"batch":q.batch}),flush=True)
    target=torch.tensor(rows,device=dev,dtype=torch.float32)
    while best_e and time.time()-started<q.seconds:
        seed=torch.from_numpy(best).to(dev).float();logits=(1.2*seed[None]+1.8*torch.randn(q.batch,4,N,device=dev)).requires_grad_();opt=torch.optim.Adam([logits],lr=q.lr);cycles+=1
        for step in range(q.steps):
            if step%32==0 and time.time()-started>=q.seconds:break
            opt.zero_grad(set_to_none=True);x=torch.tanh(logits);f=torch.fft.rfft(x,dim=2);ac=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(1),n=N,dim=1);corr=(ac[:,1:H+1]**2).mean(1);row=((x.sum(2)-target)**2).mean(1);phase=step/max(1,q.steps-1);binary=((1-x*x)**2).mean((1,2));loss=(corr+2.0*row+(0.1+20*phase*phase)*binary).mean();loss.backward();opt.step()
            if step%50==0 or step+1==q.steps:
                with torch.no_grad():disc=project(logits,counts);e=discrete_energy(disc);projections+=q.batch;cur=int(e.min())
                if cur<best_e:
                    j=int(e.argmin());cand=disc[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-started,projections);assert chk["energy"]==cur and chk["row_sums"]==rows
                    best,best_e,rep=cand,cur,chk;Path(q.prefix+"_live.json").write_text(json.dumps(chk,separators=(",",":"))+"\n");print(json.dumps({"event":"best","energy":cur,"l1":chk["l1"],"nonzero":chk["nonzero"],"cycle":cycles,"step":step,"projections":projections,"elapsed_s":chk["elapsed_s"]}),flush=True)
                    if not cur:break
    out=exact(best,time.time()-started,projections);name=q.prefix+("_candidate.json" if out["solved"] else "_summary.json");Path(name).write_text(json.dumps(out,separators=(",",":"))+"\n");print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"cycles":cycles,"projections":projections,"output":name}),flush=True)

if __name__=="__main__":main()
