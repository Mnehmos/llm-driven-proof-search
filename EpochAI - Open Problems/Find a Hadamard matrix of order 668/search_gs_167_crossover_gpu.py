"""GPU balanced crossover between two cyclic GS(167) states."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch

N,H=167,83

def exact(a,elapsed,samples):
    a=np.asarray(a,dtype=np.int8);r=[sum(int(np.dot(x.astype(np.int32),np.roll(x,-d).astype(np.int32))) for x in a) for d in range(1,H+1)]
    return {"construction":"cyclic Goethals-Seidel order 167","search":"balanced GPU crossover","solved":not any(r),"energy":sum(x*x for x in r),"l1":sum(map(abs,r)),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r)),"row_sums":[int(x.sum()) for x in a],"residual":r,"elapsed_s":elapsed,"samples":samples,"sequences":a.astype(int).tolist()}

def owners(a,b,rng):
    owner=np.full((4,N),-1,np.int16);m=0
    for k in range(4):
        left=np.flatnonzero((a[k]==1)&(b[k]==-1));right=np.flatnonzero((a[k]==-1)&(b[k]==1));assert len(left)==len(right)
        rng.shuffle(right)
        for p,q in zip(left,right):owner[k,p]=m;owner[k,q]=m;m+=1
    return owner,m

def main():
    p=argparse.ArgumentParser();p.add_argument("--a",required=True);p.add_argument("--b",required=True);p.add_argument("--seconds",type=float,default=120);p.add_argument("--batch",type=int,default=32768);p.add_argument("--samples",type=int,default=30000000);p.add_argument("--seed",type=int,default=668167);p.add_argument("--prefix",default="gs_167_crossover");q=p.parse_args()
    if not torch.cuda.is_available():raise SystemExit("CUDA unavailable")
    rng=np.random.default_rng(q.seed);dev=torch.device("cuda")
    a=np.asarray(json.loads(Path(q.a).read_text())["sequences"],np.int8);b=np.asarray(json.loads(Path(q.b).read_text())["sequences"],np.int8)
    if a.shape!=(4,N) or b.shape!=(4,N) or not np.array_equal(a.sum(1),b.sum(1)):raise ValueError("incompatible GS parents")
    ra,rb=exact(a,0,0),exact(b,0,0);best=a.copy() if ra["energy"]<=rb["energy"] else b.copy();best_e=min(ra["energy"],rb["energy"]);samples=0;decomps=0;started=time.time()
    print(json.dumps({"event":"seed","energies":[ra["energy"],rb["energy"]],"rows":ra["row_sums"]}),flush=True)
    while best_e and samples<q.samples and time.time()-started<q.seconds:
        own,m=owners(a,b,rng);decomps+=1;ot=torch.from_numpy(own).to(dev);ta=torch.from_numpy(a).to(dev);tb=torch.from_numpy(b).to(dev);oid=ot.clamp_min(0).long()
        for _ in range(16):
            bits=torch.randint(2,(q.batch,m),device=dev,dtype=torch.bool);take=bits[:,oid.reshape(-1)].reshape(q.batch,4,N)&(ot[None]>=0);x=torch.where(take,tb[None],ta[None]).float()
            f=torch.fft.rfft(x,dim=2);ac=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(dim=1),n=N,dim=1);r=torch.round(ac[:,1:H+1]).long();e=(r*r).sum(1);samples+=q.batch
            cur=int(e.min())
            if cur<best_e:
                j=int(e.argmin());cand=x[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-started,samples);assert chk["energy"]==cur and chk["row_sums"]==ra["row_sums"]
                best,best_e=cand,cur;Path(q.prefix+"_live.json").write_text(json.dumps(chk,separators=(",",":"))+"\n");print(json.dumps({"event":"best","energy":cur,"l1":chk["l1"],"nonzero":chk["nonzero"],"pairs":m,"samples":samples,"elapsed_s":chk["elapsed_s"]}),flush=True)
            if samples>=q.samples or time.time()-started>=q.seconds:break
    out=exact(best,time.time()-started,samples);name=q.prefix+("_candidate.json" if out["solved"] else "_summary.json");Path(name).write_text(json.dumps(out,separators=(",",":"))+"\n");print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"samples":samples,"decompositions":decomps,"output":name}),flush=True)

if __name__=="__main__":main()
