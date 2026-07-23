"""Massively parallel GPU simulated annealing for cyclic GS(167)."""
import argparse,json,math,time
from pathlib import Path
import numpy as np
import torch

N,H=167,83

def exact(a,elapsed,samples):
    a=np.asarray(a,np.int8);r=[sum(int(np.dot(x.astype(np.int32),np.roll(x,-d).astype(np.int32))) for x in a) for d in range(1,H+1)]
    return {"construction":"cyclic Goethals-Seidel order 167","search":"GPU population annealing","solved":not any(r),"energy":sum(x*x for x in r),"l1":sum(map(abs,r)),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r)),"row_sums":[int(x.sum()) for x in a],"residual":r,"elapsed_s":elapsed,"samples":samples,"sequences":a.astype(int).tolist()}

def energy(x):
    f=torch.fft.rfft(x,dim=2);ac=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]).long();return (r*r).sum(1)

def proposal(x,active):
    b=x.shape[0];dev=x.device;rows=torch.arange(b,device=dev);k=torch.randint(active,(b,),device=dev);p=torch.randint(N,(b,),device=dev)
    bad=x[rows,k,p]!=1
    while bool(bad.any()):p[bad]=torch.randint(N,(int(bad.sum()),),device=dev);bad=x[rows,k,p]!=1
    q=torch.randint(N,(b,),device=dev);bad=x[rows,k,q]!=-1
    while bool(bad.any()):q[bad]=torch.randint(N,(int(bad.sum()),),device=dev);bad=x[rows,k,q]!=-1
    y=x.clone();y[rows,k,p]=-1;y[rows,k,q]=1;return y

def main():
    p=argparse.ArgumentParser();p.add_argument("input");p.add_argument("--seconds",type=float,default=120);p.add_argument("--batch",type=int,default=8192);p.add_argument("--active",type=int,choices=(1,2,3,4),default=4);p.add_argument("--cycle-steps",type=int,default=4000);p.add_argument("--init-swaps",type=int,default=40);p.add_argument("--temp-high",type=float,default=3000);p.add_argument("--temp-low",type=float,default=.5);p.add_argument("--seed",type=int,default=668167);p.add_argument("--prefix",default="gs_167_gpu_anneal");q=p.parse_args()
    if not torch.cuda.is_available():raise SystemExit("CUDA unavailable")
    torch.manual_seed(q.seed);dev=torch.device("cuda");base=np.asarray(json.loads(Path(q.input).read_text())["sequences"],np.int8);best=base.copy();report=exact(best,0,0);best_e=report["energy"];started=time.time();samples=0;cycles=0
    print(json.dumps({"event":"seed","energy":best_e,"l1":report["l1"],"rows":report["row_sums"],"batch":q.batch}),flush=True)
    while best_e and time.time()-started<q.seconds:
        x=torch.from_numpy(best).to(dev).float().expand(q.batch,-1,-1).clone()
        for _ in range(q.init_swaps):x=proposal(x,q.active)
        e=energy(x);samples+=q.batch;cycles+=1
        for step in range(q.cycle_steps):
            if step%64==0 and time.time()-started>=q.seconds:break
            y=proposal(x,q.active);ne=energy(y);samples+=q.batch;phase=step/max(1,q.cycle_steps-1);temp=q.temp_high*(q.temp_low/q.temp_high)**phase
            de=ne-e;accept=(de<=0)|(torch.rand(q.batch,device=dev)<torch.exp(-de.float()/temp));x[accept]=y[accept];e[accept]=ne[accept]
            cur=int(e.min())
            if cur<best_e:
                j=int(e.argmin());cand=x[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-started,samples);assert chk["energy"]==cur and chk["row_sums"]==report["row_sums"]
                best,best_e,report=cand,cur,chk;Path(q.prefix+"_live.json").write_text(json.dumps(chk,separators=(",",":"))+"\n");print(json.dumps({"event":"best","energy":cur,"l1":chk["l1"],"nonzero":chk["nonzero"],"cycle":cycles,"step":step,"samples":samples,"elapsed_s":chk["elapsed_s"]}),flush=True)
                if not cur:break
    out=exact(best,time.time()-started,samples);name=q.prefix+("_candidate.json" if out["solved"] else "_summary.json");Path(name).write_text(json.dumps(out,separators=(",",":"))+"\n");print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"samples":samples,"cycles":cycles,"output":name}),flush=True)

if __name__=="__main__":main()
