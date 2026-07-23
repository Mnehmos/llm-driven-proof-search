"""GPU exhaustive top-single pair neighborhood and targeted triple sampling."""
import argparse,itertools,json,time
from pathlib import Path
import numpy as np
import torch

N,H=167,83

def exact(a):
    a=np.asarray(a,np.int8);r=[sum(int(np.dot(x.astype(np.int32),np.roll(x,-d).astype(np.int32))) for x in a) for d in range(1,H+1)]
    return {"construction":"cyclic Goethals-Seidel order 167","search":"GPU top-move compounds","solved":not any(r),"energy":sum(x*x for x in r),"l1":sum(map(abs,r)),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r)),"row_sums":[int(x.sum()) for x in a],"residual":r,"sequences":a.astype(int).tolist()}

def compatible(moves):
    seen=set()
    for k,p,q in moves:
        if (k,p) in seen or (k,q) in seen:return False
        seen.add((k,p));seen.add((k,q))
    return True

def evaluate(base,movesets,batch,dev):
    energies=[];best=None;best_e=10**18
    for lo in range(0,len(movesets),batch):
        chunk=movesets[lo:lo+batch];b=len(chunk);x=torch.from_numpy(base).to(dev).float().expand(b,-1,-1).clone();rows=torch.arange(b,device=dev)
        arity=len(chunk[0])
        for t in range(arity):
            k=torch.tensor([z[t][0] for z in chunk],device=dev);p=torch.tensor([z[t][1] for z in chunk],device=dev);q=torch.tensor([z[t][2] for z in chunk],device=dev)
            x[rows,k,p]*=-1;x[rows,k,q]*=-1
        f=torch.fft.rfft(x,dim=2);ac=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(1),n=N,dim=1);r=torch.round(ac[:,1:H+1]).long();e=(r*r).sum(1);energies.extend(e.cpu().tolist())
        cur=int(e.min())
        if cur<best_e:j=int(e.argmin());best_e=cur;best=x[j].cpu().numpy().astype(np.int8)
    return np.asarray(energies,np.int64),best,best_e

def main():
    p=argparse.ArgumentParser();p.add_argument("input");p.add_argument("--top",type=int,default=768);p.add_argument("--triples",type=int,default=5000000);p.add_argument("--batch",type=int,default=32768);p.add_argument("--seed",type=int,default=668167);p.add_argument("--active",type=int,choices=(1,2,3,4),default=4);p.add_argument("--prefix",default="gs_167_topmoves");q=p.parse_args()
    if not torch.cuda.is_available():raise SystemExit("CUDA unavailable")
    dev=torch.device("cuda");rng=np.random.default_rng(q.seed);base=np.asarray(json.loads(Path(q.input).read_text())["sequences"],np.int8);initial=exact(base);started=time.time();samples=0
    allmoves=[]
    for k in range(q.active):
        plus=np.flatnonzero(base[k]==1);minus=np.flatnonzero(base[k]==-1);allmoves.extend((k,int(i),int(j)) for i in plus for j in minus)
    single_sets=[(m,) for m in allmoves];se,_,single_best_e=evaluate(base,single_sets,q.batch,dev);best=base.copy();best_e=initial["energy"];samples+=len(single_sets);order=np.argsort(se);top=[allmoves[i] for i in order[:q.top]]
    print(json.dumps({"event":"singles","count":len(allmoves),"seed_energy":initial["energy"],"best_single_energy":single_best_e,"top":len(top),"elapsed_s":time.time()-started}),flush=True)
    pair_sets=[(top[i],top[j]) for i in range(len(top)) for j in range(i+1,len(top)) if compatible((top[i],top[j]))]
    pe,pbest,pbest_e=evaluate(base,pair_sets,q.batch,dev);samples+=len(pair_sets)
    if pbest_e<best_e:best,best_e=pbest,pbest_e
    print(json.dumps({"event":"pairs","count":len(pair_sets),"best_pair_energy":pbest_e,"samples":samples,"elapsed_s":time.time()-started}),flush=True)
    done=0
    while done<q.triples and best_e:
        want=min(q.batch,q.triples-done);sets=[]
        while len(sets)<want:
            ids=rng.integers(len(top),size=(want*2,3))
            for row in ids:
                z=tuple(top[int(i)] for i in row)
                if len(set(map(tuple,z)))==3 and compatible(z):sets.append(z)
                if len(sets)==want:break
        _,cand,cur=evaluate(base,sets,q.batch,dev);done+=want;samples+=want
        if cur<best_e:best,best_e=cand,cur;chk=exact(best);Path(q.prefix+"_live.json").write_text(json.dumps(chk,separators=(",",":"))+"\n");print(json.dumps({"event":"best","energy":best_e,"l1":chk["l1"],"arity":3,"samples":samples,"elapsed_s":time.time()-started}),flush=True)
    out=exact(best if best_e<initial["energy"] else base);out.update(elapsed_s=time.time()-started,samples=samples)
    name=q.prefix+("_candidate.json" if out["solved"] else "_summary.json");Path(name).write_text(json.dumps(out,separators=(",",":"))+"\n");print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"samples":samples,"output":name}),flush=True)

if __name__=="__main__":main()
