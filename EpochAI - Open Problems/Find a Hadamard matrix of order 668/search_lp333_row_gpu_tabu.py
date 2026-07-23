"""CUDA exhaustive-neighborhood tabu search in the exact 37-compression fiber."""
import argparse,json,time
from collections import deque
from pathlib import Path
import numpy as np
import torch
N,H,P,Q=333,166,37,9
def chi(r):return 0 if r==0 else (1 if pow(r,18,37)==1 else -1)
def target(s,r):return 1 if r==0 else (3*chi(r) if s==0 else -3*chi(r))

def exact(seq,elapsed,steps):
    rr=[2+sum(int(np.dot(seq[s].astype(np.int32),np.roll(seq[s],-h).astype(np.int32))) for s in range(2)) for h in range(1,H+1)]
    comp=[[int(sum(seq[s,r+P*k] for k in range(Q))) for r in range(P)] for s in range(2)]
    assert [int(x.sum()) for x in seq]==[1,1] and all(comp[s][r]==target(s,r) for s in range(2) for r in range(P))
    return {"construction":"Legendre pair length 333","fixed_compression":"quadratic-character length 37","solved":not any(rr),
            "energy":sum(x*x for x in rr),"l1":sum(map(abs,rr)),"nonzero":sum(x!=0 for x in rr),"maxabs":max(map(abs,rr)),
            "elapsed_s":elapsed,"steps":steps,"sums":[int(x.sum()) for x in seq],"residual_paf_plus_2":rr,"compression37":comp,"sequences":seq.tolist()}

def moves(seq):
    masks=[];keys=[]
    for s in range(2):
        for r in range(P):
            pos=[r+P*k for k in range(Q) if seq[s,r+P*k]==1];neg=[r+P*k for k in range(Q) if seq[s,r+P*k]==-1]
            for p in pos:
                for q in neg:
                    m=np.zeros((2,N),np.bool_);m[s,p]=m[s,q]=True;masks.append(m);keys.append((0,s,min(p,q),max(p,q)))
            old=seq[s,[r+P*k for k in range(Q)]]
            for sh in range(1,Q):
                diff=np.flatnonzero(old!=np.roll(old,-sh))
                m=np.zeros((2,N),np.bool_);m[s,[r+P*int(k) for k in diff]]=True;masks.append(m);keys.append((1,s,r,sh))
    return np.stack(masks),keys

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--input",default="lp333_native_summary.json");ap.add_argument("--seconds",type=float,default=600)
    ap.add_argument("--prefix",default="lp333_row_gpu_tabu");ap.add_argument("--tenure",type=int,default=35);ap.add_argument("--seed",type=int,default=333);ap.add_argument("--pairs",type=int,default=32768);ap.add_argument("--arity",type=int,default=2)
    a=ap.parse_args();assert torch.cuda.is_available();rng=np.random.default_rng(a.seed);dev=torch.device("cuda")
    seq=np.asarray(json.loads(Path(a.input).read_text())["sequences"],dtype=np.int8);best=seq.copy();start=time.time();z=exact(best,0,0);best_e=z["energy"]
    print(json.dumps({"event":"seed","energy":best_e,"l1":z["l1"]}),flush=True);tabu={};history=deque();step=0
    def scores(c):
        x=torch.from_numpy(c.astype(np.float32)).to(dev);f=torch.fft.rfft(x,dim=2);p=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(dim=1),n=N,dim=1)
        rr=torch.round(p[:,1:H+1]).to(torch.int64)+2;return (rr*rr).sum(dim=1).cpu().numpy(),rr.abs().sum(dim=1).cpu().numpy()
    while time.time()-start<a.seconds and best_e:
        mask,keys=moves(seq);cand=np.where(mask,-seq[None,:,:],seq[None,:,:]).astype(np.int8);e,l1=scores(cand)
        pair_candidate=None;pair_e=None
        if a.pairs:
            ij=rng.integers(len(mask),size=(a.arity,a.pairs));pmask=np.logical_xor.reduce(mask[ij],axis=0)
            pcand=np.where(pmask,-seq[None,:,:],seq[None,:,:]).astype(np.int8);pe,pl1=scores(pcand);j2=int(np.lexsort((pl1,pe))[0])
            if int(pe[j2])<best_e:pair_candidate=pcand[j2];pair_e=int(pe[j2])
        order=np.lexsort((l1,e));chosen=None
        for j in order:
            if tabu.get(keys[j],-1)<=step or e[j]<best_e:chosen=int(j);break
        if chosen is None:chosen=int(order[0])
        key=keys[chosen];tabu[key]=step+a.tenure+int(rng.integers(a.tenure//2+1));history.append(key)
        while history and tabu.get(history[0],0)<=step:history.popleft()
        seq=cand[chosen];step+=1
        if pair_candidate is not None:seq=pair_candidate;e_chosen=pair_e
        else:e_chosen=int(e[chosen])
        if e_chosen<best_e:
            chk=exact(seq,time.time()-start,step);assert chk["energy"]==e_chosen;best_e=chk["energy"];best=seq.copy()
            Path(a.prefix+"_live.json").write_text(json.dumps(chk,separators=(",",":"))+"\n")
            print(json.dumps({"event":"best","energy":best_e,"l1":chk["l1"],"nonzero":chk["nonzero"],"maxabs":chk["maxabs"],"elapsed_s":chk["elapsed_s"],"steps":step}),flush=True)
        if step%400==0:
            seq=best.copy()
            for _ in range(6):
                s=int(rng.integers(2));r=int(rng.integers(P));pos=[r+P*k for k in range(Q) if seq[s,r+P*k]==1];neg=[r+P*k for k in range(Q) if seq[s,r+P*k]==-1]
                p=int(rng.choice(pos));q=int(rng.choice(neg));seq[s,p]*=-1;seq[s,q]*=-1
            tabu.clear();history.clear()
    out=exact(best,time.time()-start,step);name=a.prefix+("_candidate.json" if out["solved"] else "_summary.json")
    Path(name).write_text(json.dumps(out,separators=(",",":"))+"\n");print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"steps":step,"output":name}),flush=True)
if __name__=="__main__":main()
