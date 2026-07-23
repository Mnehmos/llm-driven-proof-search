"""Alternating-cycle crossover of two dual-margin LP(333) states."""
import argparse,json,time
from pathlib import Path
import numpy as np
import torch
N,H,P,Q=333,166,37,9
def crt(r,c):return r+P*((c-r)%Q)
def to_grid(seq):
    g=np.zeros((2,P,Q),np.bool_)
    for r in range(P):
        for c in range(Q):g[:,r,c]=seq[:,crt(r,c)]==1
    return g
def to_seq(g):
    x=np.full((2,N),-1,np.int8)
    for r in range(P):
        for c in range(Q):x[:,crt(r,c)]=np.where(g[:,r,c],1,-1)
    return x
def exact(g,elapsed,samples):
    seq=to_seq(g);rr=[2+sum(int(np.dot(seq[s].astype(np.int32),np.roll(seq[s],-h).astype(np.int32))) for s in range(2)) for h in range(1,H+1)]
    return {"construction":"Legendre pair length 333","fixed_compressions":["quadratic-character length 37","exact length 9"],"solved":not any(rr),
      "energy":sum(x*x for x in rr),"l1":sum(map(abs,rr)),"nonzero":sum(x!=0 for x in rr),"maxabs":max(map(abs,rr)),"elapsed_s":elapsed,"crossover_samples":samples,
      "sums":[int(x.sum()) for x in seq],"residual_paf_plus_2":rr,"sequences":seq.tolist()}

def cycles(a,b,rng,row_only=False):
    ans=[]
    for s in range(2):
        if row_only:
            for r in range(P):
                left=[(s,r,c) for c in range(Q) if a[s,r,c] and not b[s,r,c]];right=[(s,r,c) for c in range(Q) if b[s,r,c] and not a[s,r,c]]
                assert len(left)==len(right);rng.shuffle(right);ans.extend([[x,y] for x,y in zip(left,right)])
            continue
        edges=[]
        for r in range(P):
            for c in range(Q):
                if a[s,r,c]!=b[s,r,c]:edges.append((r,P+c,(s,r,c)) if a[s,r,c] else (P+c,r,(s,r,c)))
        outgoing={u:[] for u in range(P+Q)}
        for j,(u,v,cell) in enumerate(edges):outgoing[u].append(j)
        for z in outgoing.values():rng.shuffle(z)
        unused=set(range(len(edges)))
        while unused:
            j=next(iter(unused));start=edges[j][0];u=start;cy=[]
            while True:
                opts=[k for k in outgoing[u] if k in unused];assert opts
                k=opts[-1];unused.remove(k);_,u,cell=edges[k];cy.append(cell)
                if u==start:break
            ans.append(cy)
    return ans

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--a",required=True);ap.add_argument("--b",required=True);ap.add_argument("--seconds",type=float,default=300)
    ap.add_argument("--batch",type=int,default=32768);ap.add_argument("--prefix",default="lp333_crossover");ap.add_argument("--seed",type=int,default=777);ap.add_argument("--row-only",action="store_true");a=ap.parse_args()
    assert torch.cuda.is_available();dev=torch.device("cuda");rng=np.random.default_rng(a.seed)
    sa=np.asarray(json.loads(Path(a.a).read_text())["sequences"],np.int8);sb=np.asarray(json.loads(Path(a.b).read_text())["sequences"],np.int8)
    ga,gb=to_grid(sa),to_grid(sb);base=exact(ga,0,0);other=exact(gb,0,0);best_g=ga.copy() if base["energy"]<=other["energy"] else gb.copy();best_e=min(base["energy"],other["energy"])
    idx=torch.tensor([crt(r,c) for r in range(P) for c in range(Q)],device=dev);start=time.time();samples=0;decomps=0
    print(json.dumps({"event":"seed","energies":[base["energy"],other["energy"]]}),flush=True)
    while time.time()-start<a.seconds and best_e:
        cy=cycles(ga,gb,rng,a.row_only);m=len(cy);owner=np.full((2,P,Q),-1,np.int16)
        for j,cells in enumerate(cy):
            for s,r,c in cells:owner[s,r,c]=j
        own=torch.from_numpy(owner).to(dev);ta=torch.from_numpy(ga).to(dev);tb=torch.from_numpy(gb).to(dev);decomps+=1
        rounds=max(1,min(64,2_000_000//a.batch))
        for _ in range(rounds):
            bits=torch.randint(2,(a.batch,m),device=dev,dtype=torch.bool);oid=own.clamp_min(0).long()
            take=bits[:,oid.reshape(-1)].reshape(a.batch,2,P,Q)&(own[None]>=0);g=torch.where(take,tb[None],ta[None])
            z=(g.reshape(a.batch,2,N).float()*2-1);seq=torch.empty_like(z);seq.index_copy_(2,idx,z)
            f=torch.fft.rfft(seq,dim=2);p=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(dim=1),n=N,dim=1);rr=torch.round(p[:,1:H+1]).long()+2;e=(rr*rr).sum(dim=1)
            cur=int(e.min());samples+=a.batch
            if cur<best_e:
                j=int(e.argmin());cand=g[j].cpu().numpy();chk=exact(cand,time.time()-start,samples);assert chk["energy"]==cur;best_e=cur;best_g=cand
                Path(a.prefix+"_live.json").write_text(json.dumps(chk,separators=(",",":"))+"\n");print(json.dumps({"event":"best","energy":cur,"l1":chk["l1"],"nonzero":chk["nonzero"],"cycles":m,"decompositions":decomps,"samples":samples,"elapsed_s":chk["elapsed_s"]}),flush=True)
        if samples>=20_000_000:break
    out=exact(best_g,time.time()-start,samples);name=a.prefix+("_candidate.json" if out["solved"] else "_summary.json");Path(name).write_text(json.dumps(out,separators=(",",":"))+"\n")
    print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"samples":samples,"decompositions":decomps,"output":name}),flush=True)
if __name__=="__main__":main()
