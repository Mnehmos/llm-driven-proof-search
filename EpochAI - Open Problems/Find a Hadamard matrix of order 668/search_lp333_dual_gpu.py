"""Batched CUDA search for LP(333) with exact 37-by-9 CRT margins."""
import argparse, json, math, time
from pathlib import Path
import numpy as np
import torch

N,H,P,Q=333,166,37,9
DEFAULT_COL=[[16,19,17,15,20,15,27,21,17],[18,17,20,21,18,17,22,18,16]]
def chi(r):return 0 if r==0 else (1 if pow(r,18,37)==1 else -1)
def row_sum(s,r):return 1 if r==0 else (3*chi(r) if s==0 else -3*chi(r))
def row_degree(s,r):return (Q+row_sum(s,r))//2
def crt(r,c):return r+P*((c-r)%Q)

def columns(path):
    if not path:return DEFAULT_COL
    z=json.loads(Path(path).read_text());return z["column_plus_counts"]

def realization(s,col,rng):
    g=np.zeros((P,Q),dtype=np.bool_);rem=list(map(int,col[s]))
    rows=list(range(P));rng.shuffle(rows);rows.sort(key=lambda r:row_degree(s,r),reverse=True)
    for r in rows:
        cs=list(range(Q));rng.shuffle(cs);cs.sort(key=lambda c:rem[c],reverse=True)
        for c in cs[:row_degree(s,r)]:
            assert rem[c]>0;g[r,c]=True;rem[c]-=1
    assert not any(rem);return g

def exact_state(grid,col,elapsed,moves):
    seq=np.full((2,N),-1,dtype=np.int8)
    for r in range(P):
        for c in range(Q):seq[:,crt(r,c)]=np.where(grid[:,r,c],1,-1)
    rr=[]
    for h in range(1,H+1):rr.append(2+sum(int(np.dot(seq[s].astype(np.int32),np.roll(seq[s],-h).astype(np.int32))) for s in range(2)))
    c37=[[int(sum(seq[s,r+P*k] for k in range(Q))) for r in range(P)] for s in range(2)]
    c9=[[int(sum(seq[s,crt(r,c)] for r in range(P))) for c in range(Q)] for s in range(2)]
    assert [int(x.sum()) for x in seq]==[1,1]
    assert all(c37[s][r]==row_sum(s,r) for s in range(2) for r in range(P))
    assert all((c9[s][c]+P)//2==col[s][c] for s in range(2) for c in range(Q))
    return {"construction":"Legendre pair length 333","fixed_compressions":["quadratic-character length 37","exact length 9"],
            "solved":not any(rr),"energy":sum(x*x for x in rr),"elapsed_s":elapsed,"moves":moves,
            "sums":[int(x.sum()) for x in seq],"nonzero":sum(x!=0 for x in rr),"maxabs":max(map(abs,rr)),
            "residual_paf_plus_2":rr,"compression37":c37,"compression9":c9,"sequences":seq.tolist()}

def propose(g,gen,compound=1):
    b=g.shape[0];cand=g.clone();bi=torch.arange(b,device=g.device)
    for _ in range(compound):
        s=torch.randint(2,(b,),device=g.device,generator=gen)
        r1=torch.randint(P,(b,),device=g.device,generator=gen);r2=torch.randint(P-1,(b,),device=g.device,generator=gen);r2+=r2>=r1
        c1=torch.randint(Q,(b,),device=g.device,generator=gen);c2=torch.randint(Q-1,(b,),device=g.device,generator=gen);c2+=c2>=c1
        a=cand[bi,s,r1,c1];d=cand[bi,s,r2,c2];v=cand[bi,s,r1,c2];w=cand[bi,s,r2,c1]
        ok=(a==d)&(v==w)&(a!=v);ii=bi[ok];ss=s[ok]
        cand[ii,ss,r1[ok],c1[ok]]^=True;cand[ii,ss,r1[ok],c2[ok]]^=True
        cand[ii,ss,r2[ok],c1[ok]]^=True;cand[ii,ss,r2[ok],c2[ok]]^=True
    return cand

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=1800);ap.add_argument("--batch",type=int,default=4096)
    ap.add_argument("--compression9");ap.add_argument("--prefix",default="lp333_dual_gpu");ap.add_argument("--seed",type=int,default=333937)
    ap.add_argument("--seed-json");ap.add_argument("--warm-switches",type=int,default=120);ap.add_argument("--proposals",type=int,default=1);ap.add_argument("--cycle",type=int,default=1500);ap.add_argument("--temperature",type=float,default=4000.);a=ap.parse_args()
    assert torch.cuda.is_available();dev=torch.device("cuda");col=columns(a.compression9);rng=np.random.default_rng(a.seed)
    if a.seed_json:
        seq=np.asarray(json.loads(Path(a.seed_json).read_text())["sequences"],dtype=np.int8)
        base=np.zeros((2,P,Q),dtype=np.bool_)
        for r in range(P):
            for c in range(Q):base[:,r,c]=seq[:,crt(r,c)]==1
        exact_state(base,col,0.,0)
    else:base=np.stack([realization(s,col,rng) for s in range(2)])
    g=torch.from_numpy(np.broadcast_to(base,(a.batch,2,P,Q)).copy()).to(dev)
    gen=torch.Generator(device=dev);gen.manual_seed(a.seed);idx=torch.tensor([crt(r,c) for r in range(P) for c in range(Q)],device=dev)
    def energy(x):
        nb=x.shape[0];z=(x.reshape(nb,2,N).to(torch.float32)*2-1);seq=torch.empty_like(z);seq.index_copy_(2,idx,z)
        f=torch.fft.rfft(seq,dim=2);p=torch.fft.irfft((f.real*f.real+f.imag*f.imag).sum(dim=1),n=N,dim=1)
        rr=torch.round(p[:,1:H+1]).to(torch.int64)+2;return (rr*rr).sum(dim=1)
    for _ in range(a.warm_switches):g=propose(g,gen,1)
    g[:a.batch//4]=torch.from_numpy(base).to(dev)
    torch.cuda.synchronize();start=time.time();e=energy(g);moves=0;best_e=int(e.min());best_g=g[int(e.argmin())].detach().cpu().numpy();last_write=0.
    z=exact_state(best_g,col,0.,0);assert z["energy"]==best_e;print(json.dumps({"event":"seed","energy":best_e,"batch":a.batch}),flush=True)
    scales=torch.exp(torch.linspace(math.log(.2),math.log(5.),a.batch,device=dev));step=0
    while time.time()-start<a.seconds and best_e:
        phase=(step%a.cycle)/a.cycle;temp=(a.temperature*(0.0005**phase)+.05)*scales
        compound=1 if step%10<8 else (2 if step%10==8 else 3)
        if a.proposals>1:
            expanded=g[:,None].expand(-1,a.proposals,-1,-1,-1).reshape(a.batch*a.proposals,2,P,Q)
            pool=propose(expanded,gen,compound);pe=energy(pool).reshape(a.batch,a.proposals);ne,j=pe.min(dim=1)
            cand=pool.reshape(a.batch,a.proposals,2,P,Q)[torch.arange(a.batch,device=dev),j]
        else:cand=propose(g,gen,compound);ne=energy(cand)
        de=ne-e
        accept=(de<=0)|(torch.rand(a.batch,device=dev,generator=gen)<torch.exp(-de.to(torch.float32)/temp))
        g=torch.where(accept[:,None,None,None],cand,g);e=torch.where(accept,ne,e);moves+=int(accept.sum())*compound;step+=1
        cur=int(e.min())
        if cur<best_e:
            j=int(e.argmin());candidate=g[j].detach().cpu().numpy();exact=exact_state(candidate,col,time.time()-start,moves)
            assert exact["energy"]==cur;best_e=cur;best_g=candidate
            now=time.time();
            if now-last_write>.5 or best_e==0:
                Path(a.prefix+"_live.json").write_text(json.dumps(exact,separators=(",",":"))+"\n");last_write=now
            print(json.dumps({"event":"best","energy":best_e,"nonzero":exact["nonzero"],"maxabs":exact["maxabs"],"elapsed_s":exact["elapsed_s"],"steps":step,"moves":moves}),flush=True)
        if step%a.cycle==0:
            # Preserve the better half; restart the worse half from the global record.
            worst=torch.topk(e,a.batch//2,largest=True).indices;bg=torch.from_numpy(best_g).to(dev)
            g[worst]=bg;e[worst]=best_e
    exact=exact_state(best_g,col,time.time()-start,moves);out=a.prefix+("_candidate.json" if exact["solved"] else "_summary.json")
    Path(out).write_text(json.dumps(exact,separators=(",",":"))+"\n");print(json.dumps({"event":"result","solved":exact["solved"],"energy":exact["energy"],"output":out}),flush=True)
if __name__=="__main__":main()
