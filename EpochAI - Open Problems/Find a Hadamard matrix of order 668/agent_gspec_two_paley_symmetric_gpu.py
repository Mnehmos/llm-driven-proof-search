"""GPU annealing for two symmetric rows plus two fixed Paley rows at n=167."""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import torch

N, H, O = 167, 83, 83


def chi(i: int) -> int:
    return 0 if i == 0 else (1 if pow(i, 83, N) == 1 else -1)


def make_seed(seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    rows = []
    for zero, plus_pairs in [(-1, 47), (1, 45)]:
        orbit = np.array([1] * plus_pairs + [-1] * (O - plus_pairs), dtype=np.int8)
        rng.shuffle(orbit)
        row = np.empty(N, dtype=np.int8)
        row[0] = zero
        for j, value in enumerate(orbit, 1):
            row[j] = row[N-j] = value
        rows.append(row)
    paley = np.array([1 if i == 0 else chi(i) for i in range(N)], dtype=np.int8)
    return np.stack((rows[0], rows[1], paley, paley))


def exact(a: np.ndarray, elapsed: float, samples: int, cycles: int) -> dict:
    a = np.asarray(a, dtype=np.int8)
    r = [sum(sum(int(x[i]) * int(x[(i+d) % N]) for i in range(N)) for x in a) for d in range(1, H+1)]
    return {"construction":"cyclic Goethals-Seidel order 167, two Paley and two symmetric rows","search":"agent GPU symmetric-orbit population annealing","solved":not any(r),"independently_recomputed":True,"energy":sum(x*x for x in r),"l1":sum(abs(x) for x in r),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r),default=0),"row_sums":[int(x.sum()) for x in a],"residual":r,"elapsed_s":elapsed,"samples":samples,"cycles":cycles,"sequences":a.astype(int).tolist()}


def energy(x: torch.Tensor):
    f = torch.fft.rfft(x, dim=2)
    ac = torch.fft.irfft((f.real.square()+f.imag.square()).sum(1), n=N, dim=1)
    r = torch.round(ac[:,1:H+1]).long()
    return (r*r).sum(1)


def proposal(x: torch.Tensor) -> torch.Tensor:
    b = x.shape[0]
    dev = x.device
    ids = torch.arange(b, device=dev)
    k = torch.randint(2, (b,), device=dev)
    p = 1 + torch.randint(O, (b,), device=dev)
    bad = x[ids,k,p] != 1
    while bool(bad.any()):
        p[bad] = 1 + torch.randint(O, (int(bad.sum()),), device=dev)
        bad = x[ids,k,p] != 1
    q = 1 + torch.randint(O, (b,), device=dev)
    bad = x[ids,k,q] != -1
    while bool(bad.any()):
        q[bad] = 1 + torch.randint(O, (int(bad.sum()),), device=dev)
        bad = x[ids,k,q] != -1
    y = x.clone()
    y[ids,k,p] = -1; y[ids,k,N-p] = -1
    y[ids,k,q] = 1; y[ids,k,N-q] = 1
    return y


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--batch", type=int, default=8192)
    p.add_argument("--cycle-steps", type=int, default=6000)
    p.add_argument("--init-swaps", type=int, default=30)
    p.add_argument("--temp-high", type=float, default=4000.0)
    p.add_argument("--temp-low", type=float, default=0.05)
    p.add_argument("--seed", type=int, default=211511)
    p.add_argument("--prefix", default="agent_gspec_two_paley_symmetric_gpu")
    q = p.parse_args()
    if not torch.cuda.is_available(): raise SystemExit("CUDA unavailable")
    torch.manual_seed(q.seed)
    dev = torch.device("cuda")
    best = make_seed(q.seed)
    rep = exact(best,0,0,0)
    best_e = rep["energy"]
    started=time.time();samples=0;cycles=0
    print(json.dumps({"event":"seed","energy":best_e,"l1":rep["l1"],"rows":rep["row_sums"],"batch":q.batch}),flush=True)
    while best_e and time.time()-started < q.seconds:
        cycles += 1
        x = torch.from_numpy(best).to(dev).float()[None].expand(q.batch,-1,-1).clone()
        for _ in range(q.init_swaps): x=proposal(x)
        e=energy(x);samples+=q.batch
        for step in range(q.cycle_steps):
            if step%64==0 and time.time()-started>=q.seconds:break
            y=proposal(x);ne=energy(y);samples+=q.batch
            phase=step/max(1,q.cycle_steps-1);temp=q.temp_high*(q.temp_low/q.temp_high)**phase
            de=ne-e;accept=(de<=0)|(torch.rand(q.batch,device=dev)<torch.exp(-de.float()/temp));x[accept]=y[accept];e[accept]=ne[accept]
            cur=int(e.min())
            if cur<best_e:
                j=int(e.argmin());cand=x[j].cpu().numpy().astype(np.int8);chk=exact(cand,time.time()-started,samples,cycles)
                assert chk["energy"]==cur and chk["row_sums"]==[21,15,1,1]
                assert all(cand[k,i]==cand[k,(-i)%N] for k in range(2) for i in range(N))
                best,best_e,rep=cand,cur,chk
                Path(q.prefix+"_live.json").write_text(json.dumps(chk,separators=(",", ":"))+"\n",encoding="utf8")
                print(json.dumps({"event":"best","energy":cur,"l1":chk["l1"],"nonzero":chk["nonzero"],"maxabs":chk["maxabs"],"cycle":cycles,"step":step,"samples":samples,"elapsed_s":chk["elapsed_s"]}),flush=True)
                if not cur:break
    out=exact(best,time.time()-started,samples,cycles)
    name=q.prefix+("_candidate.json" if out["solved"] else "_summary.json")
    Path(name).write_text(json.dumps(out,separators=(",", ":"))+"\n",encoding="utf8")
    print(json.dumps({"event":"result","solved":out["solved"],"energy":out["energy"],"l1":out["l1"],"cycles":cycles,"samples":samples,"output":name}),flush=True)


if __name__ == "__main__": main()
