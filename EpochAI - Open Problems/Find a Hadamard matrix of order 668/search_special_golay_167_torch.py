"""GPU-parallel binary relaxation in the parity-feasible special Golay space.

The GPU is only a candidate generator.  Every reported best is rounded to exact
signs and checked with integer autocorrelations on the CPU.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import torch


def expand_runs(runs: list[int]) -> list[int]:
    return [1 if j % 2 == 0 else -1 for j,n in enumerate(runs) for _ in range(n)]


Q = expand_runs([83,2,81,1])
F = [1]*84+[-1]*83


def exact_residual(s: list[int]) -> list[int]:
    return [sum(s[i]*s[i+d] for i in range(167-d) if F[i]==F[i+d] and Q[i]==Q[i+d]) for d in range(1,84)]


def main() -> int:
    p=argparse.ArgumentParser()
    p.add_argument("--steps",type=int,default=3000)
    p.add_argument("--batch",type=int,default=4096)
    p.add_argument("--lr",type=float,default=0.025)
    p.add_argument("--seed",type=int,default=668)
    p.add_argument("--input",type=Path,default=Path("Find a Hadamard matrix of order 668/special_golay_167_native_summary.json"))
    p.add_argument("--output",type=Path,default=Path("Find a Hadamard matrix of order 668/special_golay_167_torch_summary.json"))
    args=p.parse_args()
    if not torch.cuda.is_available(): raise RuntimeError("CUDA is unavailable")
    torch.manual_seed(args.seed);torch.cuda.manual_seed_all(args.seed)
    base=json.loads(args.input.read_text(encoding="utf-8"))["s"]

    # 82 mirrored pairs plus three unconstrained center signs form a complete
    # 85-dimensional basis for the parity-feasible affine space.
    group=[-1]*167;g=0
    for i in range(41):group[i]=group[82-i]=g;g+=1
    for i in range(41):group[84+i]=group[166-i]=g;g+=1
    for i in (41,83,125):group[i]=g;g+=1
    assert g==85 and min(group)>=0
    device="cuda"
    group_t=torch.tensor(group,device=device,dtype=torch.long)
    base_t=torch.tensor(base,device=device,dtype=torch.float32)
    masks=[]
    for d in range(1,84):masks.append(torch.tensor([1.0 if F[i]==F[i+d] and Q[i]==Q[i+d] else 0.0 for i in range(167-d)],device=device))

    z=torch.randn((args.batch,85),device=device)*0.5
    z[0].fill_(2.0)  # retain the native incumbent in the population
    z.requires_grad_(True)
    opt=torch.optim.Adam([z],lr=args.lr)
    best_energy=sum(x*x for x in exact_residual(base));best=base[:]
    started=time.time()
    for step in range(args.steps):
        opt.zero_grad(set_to_none=True)
        hard=torch.where(z>=0,torch.ones_like(z),-torch.ones_like(z))
        u=z+(hard-z).detach()  # straight-through binary estimator
        s=base_t.unsqueeze(0)*u[:,group_t]
        rs=[]
        for d in range(1,84):rs.append(((s[:,:167-d]*s[:,d:])*masks[d-1]).sum(dim=1))
        r=torch.stack(rs,dim=1)
        loss=((r*r).mean(dim=1)+(r.sum(dim=1)**2)/332.0).mean()
        loss.backward();opt.step()
        with torch.no_grad():z.clamp_(-3,3)
        if step%20==0 or step+1==args.steps:
            with torch.no_grad():
                e=(r*r).sum(dim=1);value,index=e.min(dim=0);candidate_energy=int(value.item());idx=int(index.item())
                if candidate_energy<best_energy:
                    signs=(base_t*hard[idx,group_t]).to(torch.int8).cpu().tolist()
                    rr=exact_residual(signs);checked=sum(x*x for x in rr)
                    if checked!=candidate_energy:raise RuntimeError((checked,candidate_energy))
                    best_energy=checked;best=signs
                    print(json.dumps({"event":"best","energy":best_energy,"step":step,"elapsed_s":time.time()-started}),flush=True)
                    args.output.write_text(json.dumps({"construction":"special Golay quadruple length 167","solved":best_energy==0,"energy_normalized":best_energy,"steps":step,"elapsed_s":time.time()-started,"residual_divided_by_4":rr,"s":best},indent=2)+"\n",encoding="utf-8")
                    if best_energy==0:return 0
            # Re-randomize a quarter of the batch to prevent population collapse.
            if step and step%400==0:
                with torch.no_grad():z[-args.batch//4:].normal_(0,0.6)
    print(json.dumps({"event":"result","solved":best_energy==0,"energy":best_energy,"elapsed_s":time.time()-started,"output":str(args.output)}),flush=True)
    return 0 if best_energy==0 else 2


if __name__=="__main__":raise SystemExit(main())
