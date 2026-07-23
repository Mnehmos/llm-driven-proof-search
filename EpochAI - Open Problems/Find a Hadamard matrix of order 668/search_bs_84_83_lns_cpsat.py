"""Exact CP-SAT large-neighborhood search inside a strict BS(84,83) fiber.

Disjoint reversal-orbit moves preserve every row sum and every residual mod 4.
Autocorrelations are quadratic, so their value after any subset of these moves
is represented exactly by singleton and pair-interaction coefficients.
"""
from __future__ import annotations
import argparse,json,random,time
from pathlib import Path
import numpy as np
from ortools.sat.python import cp_model

L=(84,84,83,83)

def corr(x:np.ndarray)->np.ndarray:
    return np.asarray([int(x[:-d]@x[d:]) if d<len(x) else 0 for d in range(1,84)],dtype=np.int64)

def residual(a:list[np.ndarray])->np.ndarray:
    return sum((corr(x) for x in a),np.zeros(83,dtype=np.int64))

def orbit_moves(a:list[np.ndarray]):
    moves=[]
    for k,x in enumerate(a):
        for p in range(len(x)//2):
            q=len(x)-1-p;moves.append((k,(p,q)))
    # Moves are pairwise position-disjoint within each sequence.
    for k in range(4):
        flat=[p for j,pos in moves if j==k for p in pos]
        assert len(flat)==len(set(flat))
    return moves

def flipped(x:np.ndarray,pos:tuple[int,...])->np.ndarray:
    y=x.copy();y[list(pos)]*=-1;return y

def solve_round(a:list[np.ndarray],seconds:float,workers:int,seed:int,optimize:bool=False):
    started=time.time();r0=residual(a);moves=orbit_moves(a);m=len(moves)
    base_corr=[corr(x) for x in a]
    single=[]
    for k,pos in moves:single.append(corr(flipped(a[k],pos))-base_corr[k])
    interactions=[]
    for i in range(m):
        ki,pi=moves[i]
        for j in range(i+1,m):
            kj,pj=moves[j]
            if ki!=kj:continue
            both=flipped(flipped(a[ki],pi),pj)
            z=corr(both)-base_corr[ki]-single[i]-single[j]
            if np.any(z):interactions.append((i,j,z))
    model=cp_model.CpModel();z=[model.new_bool_var(f'z_{i}') for i in range(m)]
    # Flipping one orbit changes its sequence row by -2 times that orbit sum.
    # These four equations make the model cover every row-preserving subset,
    # rather than one arbitrary pairing of ++ and -- orbits.
    for k in range(4):
        model.add(sum((-2*int(a[k][pos[0]]+a[k][pos[1]]))*z[i]
                      for i,(j,pos) in enumerate(moves) if j==k)==0)
    pair=[]
    for i,j,c in interactions:
        w=model.new_bool_var(f'w_{i}_{j}');model.add_multiplication_equality(w,[z[i],z[j]]);pair.append((w,c))
    abs_residual=[]
    for d in range(83):
        terms=[int(r0[d])]
        terms.extend(int(single[i][d])*z[i] for i in range(m) if single[i][d])
        terms.extend(int(c[d])*w for w,c in pair if c[d])
        expr=sum(terms)
        if optimize:
            rd=model.new_int_var(-334,334,f'r_{d}');ad=model.new_int_var(0,334,f'ar_{d}');model.add(rd==expr);model.add_abs_equality(ad,rd);abs_residual.append(ad)
        else:model.add(expr==0)
    if optimize:model.minimize(sum(abs_residual))
    for v in z:model.add_hint(v,0)
    solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=seconds;solver.parameters.num_search_workers=workers;solver.parameters.random_seed=seed;solver.parameters.cp_model_presolve=True
    status=solver.solve(model);name=solver.status_name(status)
    stats={'status':name,'moves':m,'pair_variables':len(pair),'elapsed_s':time.time()-started,'conflicts':solver.num_conflicts,'branches':solver.num_branches,'wall_time':solver.wall_time,'objective':solver.objective_value if optimize and status in (cp_model.OPTIMAL,cp_model.FEASIBLE) else None,'best_bound':solver.best_objective_bound if optimize else None}
    print(json.dumps({'event':'round','seed':seed,**stats}),flush=True)
    if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):return None,stats
    b=[x.copy() for x in a]
    selected=[]
    for i,(k,pos) in enumerate(moves):
        if solver.value(z[i]):b[k][list(pos)]*=-1;selected.append(i)
    rr=residual(b)
    if not optimize and np.any(rr):raise RuntimeError(('quadratic model mismatch',rr.tolist()))
    if [int(x.sum()) for x in b]!=[int(x.sum()) for x in a]:raise RuntimeError('row drift')
    return b,{**stats,'selected_moves':selected}

def main():
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=900);p.add_argument('--round-seconds',type=float,default=300);p.add_argument('--workers',type=int,default=8);p.add_argument('--seed',type=int,default=668);p.add_argument('--optimize',action='store_true');p.add_argument('--output',type=Path,default=Path('bs_84_83_lns_candidate.json'));args=p.parse_args()
    data=json.loads(args.input.read_text(encoding='utf8'));a=[np.asarray(x,dtype=np.int8) for x in data['sequences']]
    if tuple(map(len,a))!=L:raise ValueError('expected BS(84,83) sequences')
    r=residual(a);rows=[int(x.sum()) for x in a]
    if any(int(x)%4 for x in r) or sum(x*x for x in rows)!=334:raise ValueError('input is not a strict row/parity checkpoint')
    deadline=time.time()+args.seconds;round_no=0;history=[]
    while time.time()<deadline:
        budget=min(args.round_seconds,max(1.0,deadline-time.time()));b,stats=solve_round(a,budget,args.workers,args.seed+round_no,args.optimize);history.append(stats);round_no+=1
        if b is None:continue
        rr=residual(b);energy=int(rr@rr);payload={'construction':'base sequences BS(84,83)','solver':'CP-SAT full reversal-orbit LNS','solved':not np.any(rr),'energy':energy,'row_sums':[int(x.sum()) for x in b],'residual':rr.tolist(),'history':history,'sequences':[x.astype(int).tolist() for x in b]}
        if not np.any(rr):args.output.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf8');print(json.dumps({'event':'verified_witness','output':str(args.output)}),flush=True);return 0
        if args.optimize and energy<int(residual(a)@residual(a)):
            tag='_'.join(str(int(x.sum())) for x in a);Path(f'bs_84_83_lns_opt_{tag}_live.json').write_text(json.dumps(payload,indent=2)+'\n',encoding='utf8');a=b;print(json.dumps({'event':'improved','energy':energy}),flush=True)
    print(json.dumps({'event':'result','solved':False,'rounds':round_no,'history':history}),flush=True);return 2

if __name__=='__main__':raise SystemExit(main())
