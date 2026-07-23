"""SAT encoding for exact residual-mod-4 repair with fixed mod-4 margins."""
from __future__ import annotations

import argparse, hashlib, json, threading, time
from pathlib import Path

from pysat.formula import CNFPlus, IDPool
from pysat.solvers import Solver

LENGTHS = (84, 84, 83, 83)


def residual(a):
    return [sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in a)
            for d in range(1, 84)]


def margins(a):
    rows = [sum(x) for x in a]
    alts = [sum(v if i % 2 == 0 else -v for i, v in enumerate(x)) for x in a]
    z4 = []
    for x in a:
        z4 += [sum(v for i,v in enumerate(x) if i%4==0)-sum(v for i,v in enumerate(x) if i%4==2),
               sum(v for i,v in enumerate(x) if i%4==1)-sum(v for i,v in enumerate(x) if i%4==3)]
    return rows, alts, z4


def xor_equiv(cnf, a, b, y):
    cnf.extend([[a,b,-y],[-a,-b,-y],[a,-b,y],[-a,b,y]])


def add_equals(cnf, literals, bound):
    if bound == 0:
        cnf.extend([[-x] for x in literals])
    elif bound == len(literals):
        cnf.extend([[x] for x in literals])
    else:
        cnf.append([literals, bound], is_atmost=True)
        cnf.append([[-x for x in literals], len(literals)-bound], is_atmost=True)


def main():
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=120);p.add_argument('--max-changes',type=int,required=True);p.add_argument('--output',type=Path,default=Path('agent_bsd_repair_sat_pb0.json'));args=p.parse_args()
    start=time.time();data=json.loads(args.input.read_text(encoding='utf8'));a=[[int(v) for v in x] for x in data['sequences']]
    if tuple(map(len,a))!=LENGTHS:raise ValueError('bad lengths')
    r0=residual(a);before=margins(a);pool=IDPool();f=[[pool.id(f'f_{k}_{i}') for i in range(n)] for k,n in enumerate(LENGTHS)];cnf=CNFPlus()
    # Fixed final negative count in each residue class modulo four.
    for k,x in enumerate(a):
        for c in range(4):
            positions=list(range(c,len(x),4));lits=[f[k][i] if x[i]==1 else -f[k][i] for i in positions];add_equals(cnf,lits,sum(x[i]==-1 for i in positions))
    # Linear mod-4 autocorrelation repair equations, encoded as XOR chains.
    for d in range(1,84):
        odd=set()
        for k,n in enumerate(LENGTHS):
            for i in range(n-d):
                for key in ((k,i),(k,i+d)):
                    if key in odd:odd.remove(key)
                    else:odd.add(key)
        lits=[f[k][i] for k,i in sorted(odd)];want=(r0[d-1]//2)&1
        if len(lits)==1:cnf.append([lits[0] if want else -lits[0]])
        else:
            acc=lits[0]
            for j,b in enumerate(lits[1:],1):
                y=pool.id(f'xor_{d}_{j}');xor_equiv(cnf,acc,b,y);acc=y
            cnf.append([acc if want else -acc])
    cnf.append([[v for row in f for v in row],args.max_changes],is_atmost=True)
    print(json.dumps({'event':'built','vars':pool.top,'clauses':len(cnf.clauses),'atmosts':len(cnf.atmosts),'max_changes':args.max_changes,'seed_pb':sum(x%4!=0 for x in r0),'elapsed_s':time.time()-start}),flush=True)
    with Solver(name='minicard',use_timer=True) as solver:
        solver.append_formula(cnf.clauses)
        for lits,bound in cnf.atmosts:solver.add_atmost(lits,bound)
        solver.set_phases([-v for row in f for v in row])
        timer=threading.Timer(args.seconds,solver.interrupt);timer.start()
        try:sat=solver.solve_limited(expect_interrupt=True)
        finally:timer.cancel()
        print(json.dumps({'event':'result','sat':sat,'stats':solver.accum_stats(),'elapsed_s':time.time()-start}),flush=True)
        if sat is not True:return 2 if sat is None else 1
        model=set(solver.get_model())
    b=[[-x if f[k][i] in model else x for i,x in enumerate(row)] for k,row in enumerate(a)];rr=residual(b);after=margins(b);changed=[(k,i) for k,row in enumerate(f) for i,v in enumerate(row) if v in model]
    if before!=after or any(x%4 for x in rr):raise RuntimeError((before,after,rr))
    payload={'construction':'base sequences BS(84,83)','search':'agent SAT exact parity repair','solved':not any(rr),'independently_recomputed':True,'energy':sum(x*x for x in rr),'l1':sum(map(abs,rr)),'parity_bad':0,'changes':len(changed),'changed_positions':changed,'elapsed_s':time.time()-start,'row_sums':after[0],'alternating_sums':after[1],'z4_components':after[2],'residual':rr,'sequences':b}
    raw=(json.dumps(payload,indent=2)+'\n').encode();args.output.write_bytes(raw);print(json.dumps({'event':'verified_parity0','energy':payload['energy'],'l1':payload['l1'],'changes':len(changed),'sha256':hashlib.sha256(raw).hexdigest(),'output':str(args.output)}),flush=True);return 0


if __name__=='__main__':raise SystemExit(main())
