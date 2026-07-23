"""Direct MiniCard driver for the strict E800 TT(56) Fourier fibre."""
from __future__ import annotations
import argparse,json,threading,time,traceback
from pathlib import Path
from pysat.solvers import Minicard
from search_tt56_pysat import add_equals,build,verify
L=(56,56,56,55)
def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=900);p.add_argument('--no-interrupt',action='store_true');p.add_argument('--spectral',type=Path);p.add_argument('--order5-index',type=int,default=0);p.add_argument('--input',type=Path,default=Path('agent_btt_e800_verified.json'));p.add_argument('--output',type=Path,default=Path('agent_btt_minicard_candidate.json'));g=p.parse_args();st=time.time();rows=(10,8,6,7);alts=(-10,0,-6,9);z4=(0,2,0,-4,0,6,0,-11);cnf,bits,pool=build(True,rows,alts,z4,False);spectral=None
 if g.spectral:
  spectral=json.loads(g.spectral.read_text());targets=[(3,spectral['order3']['targets'][0]['target']),(5,spectral['order5_conditioned_on_order3']['targets'][g.order5_index]['target'])]
  for modulus,target in targets:
   for k,row in enumerate(bits):
    for residue,target_sum in enumerate(target[k]):
     pos=row[residue::modulus];assert(len(pos)-target_sum)%2==0;add_equals(cnf,pool,list(pos),(len(pos)-target_sum)//2,True)
 seed=json.loads(g.input.read_text())['sequences'];assert tuple(map(len,seed))==L;print(json.dumps({'event':'built','variables':pool.top,'clauses':len(cnf.clauses),'native_atmosts':len(cnf.atmosts),'spectral':str(g.spectral)if g.spectral else None,'order5_index':g.order5_index if g.spectral else None,'elapsed_s':time.time()-st}),flush=True)
 try:
  with Minicard(bootstrap_with=cnf.clauses,use_timer=True) as s:
   for lits,bound in cnf.atmosts:s.add_atmost(lits,bound)
   phases=[v if sign==-1 else-v for row,signs in zip(bits,seed) for v,sign in zip(row,signs)];s.set_phases(phases);print(json.dumps({'event':'launched','native_atmosts':len(cnf.atmosts),'phase_literals':len(phases)}),flush=True)
   if g.no_interrupt:sat=s.solve()
   else:
    timer=threading.Timer(g.seconds,s.interrupt);timer.start()
    try:sat=s.solve_limited(expect_interrupt=True)
    finally:timer.cancel()
   print(json.dumps({'event':'raw_result','sat':sat,'elapsed_s':time.time()-st}),flush=True)
   try:stats=s.accum_stats()
   except Exception as e:stats={'stats_error':repr(e)}
   print(json.dumps({'event':'result','sat':sat,'stats':stats,'elapsed_s':time.time()-st}),flush=True)
   if sat is not True:return 2 if sat is None else 1
   model=set(s.get_model())
 except BaseException as e:
  print(json.dumps({'event':'exception','type':type(e).__name__,'message':str(e),'traceback':traceback.format_exc(),'elapsed_s':time.time()-st}),flush=True);return 3
 a=[[-1 if v in model else 1 for v in row]for row in bits];r=verify(a);assert not any(r);out={'construction':'TT(56)','solver':'MiniCard direct strict E800 fibre','solved':True,'independently_recomputed':True,'row_sums':list(rows),'alternating_row_sums':list(alts),'z4_components':list(z4),'spectral_targets':spectral,'residual':r,'sequences':a};g.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'event':'verified_witness','output':str(g.output)}),flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
