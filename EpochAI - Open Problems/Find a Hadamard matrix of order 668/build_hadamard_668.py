"""Build and independently verify H668 from supported exact constructions."""
from __future__ import annotations
import argparse,csv,hashlib,json
from pathlib import Path
import numpy as np
def expand(r):return [1 if j%2==0 else -1 for j,n in enumerate(r) for _ in range(n)]
def circulant(x):
 n=len(x);a=np.asarray(x,dtype=np.int64);return np.stack([np.roll(a,i) for i in range(n)])
def base_to_golay(base):
 A,B,C,D=base;m=len(A);n=len(C);zm=[0]*m;zn=[0]*n
 if len(B)!=m or len(D)!=n:raise ValueError('base-sequence length pairing failure')
 t1=[(x+y)//2 for x,y in zip(A,B)]+zn
 t2=[(x-y)//2 for x,y in zip(A,B)]+zn
 t3=zm+[(x+y)//2 for x,y in zip(C,D)]
 t4=zm+[(x-y)//2 for x,y in zip(C,D)]
 if any(sum(v!=0 for v in x)!=1 for x in zip(t1,t2,t3,t4)):raise ValueError('base-to-T support failure')
 return [[a+b+c+d for a,b,c,d in zip(t1,t2,t3,t4)],
         [a-b+c-d for a,b,c,d in zip(t1,t2,t3,t4)],
         [a+b-c-d for a,b,c,d in zip(t1,t2,t3,t4)],
         [a-b-c+d for a,b,c,d in zip(t1,t2,t3,t4)]]
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--output',type=Path,default=Path('hadamard_668.csv'));a=p.parse_args();data=json.loads(a.input.read_text(encoding='utf8'))
 if 'sequences' in data:seq=data['sequences']
 else:
  s=data['s'];q=expand([83,2,81,1]);f=[1]*84+[-1]*83;seq=[s,[x*y for x,y in zip(s,f)],[x*y for x,y in zip(s,q)],[x*y*z for x,y,z in zip(s,q,f)]]
 lengths=[len(x) for x in seq];construction=str(data.get('construction','')).lower();williamson=construction.startswith('williamson');periodic_gs=construction.startswith('cyclic goethals-seidel');legendre_pair=construction.startswith('legendre pair') and lengths==[333,333];turyn_type=construction.startswith('turyn-type') or construction.startswith('tt(56)')
 if legendre_pair:
  if any(x not in (-1,1) for row in seq for x in row):raise ValueError('Legendre-pair entry failure')
  if [sum(x) for x in seq]!=[1,1]:raise ValueError('expected normalized Legendre-pair sums [1,1]')
  periodic=[2+sum(x[i]*x[(i+d)%333] for x in seq for i in range(333)) for d in range(1,333)]
  if any(periodic):raise ValueError(f'not a Legendre pair: {[(i+1,x) for i,x in enumerate(periodic) if x]}')
 elif williamson:
  if lengths!=[167]*4:raise ValueError('expected four Williamson sequences of length 167')
  if any(x[i]!=x[-i] for x in seq for i in range(1,167)):raise ValueError('Williamson symmetry failure')
  periodic=[sum(x[i]*x[(i+d)%167] for x in seq for i in range(167)) for d in range(1,167)]
  if any(periodic):raise ValueError(f'not Williamson: {[(i+1,x) for i,x in enumerate(periodic) if x]}')
 elif periodic_gs:
  if lengths!=[167]*4:raise ValueError('expected four cyclic Goethals-Seidel sequences of length 167')
  periodic=[sum(x[i]*x[(i+d)%167] for x in seq for i in range(167)) for d in range(1,167)]
  if any(periodic):raise ValueError(f'not a cyclic Goethals-Seidel family: {[(i+1,x) for i,x in enumerate(periodic) if x]}')
 elif turyn_type:
  if lengths!=[56,56,56,55]:raise ValueError('expected TT(56) lengths 56,56,56,55')
  tt_residual=[sum(w*sum(x[i]*x[i+d] for i in range(len(x)-d)) for x,w in zip(seq,(1,1,2,2))) for d in range(1,56)]
  if any(tt_residual):raise ValueError(f'not TT(56): {[(i+1,x) for i,x in enumerate(tt_residual) if x]}')
  A,B,C,D=seq;seq=base_to_golay([C+D,C+[-x for x in D],A,B])
 elif lengths[0]==lengths[1] and lengths[2]==lengths[3] and lengths[0]+lengths[2]==167:
  max_shift=max(lengths[0],lengths[2])
  base_residual=[sum(sum(x[i]*x[i+d] for i in range(len(x)-d)) for x in seq) for d in range(1,max_shift)]
  if any(base_residual):raise ValueError(f'not base sequences: {[(i+1,x) for i,x in enumerate(base_residual) if x]}')
  seq=base_to_golay(seq)
 elif lengths!=[167]*4:raise ValueError('expected LP(333), four length-167 Golay sequences, or BS lengths 84,84,83,83')
 if legendre_pair:
  A,B=map(circulant,seq);one=np.ones((333,1),dtype=np.int64);row=np.ones(333,dtype=np.int64)
  top1=np.concatenate(([-1,-1],row,row));top2=np.concatenate(([-1,1],row,-row))
  lower1=np.hstack((one,one,A,B));lower2=np.hstack((one,-one,B.T,-A.T))
  H=np.vstack((top1,top2,lower1,lower2))
 elif williamson:
  A,B,C,D=map(circulant,seq);blocks=[[A,B,C,D],[-B,A,-D,C],[-C,D,A,-B],[-D,-C,B,A]];H=np.block(blocks)
 else:
  if not periodic_gs:
   residual=[sum(x[i]*x[i+d] for x in seq for i in range(167-d)) for d in range(1,167)]
   if any(residual):raise ValueError(f'not a Golay quadruple: {[(i+1,x) for i,x in enumerate(residual) if x]}')
  A,B,C,D=map(circulant,seq);R=np.fliplr(np.eye(167,dtype=np.int64));blocks=[[A,-B@R,-C@R,-D@R],[B@R,A,-D.T@R,C.T@R],[C@R,D.T@R,A,-B.T@R],[D@R,-C.T@R,B.T@R,A]];H=np.block(blocks)
 if H.shape!=(668,668) or not np.all((H==1)|(H==-1)):raise RuntimeError('shape/entry failure')
 gram=H@H.T;diag=np.diag(gram);off=gram-np.diag(diag)
 if not np.all(diag==668) or np.any(off):raise RuntimeError(f'Gram failure max_off={np.max(np.abs(off))}')
 with a.output.open('w',newline='',encoding='ascii') as fh:csv.writer(fh,lineterminator='\n').writerows(H.tolist())
 digest=hashlib.sha256(a.output.read_bytes()).hexdigest();print(json.dumps({'output':str(a.output),'rows':668,'columns':668,'entries':'{-1,+1}','gram':'668 I','sha256':digest}))
if __name__=='__main__':main()
