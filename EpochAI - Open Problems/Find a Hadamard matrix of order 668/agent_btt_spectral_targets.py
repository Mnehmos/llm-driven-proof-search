"""Nearest weighted order-3/order-5 TT(56) compression shells with GF(2) filtering."""
from __future__ import annotations
import argparse,hashlib,itertools,json
from collections import defaultdict
from pathlib import Path
L=(56,56,56,55);W=(1,1,2,2);OFF=(0,56,112,168)
def compression(x,m):return tuple(sum(x[r::m])for r in range(m))
def counts(n,m):return tuple(len(range(r,n,m))for r in range(m))
def cubic(v):a,b,c=v;return a*a+b*b+c*c-a*b-b*c-c*a
def quintic(v):
 s0=sum(x*x for x in v);s1=sum(v[i]*v[(i+1)%5]for i in range(5));s2=sum(v[i]*v[(i+2)%5]for i in range(5));return s0-s1,s1-s2
def local(base,caps,radius):
 pre=[]
 def go(i,used,total):
  if i==len(base)-1:
   d=-total
   if d%2 or used+abs(d)>radius:return
   v=base[i]+d
   if -caps[i]<=v<=caps[i]and(v-caps[i])%2==0:yield used+abs(d),tuple(pre+[v])
   return
  for d in range(-(radius-used),radius-used+1,2):
   v=base[i]+d
   if -caps[i]<=v<=caps[i]and(v-caps[i])%2==0:pre.append(v);yield from go(i+1,used+abs(d),total+d);pre.pop()
 yield from go(0,0,0)
def add(a,b):return a+b if isinstance(a,int)else tuple(x+y for x,y in zip(a,b))
def sub(a,b):return a-b if isinstance(a,int)else tuple(x-y for x,y in zip(a,b))
def scale(x,w):return x*w if isinstance(x,int)else tuple(w*y for y in x)
def mask(k,positions):return sum(1<<(OFF[k]+i)for i in positions)
def append_margin(eq,k,m,target):
 for r,s in enumerate(target):
  pos=list(range(r,L[k],m));assert(len(pos)-s)%2==0;eq.append((mask(k,pos),((len(pos)-s)//2)&1))
def extend(basis,eq):
 b=basis.copy()
 for x,rhs in eq:
  while x:
   p=(x&-x).bit_length()-1
   if p not in b:b[p]=(x,rhs);break
   x^=b[p][0];rhs^=b[p][1]
  if not x and rhs:return None
 return b
def base_basis(a):
 eq=[]
 for d in range(1,56):
  x=0
  for k in range(2):
   x^=mask(k,(p for p in range(56)if(p<d)^(p>=56-d)))
  constant=2*(56-d)+2*((56-d)+max(0,55-d));eq.append((x,(constant//2)&1))
 for k in range(4):append_margin(eq,k,4,compression(a[k],4))
 b=extend({},eq);assert b is not None;return b
def with_target(b,m,t):
 eq=[]
 for k in range(4):append_margin(eq,k,m,t[k])
 return extend(b,eq)
def groups(a,m,radius,value):
 out=[]
 for k in range(4):
  g=defaultdict(lambda:defaultdict(list));base=compression(a[k],m)
  for cost,t in local(base,counts(L[k],m),radius):g[cost][scale(value(t),W[k])].append(t)
  out.append(g)
 return out
def shell(a,m,value,invariant,basis,max_radius,limit):
 bases=[compression(x,m)for x in a]
 for radius in range(0,max_radius+1,4):
  gs=groups(a,m,radius,value);total=ok=0;records=[]
  allowed=range(0,radius+1,4)
  for cs in itertools.product(allowed,repeat=4):
   if sum(cs)!=radius:continue
   left=defaultdict(list)
   for ka,va in gs[0][cs[0]].items():
    for kb,vb in gs[1][cs[1]].items():left[add(ka,kb)].extend((x,y)for x in va for y in vb)
   for kc,vc in gs[2][cs[2]].items():
    for kd,vd in gs[3][cs[3]].items():
     need=sub(invariant,add(kc,kd));pairs=left.get(need,())
     for x,y in pairs:
      for z in vc:
       for u in vd:
        total+=1;t=(x,y,z,u);nb=with_target(basis,m,t);good=nb is not None
        if good:
         ok+=1
         if len(records)<limit:records.append({'target':[list(q)for q in t],'local_l1':radius,'gf2_rank':len(nb)})
  if ok:
   records.sort(key=lambda q:q['target']);return {'modulus':m,'current':[list(x)for x in bases],'current_value':sum(W[k]*value(bases[k])for k in range(4))if m==3 else tuple(sum(W[k]*value(bases[k])[j]for k in range(4))for j in range(2)),'proved_nearest_total_l1':radius,'aggregate_target_count':total,'compatible_target_count':ok,'targets':records}
 return None
def main():
 p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--limit',type=int,default=2000);p.add_argument('--output',type=Path,default=Path('agent_btt_spectral_targets.json'));g=p.parse_args();q=json.loads(g.input.read_text())['sequences'];a=[q[k][:L[k]]for k in range(4)];base=base_basis(a);o3=shell(a,3,cubic,334,base,40,g.limit);assert o3 and o3['targets'];t3=tuple(tuple(x)for x in o3['targets'][0]['target']);b3=with_target(base,3,t3);assert b3 is not None;o5=shell(a,5,quintic,(334,0),b3,48,g.limit);c4=[compression(x,4)for x in a];z4=[v for x in c4 for v in(x[0]-x[2],x[1]-x[3])];out={'construction':'TT(56) weighted nearest spectral targets','source':str(g.input),'weights':W,'fixed_rows':[sum(x)for x in a],'fixed_alts':[sum(v if i%2==0 else-v for i,v in enumerate(x))for x in a],'fixed_z4':z4,'base_gf2_rank':len(base),'order3':o3,'order5_conditioned_on_order3':o5};raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'base_rank':len(base),'order3':{k:o3[k]for k in('current_value','proved_nearest_total_l1','aggregate_target_count','compatible_target_count')},'chosen3':o3['targets'][0],'order5':None if o5 is None else{k:o5[k]for k in('current_value','proved_nearest_total_l1','aggregate_target_count','compatible_target_count')},'chosen5':None if o5 is None else o5['targets'][0],'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}))
if __name__=='__main__':main()
