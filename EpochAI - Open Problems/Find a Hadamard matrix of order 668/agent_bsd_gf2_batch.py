"""Batch GF(2) quartic-fibre counts for all 12 canonical row types."""
from __future__ import annotations
import hashlib,itertools,json,time
from collections import Counter
from pathlib import Path
L=(84,84,83,83)
TYPES=[(0,6,3,17),(0,10,3,15),(0,18,1,3),(2,4,5,17),(2,16,5,7),(4,10,7,13),(4,14,1,11),(6,8,3,15),(8,10,1,13),(8,10,7,11),(8,14,5,7),(10,12,3,9)]
def signed_tuples():
 out=set()
 for t in TYPES:
  for e in set(itertools.permutations(t[:2])):
   for o in set(itertools.permutations(t[2:])):
    for s in itertools.product((-1,1),repeat=4):out.add(tuple(v*q for v,q in zip(e+o,s)))
 return sorted(out)
def dependencies():
 off=[];z=0
 for n in L:off.append(z);z+=n
 rows=[];base=0
 for d in range(1,84):
  m=0;terms=0
  for k,n in enumerate(L):
   for i in range(n-d):m^=1<<(off[k]+i);m^=1<<(off[k]+i+d);terms+=1
  rows.append([m,1<<(d-1)]);base|=((terms//2)&1)<<(d-1)
 for k,n in enumerate(L):
  for c in range(4):rows.append([sum(1<<(off[k]+i) for i in range(c,n,4)),1<<(83+4*k+c)])
 rank=0
 for col in range(sum(L)):
  h=next((j for j in range(rank,len(rows)) if rows[j][0]>>col&1),None)
  if h is None:continue
  rows[rank],rows[h]=rows[h],rows[rank]
  for j in range(len(rows)):
   if j!=rank and rows[j][0]>>col&1:rows[j][0]^=rows[rank][0];rows[j][1]^=rows[rank][1]
  rank+=1
 return rank,[c for m,c in rows if m==0],base
def main():
 st=time.time();rank,deps,base=dependencies();base_syn=sum(((base&d).bit_count()&1)<<j for j,d in enumerate(deps));alts=signed_tuples();cache={}
 def summary(k,row,alt):
  key=(k,row,alt)
  if key in cache:return cache[key]
  n=L[k];lens=[len(range(c,n,4)) for c in range(4)];ev=(row+alt)//2 if (row+alt)%2==0 else 999;od=(row-alt)//2 if (row-alt)%2==0 else 999;cnt=Counter()
  for u in range(-n,n+1):
   if (ev+u)%2:continue
   s0=(ev+u)//2;s2=(ev-u)//2
   if abs(s0)>lens[0] or abs(s2)>lens[2] or (lens[0]-s0)%2 or (lens[2]-s2)%2:continue
   for v in range(-n,n+1):
    if (od+v)%2:continue
    s1=(od+v)//2;s3=(od-v)//2
    if abs(s1)>lens[1] or abs(s3)>lens[3] or (lens[1]-s1)%2 or (lens[3]-s3)%2:continue
    q=u*u+v*v
    if q>334:continue
    np=[((lens[c]-s)//2)&1 for c,s in enumerate((s0,s1,s2,s3))];syn=0
    for j,d in enumerate(deps):
     bit=sum(np[c]*((d>>(83+4*k+c))&1) for c in range(4))&1;syn|=bit<<j
    cnt[q,syn]+=1
  cache[key]=cnt;return cnt
 all_rows=[]
 for ri,row in enumerate(TYPES):
  records=[];tf=tc=0
  for alt in alts:
   parts=[summary(k,row[k],alt[k]) for k in range(4)]
   if any(not x for x in parts):continue
   dp={(0,base_syn):1}
   for part in parts:
    nd={}
    for (q0,s0),n0 in dp.items():
     for (q,s),n in part.items():
      if q0+q<=334:nd[q0+q,s0^s]=nd.get((q0+q,s0^s),0)+n0*n
    dp=nd
   feasible=sum(n for (q,s),n in dp.items() if q==334);compatible=dp.get((334,0),0)
   if feasible:records.append({'alt':alt,'feasible_z4':feasible,'compatible_z4':compatible});tf+=feasible;tc+=compatible
  records.sort(key=lambda x:(x['compatible_z4'],x['feasible_z4'],x['alt']))
  all_rows.append({'magnitude_type':row,'feasible_alt_tuples':len(records),'total_feasible_z4':tf,'total_compatible_z4':tc,'compatibility_fraction':tc/tf if tf else None,'min_survivor_alt_records':records[:16],'max_survivor_alt_records':records[-16:]})
  print(json.dumps({'event':'row_type','index':ri,'row':row,'alts':len(records),'feasible':tf,'compatible':tc,'elapsed_s':time.time()-st}),flush=True)
 out={'construction':'BS(84,83) batch GF(2) quartic-fibre counts','matrix_dimensions':[99,334],'coefficient_rank':rank,'dependencies':len(deps),'row_magnitude_types':TYPES,'signed_ordered_alt_tuples_considered':len(alts),'rows':all_rows,'elapsed_s':time.time()-st};raw=(json.dumps(out,indent=2)+'\n').encode();path=Path('agent_bsd_gf2_batch.json');path.write_bytes(raw);print(json.dumps({'event':'done','sha256':hashlib.sha256(raw).hexdigest(),'output':str(path),'elapsed_s':time.time()-st}),flush=True)
if __name__=='__main__':main()
