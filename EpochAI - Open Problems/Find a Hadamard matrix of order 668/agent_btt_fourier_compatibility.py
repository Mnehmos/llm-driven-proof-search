"""Enumerate TT(56) z=i norm-334 fibres and exact residual-mod-4 compatibility.

The fixed z=1 and z=-1 margins determine the even/odd residue sums.  We
enumerate feasible z=i real/imaginary components, retain weighted norm 334,
and test the GF(2) autocorrelation-parity system.  Modulo four only the two
weight-one sequences are variable; the weight-two sequences contribute a
fixed constant at every lag.
"""
from __future__ import annotations
import argparse, hashlib, heapq, json
from collections import defaultdict
from pathlib import Path

L=(56,56,56,55); W=(1,1,2,2)

def read_seed(path:Path):
    q=json.loads(path.read_text())['sequences']
    return [list(map(int,q[k][:L[k]])) for k in range(4)]

def rows_alts(a):
    return [sum(x) for x in a],[sum(v if i%2==0 else -v for i,v in enumerate(x)) for x in a]

def current_z4(a):
    return [v for x in a for v in (sum(x[0::4])-sum(x[2::4]),sum(x[1::4])-sum(x[3::4]))]

def options(k,row,alt):
    n=L[k]; lens=[len(range(c,n,4)) for c in range(4)]; even=(row+alt)//2; odd=(row-alt)//2; out=[]
    for s0 in range(-lens[0],lens[0]+1,2):
      s2=even-s0
      if not (-lens[2]<=s2<=lens[2] and (s2-lens[2])%2==0):continue
      for s1 in range(-lens[1],lens[1]+1,2):
        s3=odd-s1
        if not (-lens[3]<=s3<=lens[3] and (s3-lens[3])%2==0):continue
        u,v=s0-s2,s1-s3; neg=tuple((lens[c]-s)//2 for c,s in enumerate((s0,s1,s2,s3)))
        out.append({'u':u,'v':v,'norm':W[k]*(u*u+v*v),'neg':neg})
    return out

def gf2_template():
    rows=[]; rhs=[]
    # Residual/2 mod 2 equations.  Only A and B supply variable coefficients.
    for d in range(1,56):
      mask=0
      for k in range(2):
        for p in range(L[k]):
          if (p<d) ^ (p>=L[k]-d):mask ^= 1<<(k*56+p)
      constant=2*(56-d)+2*((56-d)+max(0,55-d))
      assert constant%2==0
      rows.append(mask);rhs.append((constant//2)&1)
    # Eight residue-count parity equations for A and B; RHS is target-specific.
    for k in range(2):
      for c in range(4):
        rows.append(sum(1<<(k*56+p) for p in range(c,56,4)));rhs.append(0)
    # RREF with row-operation masks, allowing very cheap target-RHS checks.
    aug=[rows[i] | (1<<(112+i)) for i in range(len(rows))]
    rr=0
    for col in range(112):
      hit=next((j for j in range(rr,len(aug)) if aug[j]>>col&1),None)
      if hit is None:continue
      aug[rr],aug[hit]=aug[hit],aug[rr]
      for j in range(len(aug)):
        if j!=rr and aug[j]>>col&1:aug[j]^=aug[rr]
      rr+=1
    dependencies=[row>>112 for row in aug if row&((1<<112)-1)==0]
    return rhs,rr,dependencies

def compatible(oa,ob,base_rhs,deps):
    rhs=base_rhs[:55]+[x&1 for x in oa['neg']+ob['neg']]
    packed=sum(v<<i for i,v in enumerate(rhs))
    return all((packed&dep).bit_count()%2==0 for dep in deps)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('seed',type=Path);ap.add_argument('--limit',type=int,default=5000);ap.add_argument('--output',type=Path,default=Path('agent_btt_fourier_compatibility.json'));g=ap.parse_args()
    a=read_seed(g.seed);rows,alts=rows_alts(a);cur=current_z4(a)
    assert sum(W[k]*rows[k]*rows[k] for k in range(4))==334
    assert sum(W[k]*alts[k]*alts[k] for k in range(4))==334
    opts=[options(k,rows[k],alts[k]) for k in range(4)]
    base_rhs,rank,deps=gf2_template()
    ab=defaultdict(list);ab_total=ab_ok=0
    for x in opts[0]:
      for y in opts[1]:
        ab_total+=1
        if compatible(x,y,base_rhs,deps):ab_ok+=1;ab[x['norm']+y['norm']].append((x,y))
    cd=defaultdict(list)
    for x in opts[2]:
      for y in opts[3]:cd[x['norm']+y['norm']].append((x,y))
    heap=[];serial=0;total=0
    for n,left in ab.items():
      right=cd.get(334-n,())
      total+=len(left)*len(right)
      for x,y in left:
        for u,v in right:
          flat=[x['u'],x['v'],y['u'],y['v'],u['u'],u['v'],v['u'],v['v']]
          dist=sum(abs(flat[i]-cur[i])//4 for i in range(8))
          rec={'distance_swaps':dist,'z4':flat,'negative_counts':[list(x['neg']),list(y['neg']),list(u['neg']),list(v['neg'])]};inv=(-dist,tuple(-z for z in flat));serial+=1
          if len(heap)<g.limit:heapq.heappush(heap,(inv,serial,rec))
          else:
            worst=(-heap[0][0][0],[-z for z in heap[0][0][1]])
            if (dist,flat)<worst:heapq.heapreplace(heap,(inv,serial,rec))
    top=sorted((q[2] for q in heap),key=lambda q:(q['distance_swaps'],q['z4']))
    out={'construction':'TT(56)','weights':W,'lengths':L,'seed':str(g.seed),'rows':rows,'alternating_rows':alts,'current_z4':cur,'current_z4_norm':sum(W[k]*(cur[2*k]**2+cur[2*k+1]**2) for k in range(4)),'coefficient_rows':63,'coefficient_rank':rank,'dependency_count':len(deps),'options_per_sequence':list(map(len,opts)),'ab_pairs':ab_total,'compatible_ab_pairs':ab_ok,'compatible_norm334_fibres':total,'top_targets':top}
    raw=(json.dumps(out,indent=2)+'\n').encode();g.output.write_bytes(raw);print(json.dumps({'rows':rows,'alts':alts,'current_z4':cur,'rank':rank,'dependencies':len(deps),'ab_pairs':ab_total,'compatible_ab':ab_ok,'fibres':total,'best':top[:5],'sha256':hashlib.sha256(raw).hexdigest(),'output':str(g.output)}))
if __name__=='__main__':main()
