"""Generate and exactly verify the quadratic-character 37-compression."""
import json
from pathlib import Path

P=37
def chi(x):
    x%=P
    if x==0:return 0
    return 1 if pow(x,(P-1)//2,P)==1 else -1

A=[1]+[3*chi(i) for i in range(1,P)]
B=[1]+[-3*chi(i) for i in range(1,P)]
R=[18+sum(A[i]*A[(i+h)%P]+B[i]*B[(i+h)%P] for i in range(P)) for h in range(1,19)]
assert sum(A)==sum(B)==1
assert sum(x*x for x in A+B)==650
assert R==[0]*18
out={"construction":"Legendre pair length 333, quadratic-character 37-compression",
     "solved_compression":True,"energy":0,"sums":[1,1],"square_norm":650,
     "residual_paf_plus_18":R,"compressed_sequences":[A,B]}
Path("legendre37_character_candidate.json").write_text(json.dumps(out,separators=(",",":"))+"\n")
print("verified exact 37-compression -> legendre37_character_candidate.json")
