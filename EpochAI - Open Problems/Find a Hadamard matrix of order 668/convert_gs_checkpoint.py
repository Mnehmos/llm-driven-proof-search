"""Convert this search lane's GS JSON into the public Hadamard_Proof format."""
import argparse,json
from pathlib import Path
def main():
    p=argparse.ArgumentParser();p.add_argument("input");p.add_argument("output");q=p.parse_args();src=json.loads(Path(q.input).read_text(encoding="utf8"));seq=src["sequences"]
    if len(seq)!=4 or any(len(a)!=167 for a in seq):raise ValueError("expected GS(167)")
    signature=[sum(a) for a in seq]
    if sum(x*x for x in signature)!=668:raise ValueError("row identity")
    out={"family":"goethals_seidel","order":668,"n":167,"signature":signature,"best_score":2*int(src.get("energy",0)),"best_state":seq}
    Path(q.output).write_text(json.dumps(out,indent=2)+"\n",encoding="utf8");print(json.dumps({"output":q.output,"signature":signature,"external_score":out["best_score"]}))
if __name__=="__main__":main()
