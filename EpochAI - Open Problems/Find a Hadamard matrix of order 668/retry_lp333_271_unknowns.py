"""Escalate the UNKNOWN sub-fibers of the <271> split with a longer budget."""
import importlib.util, json, sys
from pathlib import Path

spec = importlib.util.spec_from_file_location("sp", "search_lp333_271_split.py")
sp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sp)

seconds = float(sys.argv[1]) if len(sys.argv) > 1 else 600
workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
src = Path("lp333_271_split.jsonl")
out = Path("lp333_271_split_retry.jsonl")
done = set()
if out.exists():
    for line in out.read_text().splitlines():
        try:
            r = json.loads(line)
            if r["status"] != "UNKNOWN":
                done.add((tuple(r["pa"]), tuple(r["pb"])))
        except Exception:
            pass
todo = []
for line in src.read_text().splitlines():
    try:
        r = json.loads(line)
    except Exception:
        continue
    if r.get("status") == "UNKNOWN" and (tuple(r["pa"]), tuple(r["pb"])) not in done:
        todo.append((r["i"], r["pa"], r["pb"]))
print(json.dumps({"event": "retry", "count": len(todo), "seconds": seconds}), flush=True)
unk = 0
for i, pa, pb in todo:
    r = sp.solve_sub(pa, pb, seconds, workers)
    rec = {"i": i, "pa": pa, "pb": pb, **{k: v for k, v in r.items() if k != "sequences"}}
    if "sequences" in r:
        rec["sequences"] = r["sequences"]
    print(json.dumps({k: v for k, v in rec.items() if k != "sequences"}), flush=True)
    with out.open("a") as f:
        f.write(json.dumps(rec) + "\n")
    if r["status"] == "UNKNOWN":
        unk += 1
    if r.get("verified_paf"):
        Path("lp333_271_WITNESS.json").write_text(json.dumps(rec))
        print("WITNESS FOUND", flush=True)
        sys.exit(0)
print(json.dumps({"event": "done", "still_unknown": unk}), flush=True)
