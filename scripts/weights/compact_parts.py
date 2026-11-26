"""Weigh the steps of grh-compact's spine (project constants only).

Usage: python3 -I compact_parts.py <constants.tsv> <deps_edges.tsv.gz> <out.json>
For each step: closure size, closure split by Lib/New, and constants that no other listed step
needs ("only"). Steps are disjoint roles from New/Main.lean's list of inputs.
"""
import csv, gzip, json, sys
from collections import defaultdict, deque
C, E, OUT = sys.argv[1:4]
mod = {}
with open(C, encoding="utf-8") as f:
    for r in csv.DictReader(f, delimiter="\t"): mod[r["constant"]] = r["module"]
adj = defaultdict(list)
with gzip.open(E, "rt", encoding="utf-8") as f:
    next(f)
    for line in f:
        a, _, b = line.rstrip("\n").partition("\t"); adj[a].append(b)
steps = {
 "S3a Theorem A short_forms": ["Data.short_forms"],
 "S3b Theorem B enough_forms": ["Data.enough_forms"],
 "S3c level pays excess heightPerRow_le": ["Data.heightPerRow_le"],
 "S3d fit twists (Selmer) exists_isFitFamily": ["exists_isFitFamily"],
 "S3e chain volume = lift volumes": ["Data.volume_iota_eq_prod_liftVolume"],
 "S3f one lift gains heightLe_liftVolume_ratio": ["Data.heightLe_liftVolume_ratio"],
 "S3g crude rows / one determinant": ["Data.crude_rows", "one_determinant"],
 "S3h product formula HeightLe.nonneg": ["HeightLe.nonneg"],
 "S2 remainder as prime sums": ["Data.remainder_eq", "Data.abs_mainHeight_add_remainder_le"],
 "S4 data exist at every x (scales)": ["exists_data"],
 "S5 window for second scale": ["IsPolar.exists_window_sub_mul_le", "isPolar_primeError"],
 "S6 Landau + quadratic twist": ["entireL_ne_zero_of_primeError_le", "exists_entireL_quadTwist_ne_zero"],
}
def bfs(roots):
    seen = set(r for r in roots if r in mod); q = deque(seen)
    while q:
        v = q.popleft()
        for w in adj.get(v, ()):
            if w not in seen and w in mod: seen.add(w); q.append(w)
    return seen
total = bfs(["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
             "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"])
sets = {k: bfs(v) for k, v in steps.items()}
res = {"reachable_project_constants": len(total),
       "reachable_New": sum(1 for c in total if mod[c].startswith("New")),
       "reachable_Lib": sum(1 for c in total if mod[c].startswith("Lib"))}
for k, s in sets.items():
    others = set().union(*(t for kk, t in sets.items() if kk != k))
    only = s - others
    res[k] = {"closure": len(s), "closure_New": sum(1 for c in s if mod[c].startswith("New")),
              "only": len(only), "only_New": sum(1 for c in only if mod[c].startswith("New")),
              "only_Lib": sum(1 for c in only if mod[c].startswith("Lib"))}
union = set().union(*sets.values())
res["not_in_any_step"] = len(total - union)
json.dump(res, open(OUT, "w"), indent=1)
for k, v in res.items(): print(k, v)
