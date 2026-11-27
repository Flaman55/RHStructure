"""Exact layer split of the reachable RH proof from DepGraph edges.

Usage: python3 -I layers.py <deps_edges.tsv.gz> <deps_by_module-free: src_dir> <out_dir>

Layers (project constants only, edges are project-internal):
  reach    : reachable from the Main roots
  spine    : reachable from the roots without expanding the literature-interface
             theorems (UpperTheory.LiteratureTheorems.*)
  literature-only : reach minus spine (used only through the interfaces)
Also reports, per interface, the size of what it alone pulls in.
"""
import array
import gzip
import json
import os
import sys
from collections import Counter, deque

edges_path, src, out = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)

ids = {}
names = []
def nid(s):
    i = ids.get(s)
    if i is None:
        i = len(names)
        ids[s] = i
        names.append(s)
    return i

es = array.array("i")
ed = array.array("i")
with gzip.open(edges_path, "rt", encoding="utf-8") as f:
    next(f)
    for line in f:
        a, _, b = line.rstrip("\n").partition("\t")
        es.append(nid(a))
        ed.append(nid(b))
n = len(names)
print("nodes", n, "edges", len(es), flush=True)

deg = array.array("i", [0]) * (n + 1)
for s in es:
    deg[s + 1] += 1
for i in range(n):
    deg[i + 1] += deg[i]
adj = array.array("i", [0]) * len(es)
fill = array.array("i", deg[:n])
for s, d in zip(es, ed):
    adj[fill[s]] = d
    fill[s] += 1
del es, ed, fill

indeg = array.array("i", [0]) * n
for d in adj:
    indeg[d] += 1

def bfs(roots, stop=frozenset()):
    seen = bytearray(n)
    q = deque()
    for r in roots:
        if not seen[r]:
            seen[r] = 1
            q.append(r)
    while q:
        v = q.popleft()
        if v in stop:
            continue
        for e in range(deg[v], deg[v + 1]):
            w = adj[e]
            if not seen[w]:
                seen[w] = 1
                q.append(w)
    return seen

# roots: project constants with no incoming edge that sit in Main
roots = [ids[x] for x in ("riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
                          "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive") if x in ids]
if not roots:
    roots = [i for i in range(n) if indeg[i] == 0 and "." not in names[i]]
print("roots", [names[r] for r in roots], flush=True)

iface = [i for i, s in enumerate(names) if s.startswith("UpperTheory.LiteratureTheorems.")]
iface_set = frozenset(iface)
print("interface theorems in graph", len(iface), flush=True)

reach = bfs(roots)
spine = bfs(roots, stop=iface_set)
lit = bfs(iface)
count = lambda m: sum(1 for i in range(n) if m(i))
summary = {
    "nodes_in_edge_graph": n,
    "roots": [names[r] for r in roots],
    "interfaces": len(iface),
    "reach": count(lambda i: reach[i]),
    "spine": count(lambda i: spine[i]),
    "literature_only": count(lambda i: reach[i] and not spine[i]),
    "spine_shared_with_literature": count(lambda i: spine[i] and lit[i]),
}

# module of a constant: longest module prefix that exists as a file under src
mod_cache = {}
def module_of(name):
    parts = name.split(".")
    for k in range(len(parts), 0, -1):
        key = ".".join(parts[:k])
        if key in mod_cache:
            if mod_cache[key]:
                return key
            continue
        exists = os.path.exists(os.path.join(src, *parts[:k]) + ".lean")
        mod_cache[key] = exists
        if exists:
            return key
    return "?"

# per-interface exclusive pull: what each interface reaches that the spine does not
rows = []
for i in iface:
    # walk only through constants outside the spine
    seen = set()
    q = deque()
    for e in range(deg[i], deg[i + 1]):
        w = adj[e]
        if not spine[w] and w not in seen:
            seen.add(w)
            q.append(w)
    while q:
        v = q.popleft()
        for e in range(deg[v], deg[v + 1]):
            w = adj[e]
            if not spine[w] and w not in seen:
                seen.add(w)
                q.append(w)
    rows.append((names[i], len(seen)))
rows.sort(key=lambda r: -r[1])
with open(os.path.join(out, "interface_pull.tsv"), "w") as f:
    f.write("interface\tconstants_outside_spine\n")
    for a, b in rows:
        f.write(f"{a}\t{b}\n")

with open(os.path.join(out, "spine_constants.txt"), "w") as f:
    for i in range(n):
        if spine[i]:
            f.write(names[i] + "\n")
with open(os.path.join(out, "layers_summary.json"), "w") as f:
    json.dump(summary, f, indent=1)
print(json.dumps(summary, indent=1))
