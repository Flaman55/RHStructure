"""Structural and redundancy measurements of the RH Lean archive.

Usage: python3 -I measure.py <src_dir> <out_dir>
Writes JSON/TSV summaries into out_dir.
"""
import hashlib
import json
import os
import re
import sys
from collections import Counter, defaultdict

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)

decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                     r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:({\[]+)",
                     re.M)
tactics = ["decide", "native_decide", "interval_cases", "fin_cases", "norm_num", "simp",
           "omega", "linarith", "nlinarith", "positivity", "polyrith", "ring", "aesop", "grind"]
tac_re = {t: re.compile(r"\b" + t + r"\b") for t in tactics}

files = []
for root, _, fs in os.walk(src):
    for f in fs:
        if f.endswith(".lean"):
            files.append(os.path.join(root, f))

lines_hist = Counter()
by_dir2 = defaultdict(lambda: [0, 0, 0])  # files, lines, decls
hashes = defaultdict(list)
norm_hashes = defaultdict(list)
decl_kinds = Counter()
decl_last = defaultdict(list)  # last name component -> files
tac_counts = Counter()
name_pat = Counter()
import_only = 0
tot_lines = 0
pat_list = ["Statement", "OfHyp", "OfPublished", "OfLiterature", "Imports", "Copy", "Bis", "Alt",
            "Ter", "2", "Proof", "Inputs"]

for p in files:
    rel = os.path.relpath(p, src)
    parts = rel.split(os.sep)
    key = "/".join(parts[:2]) if len(parts) > 2 else parts[0]
    with open(p, "rb") as fh:
        raw = fh.read()
    text = raw.decode("utf-8", "replace")
    nl = text.count("\n") + (0 if text.endswith("\n") else 1)
    tot_lines += nl
    b = 0
    while (1 << b) < nl:
        b += 1
    lines_hist[1 << b] += 1
    hashes[hashlib.sha1(raw).hexdigest()].append(rel)
    body = "\n".join(l for l in text.splitlines()
                     if l.strip() and not l.lstrip().startswith(("import", "--", "open", "namespace", "end", "section", "noncomputable section")))
    body_n = re.sub(r"\s+", " ", body)
    if not body_n.strip():
        import_only += 1
    else:
        norm_hashes[hashlib.sha1(body_n.encode()).hexdigest()].append(rel)
    ds = decl_re.findall(text)
    by_dir2[key][0] += 1
    by_dir2[key][1] += nl
    by_dir2[key][2] += len(ds)
    for kind, name in ds:
        decl_kinds[kind] += 1
        decl_last[name.split(".")[-1]].append(rel)
    for t, r in tac_re.items():
        tac_counts[t] += len(r.findall(text))
    stem = os.path.splitext(parts[-1])[0]
    for pat in pat_list:
        if pat in stem:
            name_pat[pat] += 1

exact_dup_groups = [v for v in hashes.values() if len(v) > 1]
norm_dup_groups = [v for v in norm_hashes.values() if len(v) > 1]
dup_names = {k: v for k, v in decl_last.items() if len(v) > 1}

summary = {
    "files": len(files),
    "lines": tot_lines,
    "import_only_files": import_only,
    "decls": dict(decl_kinds),
    "decls_total": sum(decl_kinds.values()),
    "exact_dup_groups": len(exact_dup_groups),
    "exact_dup_extra_files": sum(len(v) - 1 for v in exact_dup_groups),
    "norm_dup_groups": len(norm_dup_groups),
    "norm_dup_extra_files": sum(len(v) - 1 for v in norm_dup_groups),
    "decl_names_repeated": len(dup_names),
    "decl_instances_in_repeated_names": sum(len(v) for v in dup_names.values()),
    "tactics": dict(tac_counts),
    "file_name_patterns": dict(name_pat),
    "lines_per_file_hist": {str(k): v for k, v in sorted(lines_hist.items())},
}
with open(os.path.join(out, "summary.json"), "w") as f:
    json.dump(summary, f, indent=1)
with open(os.path.join(out, "by_dir2.tsv"), "w") as f:
    f.write("dir\tfiles\tlines\tdecls\n")
    for k, (a, b2, c) in sorted(by_dir2.items(), key=lambda x: -x[1][1]):
        f.write(f"{k}\t{a}\t{b2}\t{c}\n")
with open(os.path.join(out, "norm_dup_groups_top.txt"), "w") as f:
    for g in sorted(norm_dup_groups, key=len, reverse=True)[:200]:
        f.write(f"{len(g)}\t" + " | ".join(g[:6]) + "\n")
with open(os.path.join(out, "dup_names_top.txt"), "w") as f:
    for k, v in sorted(dup_names.items(), key=lambda x: -len(x[1]))[:300]:
        f.write(f"{len(v)}\t{k}\t" + " | ".join(v[:4]) + "\n")
print(json.dumps(summary, indent=1))
