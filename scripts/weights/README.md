# Weights of the steps (Section "Weights of the steps" of the paper)

1. In a built checkout of grh-compact (commit 72fead1), copy `DepGraphCompact.lean` to the project
   root and run `lake env lean --run DepGraphCompact.lean`. It writes `constants.tsv` and
   `deps_edges.tsv` (gzip the latter to `deps_edges.tsv.gz`).
2. `python3 -I compact_parts.py constants.tsv deps_edges.tsv.gz parts.json` prints, for each step
   of the spine, the size of its closure and the constants that no other listed step needs.
