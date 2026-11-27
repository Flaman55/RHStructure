# Analysis of the original Lean proof

The structural analysis started on the original archive, before the compact rewriting existed:
leanprover-community/riemann-hypothesis at commit 6b1e1b8e9d683841024757f158fda63a32bbeae7
(Lean v4.33.1; 175,187 files, about 17.4 million lines).

1. `measure.py`: text-level counts (files, lines, declarations, tactics) -> `text_measurements.json`.
2. `DepGraph.lean`: declaration-level dependency walk from the five headline theorems of `Main`,
   run with the community cache in place (`lake env lean --run DepGraph.lean`) ->
   `depgraph_summary.txt` and `deps_edges.tsv` (not included: about 14 million edges).
3. `layers.py`: splits the reachable constants into the spine (reachable without expanding the
   literature-interface theorems) and the literature-only layer, and measures what each interface
   pulls outside the spine -> `layers_summary.json`, `interface_pull.tsv`.
