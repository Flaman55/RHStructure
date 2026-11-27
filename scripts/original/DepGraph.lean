/-
DepGraph.lean — declaration-level dependency walk for the RH Lean archive.

Roots: every constant declared in module `Main` (the headline theorems).
Walks all constants used in types and values, then writes:
  * depgraph_summary.txt   : counts (project vs external, reachable vs total)
  * deps_by_module.tsv     : per project module, reachable / total constants
  * deps_edges.tsv         : project-internal edges among reachable constants
  * unreachable.tsv        : project constants not reachable from Main (dead-code candidates)

Run inside the project (WSL):  lake env lean --run DepGraph.lean
-/
import Lean
import Std.Data.HashMap
open Lean

def externalRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets,
   `Plausible, `ImportGraph, `LeanSearchClient, `Cli]

def isProjectModule (m : Name) : Bool :=
  !(externalRoots.any fun r => r.isPrefixOf m)

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  initSearchPath (← findSysroot)
  IO.println "Importing Main (loads all oleans)..."
  let env ← importModules #[{ module := `Main }] {} (trustLevel := 1024)
  let t1 ← IO.monoMsNow
  IO.println s!"Environment loaded in {(t1 - t0) / 1000} s"
  let names := env.header.moduleNames
  let modOf (c : Name) : Name :=
    match env.getModuleIdxFor? c with
    | some idx => names[idx.toNat]!
    | none => `Main
  -- Roots: constants declared in module Main
  let mut roots : Array Name := #[]
  let mut totalPerMod : Std.HashMap Name Nat := {}
  let mut allProject : Array Name := #[]
  for (c, _) in env.constants.toList do
    let m := modOf c
    if m == `Main then roots := roots.push c
    if isProjectModule m then
      totalPerMod := totalPerMod.insert m (totalPerMod.getD m 0 + 1)
      allProject := allProject.push c
  IO.println s!"Roots in Main: {roots.size}"
  -- BFS
  let edgeH ← IO.FS.Handle.mk "deps_edges.tsv" IO.FS.Mode.write
  edgeH.putStrLn "from\tto"
  let mut seen : NameSet := {}
  let mut stack : Array Name := roots
  let mut nEdges := 0
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let cProj := isProjectModule (modOf c)
    for d in ci.getUsedConstantsAsSet.toList do
      if cProj && isProjectModule (modOf d) then
        edgeH.putStrLn s!"{c}\t{d}"
        nEdges := nEdges + 1
      unless seen.contains d do
        stack := stack.push d
  edgeH.flush
  -- Statistics
  let mut reachPerMod : Std.HashMap Name Nat := {}
  let mut nProj := 0
  let mut nExt := 0
  for c in seen.toList do
    let m := modOf c
    if isProjectModule m then
      nProj := nProj + 1
      reachPerMod := reachPerMod.insert m (reachPerMod.getD m 0 + 1)
    else
      nExt := nExt + 1
  let modH ← IO.FS.Handle.mk "deps_by_module.tsv" IO.FS.Mode.write
  modH.putStrLn "module\treachable\ttotal"
  for (m, tot) in totalPerMod.toList do
    modH.putStrLn s!"{m}\t{reachPerMod.getD m 0}\t{tot}"
  modH.flush
  let deadH ← IO.FS.Handle.mk "unreachable.tsv" IO.FS.Mode.write
  deadH.putStrLn "constant\tmodule"
  let mut nDead := 0
  for c in allProject do
    unless seen.contains c do
      deadH.putStrLn s!"{c}\t{modOf c}"
      nDead := nDead + 1
  deadH.flush
  let t2 ← IO.monoMsNow
  let summary := String.intercalate "\n" [
    s!"roots_in_Main\t{roots.size}",
    s!"reachable_constants\t{seen.size}",
    s!"reachable_project\t{nProj}",
    s!"reachable_external\t{nExt}",
    s!"project_constants_total\t{allProject.size}",
    s!"project_unreachable\t{nDead}",
    s!"project_modules_total\t{totalPerMod.size}",
    s!"project_modules_with_reachable\t{reachPerMod.size}",
    s!"project_internal_edges\t{nEdges}",
    s!"seconds_load\t{(t1 - t0) / 1000}",
    s!"seconds_walk\t{(t2 - t1) / 1000}"]
  IO.FS.writeFile "depgraph_summary.txt" (summary ++ "\n")
  IO.println summary
