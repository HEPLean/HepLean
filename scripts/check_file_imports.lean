/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
/-!

# Check file imports

This file checks that the imports in `HepLean.lean` are sorted and complete.

It can be run from the terminal using
`lake exe check_file_imports`.

## Note on adaptation

The functions

`addModulesIn`, `expectedHepLeanImports`, and `checkMissingImports`

are adapted from `batteries.scripts.check_imports.lean` authored by Joe Hendrix.

-/
open Lean System Meta

/--  Recursively finds files in directory. -/
partial def addModulesIn (recurse : Bool) (prev : Array Name) (root : Name := .anonymous)
    (path : FilePath) : IO (Array Name) := do
  let mut r := prev
  for entry in ← path.readDir do
    if ← entry.path.isDir then
      if recurse then
        r ← addModulesIn recurse r (root.mkStr entry.fileName) entry.path
    else
      let .some mod := FilePath.fileStem entry.fileName
        | continue
      r := r.push (root.mkStr mod)
  pure r

/-- Compute imports expected by `HepLean.lean` by looking at file structure. -/
def expectedHepLeanImports : IO (Array Name) := do
  let mut needed := #[]
  for top in ← FilePath.readDir "HepLean" do
      let nm := `HepLean
      let rootname := FilePath.withExtension top.fileName ""
      let root :=  nm.mkStr rootname.toString
      if ← top.path.isDir then
        needed ← addModulesIn (recurse := true) needed (root := root) top.path
      else
        needed :=
        needed.push root
  pure needed

/-- Checks whether an array `imports` is sorted after `Init` is removed.  -/
def arrayImportSorted (imports : Array Import) : IO Bool :=  do
  let X := (imports.map (fun x => x.module.toString)).filter (fun x => x != "Init")
  let mut warned := false
  if ! X = X.qsort (· < ·) then
    IO.print s!"Import file is not sorted. \n"
    warned := true
  pure warned

/-- Checks every file in `reqImports` is imported into `modData`
  return true if this is NOT the case. -/
def checkMissingImports (modData : ModuleData) (reqImports : Array Name) :
    IO Bool := do
  let names : HashSet Name := HashSet.ofArray (modData.imports.map (·.module))
  let mut warned := false
  for req in reqImports do
    if !names.contains req then
      IO.print s!"File {req} is not imported. \n"
      warned := true
  pure warned

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let eHepLeanImports ← expectedHepLeanImports
  let sortedWarned ← arrayImportSorted hepLeanMod.imports
  let warned ← checkMissingImports hepLeanMod eHepLeanImports
  if (warned ∨ sortedWarned) then
    throw <| IO.userError s!"The HepLean module is not sorted, or has missing imports."
  IO.println s!"Import check complete."
  pure 0
