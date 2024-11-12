/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Basic
/-!

# Extracting commands with no doc strings.

-/

open Lean System Meta HepLean

def Imports.NoDocStringDef (imp : Import) : MetaM UInt32 := do
  let x := (← Imports.getUserConsts imp).filter (fun c => c.isDef)
  let x ← x.filterM (fun c => do
    return Bool.not (← (Name.hasDocString c.name)))
  let y ← x.filterM (fun c => Name.hasPos c.name)
  let loc ← y.mapM (fun c => (Name.location c.name))
  if loc.toList.length > 0 then
    IO.println "\n"
    IO.println s!"Module {imp.module} has the following definitions without doc strings:"
    IO.println (String.intercalate "\n" loc.toList.mergeSort)
  pure 0

def Imports.NoDocStringLemma (imp : Import) : MetaM UInt32 := do
  let x := (← Imports.getUserConsts imp).filter (fun c => ¬ c.isDef)
  let x ← x.filterM (fun c => do
    return Bool.not (← (Name.hasDocString c.name)))
  let y ← x.filterM (fun c => Name.hasPos c.name)
  let loc ← y.mapM (fun c => (Name.location c.name))
  if loc.toList.length > 0 then
    IO.println "\n"
    IO.println s!"Module {imp.module} has the following lemmas without doc strings:"
    IO.println (String.intercalate "\n" loc.toList.mergeSort)
  pure 0

unsafe def main (args : List String) : IO UInt32 := do
  let imports ← allImports
  let _ ← CoreM.withImportModules #[`HepLean] (imports.mapM Imports.NoDocStringDef).run'
  if "--lemmas" ∈ args then
    let _ ← CoreM.withImportModules #[`HepLean] (imports.mapM Imports.NoDocStringLemma).run'
  pure 0
