/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import HepLean.Meta.Informal
import ImportGraph.RequiredModules
/-!

# Extracting commands with no doc strings.

-/

open Lean System Meta

def Imports.getConsts (imp : Import) : IO (Array ConstantInfo) := do
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  pure modData.constants

def Imports.getUserConsts (imp : Import) : MetaM (Array ConstantInfo) := do
  let env ← getEnv
  let x := (← Imports.getConsts imp).filter (fun c => ¬ c.name.isInternal)
  let x := x.filter (fun c => ¬ Lean.isCasesOnRecursor env c.name)
  let x := x.filter (fun c => ¬ Lean.isRecOnRecursor env c.name)
  let x := x.filter (fun c => ¬ Lean.isNoConfusion env c.name)
  let x := x.filter (fun c => ¬ Lean.isBRecOnRecursor env c.name)
  let x := x.filter (fun c => ¬ Lean.isAuxRecursorWithSuffix env c.name Lean.binductionOnSuffix)
  let x := x.filter (fun c => ¬ Lean.isAuxRecursorWithSuffix env c.name Lean.belowSuffix)
  let x := x.filter (fun c => ¬ Lean.isAuxRecursorWithSuffix env c.name Lean.ibelowSuffix)
  /- Removing syntax category declarations. -/
  let x := x.filter (fun c => ¬ c.name.toString = "Informal.informalAssignment.quot" )
  let x := x.filter (fun c => ¬ c.name.toString = "TensorTree.indexExpr.quot" )
  let x := x.filter (fun c => ¬ c.name.toString = "TensorTree.tensorExpr.quot" )
  pure x

def Name.lineNumber (c : Name) : MetaM Nat := do
  match ← findDeclarationRanges? c  with
  | some decl => pure decl.range.pos.line
  | none => panic! s!"{c} is a declaration without position"

def Name.toFile (c : Name) : MetaM String := do
  return s!"./{c.toString.replace "." "/" ++ ".lean"}"

def Name.location (c : Name) : MetaM String := do
  let env ← getEnv
  let x := env.getModuleFor?  c
  match x with
  | some decl => pure ((← Name.toFile decl) ++ ":" ++ toString (← Name.lineNumber c) ++ " "
    ++ c.toString)
  | none => panic! s!"{c} is a declaration without position"

def Name.hasPos (c : Name) : MetaM Bool := do
  match ← findDeclarationRanges? c  with
  | some _ => pure true
  | none => pure false

def Name.hasDocString (c : Name) : MetaM Bool := do
  let env ← getEnv
  let doc ← Lean.findDocString? env c
  match doc with
  | some _ => pure true
  | none => pure false

def Imports.NoDocStringDef (imp : Import) : MetaM UInt32 := do
  let x := (← Imports.getUserConsts imp).filter (fun c => c.isDef)
  let x ← x.filterM (fun c => do
    return Bool.not (← (Name.hasDocString c.name)))
  let y ← x.filterM (fun c => Name.hasPos c.name)
  let loc ← y.mapM (fun c => (Name.location c.name))
  if loc.toList.length > 0 then
    IO.println "\n"
    IO.println s!"Module {imp.module} has the following definitions without doc strings:"
    IO.println (String.intercalate "\n" loc.toList)
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
    IO.println (String.intercalate "\n" loc.toList)
  pure 0

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name := `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let imports := hepLeanMod.imports.filter (fun c => c.module ≠ `Init)
  let _ ← CoreM.withImportModules #[`HepLean] (imports.mapM Imports.NoDocStringDef).run'
  if "--lemmas" ∈ args then
    let _ ← CoreM.withImportModules #[`HepLean] (imports.mapM Imports.NoDocStringLemma).run'
  pure 0
