/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import ImportGraph.RequiredModules
import HepLean.Meta.Informal.Basic
/-!

## Basic Lean meta programming commands

-/

namespace HepLean
open Lean System Meta

/-!

## Imports

-/

/-- Gets all imports within HepLean. -/
def allImports : IO (Array Import) := do
  initSearchPath (← findSysroot)
  let mods : Name := `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let imports := hepLeanMod.imports.filter (fun c => c.module ≠ `Init)
  return imports

/-- Number of files within HepLean. -/
def noImports : IO Nat := do
  let imports ← allImports
  pure imports.size

/-- Gets all constants from an import. -/
def Imports.getConsts (imp : Import) : IO (Array ConstantInfo) := do
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  pure modData.constants

/-- Gets all user defined constants from an import. -/
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
  let x := x.filter (fun c => ¬ c.name.toString = "Informal.informalAssignment.quot")
  let x := x.filter (fun c => ¬ c.name.toString = "TensorTree.indexExpr.quot")
  let x := x.filter (fun c => ¬ c.name.toString = "TensorTree.tensorExpr.quot")
  pure x

/-- Lines from import. -/
def Imports.getLines (imp : Import) : IO (Array String) := do
  let filePath := (mkFilePath (imp.module.toString.split (· == '.'))).addExtension "lean"
  let lines ← IO.FS.lines filePath
  return lines

/-!

## Name

-/

/-- Turns a name into a Lean file. -/
def Name.toFile (c : Name) : MetaM String := do
  return s!"./{c.toString.replace "." "/" ++ ".lean"}"

/-- Turns a name, which represents a module, into a link to github. -/
def Name.toGitHubLink (c : Name) (l : Nat := 0) : MetaM String := do
  let headerLink := "https://github.com/HEPLean/HepLean/blob/master/"
  let filePart := (c.toString.replace "." "/") ++ ".lean"
  let linePart := "#L" ++ toString l
  return headerLink ++ filePart ++ linePart

/-- Given a name, returns the line number. -/
def Name.lineNumber (c : Name) : MetaM Nat := do
  match ← findDeclarationRanges? c with
  | some decl => pure decl.range.pos.line
  | none => panic! s!"{c} is a declaration without position"

/-- Given a name, returns the file name corresponding to that declaration. -/
def Name.fileName (c : Name) : MetaM Name := do
  let env ← getEnv
  let x := env.getModuleFor? c
  match x with
  | some c => pure c
  | none => panic! s!"{c} is a declaration without position"

/-- Returns the location of a name. -/
def Name.location (c : Name) : MetaM String := do
  let env ← getEnv
  let x := env.getModuleFor? c
  match x with
  | some decl => pure ((← Name.toFile decl) ++ ":" ++ toString (← Name.lineNumber c) ++ " "
    ++ c.toString)
  | none => panic! s!"{c} is a declaration without position"

/-- Determines if a name has a location. -/
def Name.hasPos (c : Name) : MetaM Bool := do
  match ← findDeclarationRanges? c with
  | some _ => pure true
  | none => pure false

/-- Determines if a name has a doc string. -/
def Name.hasDocString (c : Name) : MetaM Bool := do
  let env ← getEnv
  let doc ← Lean.findDocString? env c
  match doc with
  | some _ => pure true
  | none => pure false

/-- Given a name, returns the source code defining that name. -/
def Name.getDeclString (name : Name) : MetaM String := do
  let env ← getEnv
  let decl ← findDeclarationRanges? name
  match decl with
  | some decl =>
    let startLine := decl.range.pos
    let endLine := decl.range.endPos
    let fileName? := env.getModuleFor? name
    match fileName? with
    | some fileName =>
      let fileContent ← IO.FS.readFile { toString := (← Name.toFile fileName)}
      let fileMap := fileContent.toFileMap
      let startPos := fileMap.ofPosition startLine
      let endPos := fileMap.ofPosition endLine
      let text := fileMap.source.extract startPos endPos
      pure text
    | none =>
        pure ""
  | none => pure ""

/-- Number of definitions. -/
def noDefs : MetaM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  let x := x.flatten
  let x := x.filter (fun c => c.isDef)
  let x ← x.filterM (fun c => (Name.hasPos c.name))
  pure x.toList.length

/-- Number of definitions. -/
def noLemmas : MetaM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  let x := x.flatten
  let x := x.filter (fun c => ¬ c.isDef)
  let x ← x.filterM (fun c => (Name.hasPos c.name))
  pure x.toList.length

/-- Number of definitions without a doc-string. -/
def noDefsNoDocString : MetaM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  let x := x.flatten
  let x := x.filter (fun c => c.isDef)
  let x ← x.filterM (fun c => (Name.hasPos c.name))
  let x ← x.filterM (fun c => do
    return Bool.not (← (Name.hasDocString c.name)))
  pure x.toList.length

/-- Number of definitions without a doc-string. -/
def noLemmasNoDocString : MetaM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  let x := x.flatten
  let x := x.filter (fun c => ¬ c.isDef)
  let x ← x.filterM (fun c => (Name.hasPos c.name))
  let x ← x.filterM (fun c => do
    return Bool.not (← (Name.hasDocString c.name)))
  pure x.toList.length

/-- The number of lines in HepLean. -/
def noLines : IO Nat := do
  let imports ← HepLean.allImports
  let x ← imports.mapM HepLean.Imports.getLines
  let x := x.flatten
  pure x.toList.length

/-- The number of TODO items. -/
def noTODOs : IO Nat := do
  let imports ← HepLean.allImports
  let x ← imports.mapM HepLean.Imports.getLines
  let x := x.flatten
  let x := x.filter fun l => l.startsWith "/-! TODO:"
  pure x.size

/-- The number of files with a TODO item. -/
def noFilesWithTODOs : IO Nat := do
  let imports ← HepLean.allImports
  let x ← imports.mapM HepLean.Imports.getLines
  let x := x.filter (fun M => M.any fun l => l.startsWith "/-! TODO:")
  pure x.size

end HepLean
