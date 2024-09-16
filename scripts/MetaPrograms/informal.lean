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

# Extracting information about informal definitions and lemmas

-/

open Lean System Meta

def getConst (imp : Import) : IO (Array (Import × ConstantInfo)) := do
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  pure (modData.constants.map (fun c => (imp, c)))

def getLineNumber (c : Name) : MetaM Nat := do
  match ← findDeclarationRanges? c  with
  | some decl => pure decl.range.pos.line
  | none => panic! s!"{c} is a declaration without position"

def getModule (c : Name) : MetaM Name := do
  match Lean.Environment.getModuleFor? (← getEnv) c with
  | some mod => pure mod
  | none => panic! s!"{c} is a declaration without position"

def depToString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  pure s!"    * {d}: ./{mod.toString.replace "." "/" ++ ".lean"}:{lineNo}"

unsafe def informalLemmaToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ←
    match c.2 with
    | ConstantInfo.defnInfo c =>
        Lean.Meta.evalExpr' InformalLemma ``InformalLemma c.value
    | _ => panic! "This should not happen"
  let dep ← informalLemma.dependencies.mapM fun d => depToString d
  pure s!"
Informal lemma: {informalLemma.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalLemma.math}
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ←
    match c.2 with
    | ConstantInfo.defnInfo c =>
        Lean.Meta.evalExpr' InformalDefinition ``InformalDefinition c.value
    | _ => panic! "This should not happen"
  let dep ← informalDef.dependencies.mapM fun d => depToString d
  pure s!"
Informal lemma: {informalDef.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalDef.math}
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mods : Name := `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let imports := hepLeanMod.imports.filter (fun c => c.module ≠ `Init)
  let constants ← imports.mapM getConst
  let constants := constants.flatten
  let constants := constants.filter (fun c => ¬ Lean.Name.isInternalDetail c.2.name)
  /- Informal lemmas. -/
  let informalLemma := constants.filter fun c => Informal.isInformalLemma c.2
  let informalLemmaPrint ← CoreM.withImportModules #[`HepLean] (informalLemma.mapM informalLemmaToString).run'
  IO.println (String.intercalate "\n" informalLemmaPrint.toList)
  /- Informal definitions-/
  let informalDef := constants.filter fun c => Informal.isInformalDef c.2
  let informalDefPrint ← CoreM.withImportModules #[`HepLean] (informalDef.mapM informalDefToString).run'
  IO.println (String.intercalate "\n" informalDefPrint.toList)
