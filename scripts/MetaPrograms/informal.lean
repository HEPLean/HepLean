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

def getConstInfo (n : Name) : MetaM ConstantInfo := do
  match (← getEnv).find? n  with
  | some c => pure c
  | none => panic! s!"{n} is not a constant"

/-- Gets the docstring from a name, if it exists, otherwise the string "No docstring."-/
def getDocString (n : Name) : MetaM String := do
  match ← Lean.findDocString? (← getEnv) n with
  | some doc => pure doc
  | none => pure "No docstring."

def depToString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  pure s!"    * {d}: ./{mod.toString.replace "." "/" ++ ".lean"}:{lineNo}"

def depToWebString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (mod.toString.replace "." "/") ++ ".lean"
  pure s!"    * [{d}]({webPath}#L{lineNo})"

/-- Takes a `ConstantInfo` corresponding to a `InformalLemma` and returns
  the corresponding `InformalLemma`. -/
unsafe def constantInfoToInformalLemma (c : ConstantInfo) : MetaM InformalLemma := do
  match c with
  | ConstantInfo.defnInfo c =>
      Lean.Meta.evalExpr' InformalLemma ``InformalLemma c.value
  | _ => panic! "Passed constantInfoToInformalLemma a `ConstantInfo` that is not a `InformalLemma`"

/-- Takes a `ConstantInfo` corresponding to a `InformalDefinition` and returns
  the corresponding `InformalDefinition`. -/
unsafe def constantInfoToInformalDefinition (c : ConstantInfo) : MetaM InformalDefinition := do
  match c with
  | ConstantInfo.defnInfo c =>
      Lean.Meta.evalExpr' InformalDefinition ``InformalDefinition c.value
  | _ => panic! "Passed constantInfoToInformalDefinition a
    `ConstantInfo` that is not a `InformalDefinition`"

unsafe def informalDependencies (c : ConstantInfo) : MetaM (Array Name) := do
  if Informal.isInformalLemma c then
    let informal ← constantInfoToInformalLemma c
    pure informal.dependencies.toArray
  else if Informal.isInformalDef c then
    let informal ← constantInfoToInformalDefinition c
    pure informal.dependencies.toArray
  else
    pure #[]

unsafe def informalLemmaToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ← constantInfoToInformalLemma c.2
  let dep ← informalLemma.dependencies.mapM fun d => depToString d
  pure s!"
Informal lemma: {informalLemma.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalLemma.math}
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalLemmaToWebString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ← constantInfoToInformalLemma c.2
  let dep ← informalLemma.dependencies.mapM fun d => depToWebString d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  pure s!"
**Informal lemma**: [{informalLemma.name}]({webPath}#L{lineNo}) :=
  *{informalLemma.math}*
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ← constantInfoToInformalDefinition c.2
  let dep ← informalDef.dependencies.mapM fun d => depToString d
  pure s!"
Informal def: {informalDef.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalDef.math}
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToWebString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ← constantInfoToInformalDefinition c.2
  let dep ← informalDef.dependencies.mapM fun d => depToWebString d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  pure s!"
**Informal def**: [{informalDef.name}]({webPath}#L{lineNo}) :=
  *{informalDef.math}*
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalToString (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToString c
  else if Informal.isInformalDef c.2 then
    informalDefToString c
  else
    pure ""

unsafe def informalToWebString (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToWebString c
  else if Informal.isInformalDef c.2 then
    informalDefToWebString c
  else
    pure ""

def informalFileHeader : String := s!"
# Informal definitions and lemmas

See [informal definitions and lemmas as a dependency graph](https://heplean.github.io/HepLean/graph.svg).

This file is automatically generated using `informal_lemma` and `informal_definition` commands
appearing in the raw Lean code of HepLean.

There is an implicit invitation to the reader to contribute to the formalization of
 informal definitions and lemmas. You may also wish to contribute to HepLean by including
 informal definitions and lemmas in the raw Lean code, especially if you do not have a
 background in Lean.

"

/-- Takes an import and outputs the list of `ConstantInfo` corresponding
  to an informal definition or lemma in that import, sorted by line number. -/
def importToInformal (i : Import) : MetaM (Array (Import × ConstantInfo)) := do
  let constants ← getConst i
  let constants := constants.filter (fun c => ¬ Lean.Name.isInternalDetail c.2.name)
  let informalConst := constants.filter fun c => Informal.isInformal c.2
  let informalConstLineNo ← informalConst.mapM fun c => getLineNumber c.2.name
  let informalConstWithLineNo := informalConst.zip informalConstLineNo
  let informalConstWithLineNoSort := informalConstWithLineNo.qsort (fun a b => a.2 < b.2)
  return informalConstWithLineNoSort.map (fun c => c.1)

unsafe def importToString (i : Import) : MetaM String := do
  let informalConst ← importToInformal i
  let informalPrint ← (informalConst.mapM informalToString).run'
  if informalPrint.isEmpty then
    pure ""
  else
    pure ("\n\n" ++ i.module.toString ++ "\n" ++ String.intercalate "\n\n" informalPrint.toList)

unsafe def importToWebString (i : Import) : MetaM String := do
  let informalConst ← importToInformal i
  let informalPrint ← (informalConst.mapM informalToWebString).run'
  if informalPrint.isEmpty then
    pure ""
  else
    pure ("\n\n## " ++ i.module.toString ++ "\n" ++ String.intercalate "\n\n" informalPrint.toList)

section dotFile
/-!

## Making the dot file for dependency graph.

-/

/-- Turns a formal definition or lemma into a node of a dot graph. -/
def formalToNode (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (mod.toString.replace "." "/") ++ ".lean"
  let docstring ← getDocString d
  pure s!"\"{d}\"[label=\"{d}\", shape=box, style=filled, fillcolor=green,
    href=\"{webPath}#L{lineNo}\", tooltip=\"{docstring}\"]"

unsafe def informalLemmaToNode (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  let informalLemma ← (constantInfoToInformalLemma c.2)
  pure s!"\"{c.2.name}\"[label=\"{c.2.name}\", shape=ellipse, style=filled, fillcolor=orange,
    href=\"{webPath}#L{lineNo}\", tooltip=\"{informalLemma.math}\"]"

unsafe def informalDefToNode (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  let informalDef ← (constantInfoToInformalDefinition c.2)
  pure s!"\"{c.2.name}\"[label=\"{c.2.name}\", shape=box, style=filled, fillcolor=orange,
    href=\"{webPath}#L{lineNo}\", tooltip=\"{informalDef.math}\"]"

unsafe def informalToNode (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToNode c
  else if Informal.isInformalDef c.2 then
    informalDefToNode c
  else
    pure ""

unsafe def informalLemmaToEdges (c : Import × ConstantInfo) : MetaM (String) := do
  let informalLemma ← constantInfoToInformalLemma c.2
  let deps := informalLemma.dependencies
  let edge := deps.map (fun d => s!"\"{d}\" -> \"{c.2.name}\"")
  pure (String.intercalate "\n" edge)

unsafe def informalDefToEdges (c : Import × ConstantInfo) : MetaM (String) := do
  let informalDef ← constantInfoToInformalDefinition c.2
  let deps := informalDef.dependencies
  let edge := deps.map (fun d => s!"\"{d}\" -> \"{c.2.name}\"")
  pure (String.intercalate "\n" edge)

unsafe def informalToEdges (c : Import × ConstantInfo) : MetaM (String) := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToEdges c
  else if Informal.isInformalDef c.2 then
    informalDefToEdges c
  else
    pure ""

unsafe def mkDot (imports : Array Import) : MetaM String := do
  let informal ← imports.mapM importToInformal
  let informal := informal.flatten
  let deps ← (informal.map (fun c => c.2)).mapM informalDependencies
  let deps := deps.flatten
  let informal_name := informal.map (fun c => c.2.name)
  let formal_deps := deps.filter (fun d => d ∉ informal_name)
  let formal_nodes ← formal_deps.mapM formalToNode
  let nodes := String.intercalate "\n" formal_nodes.toList
  let informalLemmaNodes ← informal.mapM informalToNode
  let informalNodes := String.intercalate "\n" informalLemmaNodes.toList
  let edges ← informal.mapM informalToEdges
  let edges := String.intercalate "\n" edges.toList
  let header := "strict digraph G {
    bgcolor=\"lightyellow\";
    label=\"Informal dependency graph for HepLean\";
    labelloc=\"t\";
    labeljust=\"l\";
    edge [arrowhead=vee];"
  let footer := "}"
  pure (header ++ "\n" ++ nodes ++ "\n" ++ informalNodes ++ "\n" ++ edges ++ "\n" ++ footer)

end dotFile

/-!

## Main function

-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name := `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let imports := hepLeanMod.imports.filter (fun c => c.module ≠ `Init)
  let importString ← CoreM.withImportModules #[`HepLean] (imports.mapM importToString).run'
  IO.println (String.intercalate "" importString.toList)
  /- Writing out informal file. -/
  let fileOut : System.FilePath := {toString := "./docs/Informal.md"}
  if "mkFile" ∈ args then
    let importWebString ← CoreM.withImportModules #[`HepLean] (imports.mapM importToWebString).run'
    let out := String.intercalate "\n" importWebString.toList
    IO.println (s!"Informal file made.")
    IO.FS.writeFile fileOut (informalFileHeader ++ out)
  /- Making the dot file. -/
  if "mkDot" ∈ args then
    let dot ← CoreM.withImportModules #[`HepLean] (mkDot imports).run'
    let dotFile : System.FilePath := {toString := "./docs/InformalDot.dot"}
    IO.FS.writeFile dotFile dot
    IO.println (s!"Dot file made.")
  pure 0
