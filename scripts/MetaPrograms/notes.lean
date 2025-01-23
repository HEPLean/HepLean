/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Basic
import HepLean.Meta.Remark.Properties
import HepLean.Meta.Notes.ToHTML
/-!

# Extracting notes from Lean files

-/

open Lean System Meta HepLean

inductive NotePart
  | h1 : String → NotePart
  | h2 : String → NotePart
  | p : String → NotePart
  | name : Name → NotePart

def formalContent (name : Name) : MetaM String := do
  let line ← Name.lineNumber name
  let decl ← Name.getDeclString name
  let fileName ← Name.fileName name
  let webAddress : String ← Name.toGitHubLink fileName line
  pure decl


def NotePart.toYMLM : NotePart →  MetaM String
  | NotePart.h1 s => pure s!"
  - type: h1
    content: \"{s}\""
  | NotePart.h2 s => pure s!"
  - type: h2
    content: \"{s}\""
  | NotePart.p s => pure s!"
  - type: p
    content: \"{s}\""
  | NotePart.name n => do
  match (← RemarkInfo.IsRemark n) with
  | true =>
    let remarkInfo ← RemarkInfo.getRemarkInfo n
    let content := remarkInfo.content
    let contentIndent := content.replace "\n" "\n      "
    let shortName := remarkInfo.name.toString
    return s!"
  - type: remark
    name: \"{shortName}\"
    content: |
      {contentIndent}"
  | false =>
  let content ← formalContent n
  let contentIndent := content.replace "\n" "\n      "
  return s!"
  - type: name
    content: |
      {contentIndent}"

structure Note where
  title : String
  /-- The curators of the note are the people who put the note together.
    This may not conicide with the original authors of the material. -/
  curators : List String
  parts : List NotePart

def Note.toYML : Note → MetaM String
  | ⟨title, curators, parts⟩ => return s!"
title: \"{title}\"
curators: {curators}
parts:
  {String.intercalate "\n" (← parts.mapM NotePart.toYMLM)}"

def perturbationTheory : Note where
  title := "Proof of Wick's theorem"
  curators := ["Joseph Tooby-Smith"]
  parts := [
    .h1 "Field statistics",
    .p "A quantum field can either be a bosonic or fermionic. This information is
      contained in the inductive type `FieldStatistic`. This is defined as follows:",
    .name `FieldStatistic,
    .h1 "Field specifications",
    .name `fieldSpecification_intro,
    .name `FieldSpecification]

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let ymlString ← CoreM.withImportModules #[`HepLean] (perturbationTheory.toYML).run'
  let fileOut : System.FilePath := {toString := "./docs/_data/perturbationTheory.yml"}
  IO.println (s!"YML file made.")
  IO.FS.writeFile fileOut ymlString
  pure 0
