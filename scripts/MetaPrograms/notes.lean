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

structure DeclInfo where
  line : Nat
  fileName : Name
  name : Name
  declString : String
  docString : String

def DeclInfo.ofName (n : Name) : MetaM DeclInfo := do
  let line ← Name.lineNumber n
  let fileName ← Name.fileName n
  let declString ← Name.getDeclString n
  let docString ← Name.getDocString n
  pure {
    line := line,
    fileName := fileName,
    name := n,
    declString := declString,
    docString := docString}

def DeclInfo.toYML (d : DeclInfo) : String :=
  let declStringIndent := d.declString.replace "\n" "\n      "
  s!"
  - type: name
    name: {d.name}
    line: {d.line}
    fileName: {d.fileName}
    docString: \"{d.docString}\"
    declString: |
      {declStringIndent}"

def NotePart.toYMLM : ((List String) × Nat × Nat) →  NotePart → MetaM ((List String) × Nat × Nat)
  | x, NotePart.h1 s =>
    let newString := s!"
  - type: h1
    sectionNo: {x.2.1.succ}
    content: \"{s}\""
    return ⟨x.1 ++ [newString], ⟨Nat.succ x.2.1, 0⟩⟩
  | x, NotePart.h2 s =>
    let newString := s!"
  - type: h2
    sectionNo: \"{x.2.1}.{x.2.2.succ}\"
    content: \"{s}\""
    return ⟨x.1 ++ [newString], ⟨x.2.1, Nat.succ x.2.2⟩⟩
  | x, NotePart.p s =>
    let newString := s!"
  - type: p
    content: \"{s}\""
    return ⟨x.1 ++ [newString], x.2⟩
  | x, NotePart.name n => do
  match (← RemarkInfo.IsRemark n) with
  | true =>
    let remarkInfo ← RemarkInfo.getRemarkInfo n
    let content := remarkInfo.content
    let contentIndent := content.replace "\n" "\n      "
    let shortName := remarkInfo.name.toString
    let newString := s!"
  - type: remark
    name: \"{shortName}\"
    content: |
      {contentIndent}"
    return ⟨x.1 ++ [newString], x.2⟩
  | false =>
  let newString :=  (← DeclInfo.ofName n).toYML
  return ⟨x.1 ++ [newString], x.2⟩

structure Note where
  title : String
  /-- The curators of the note are the people who put the note together.
    This may not conicide with the original authors of the material. -/
  curators : List String
  parts : List NotePart

def Note.toYML : Note → MetaM String
  | ⟨title, curators, parts⟩ => do
  let parts ← parts.foldlM NotePart.toYMLM ([], ⟨0, 0⟩)
  return s!"
title: \"{title}\"
curators: {String.intercalate "," curators}
parts:
  {String.intercalate "\n" parts.1}"

def perturbationTheory : Note where
  title := "Proof of Wick's theorem"
  curators := ["Joseph Tooby-Smith"]
  parts := [
    .h1 "Introduction",
    .name `FieldSpecification.wicks_theorem_context,
    .p "In this note we walk through the important parts of the proof of Wick's theorem
      for both fermions and bosons,
      as it appears in HepLean. We start with some basic definitions.",
    .h1 "Preliminary definitions",
    .h2 "Field statistics",
    .p "A quantum field can either be a bosonic or fermionic. This information is
      contained in the inductive type `FieldStatistic`. This is defined as follows:",
    .name `FieldStatistic,
    .p "Field statistics form a commuative group isomorphic to ℤ₂, with
      the bosonic element of `FieldStatistic` being the identity element.",
    .p "Most of our use of field statistics will come by comparing two field statistics
      and picking up a minus sign when they are both fermionic. This concept is
      made precise using the notion of an exchange sign, defined as:",
    .name `FieldStatistic.exchangeSign,
    .p "We use the notation `𝓢(a,b)` as shorthand for the exchange sign of
      `a` and `b`.",
    .h2 "Field specifications",
    .name `fieldSpecification_intro,
    .name `FieldSpecification,
    .h2 "States",
    .h2 "Time ordering",
    .h2 "Creation and annihilation states",
    .h2 "Normal ordering",
    .h1 "Algebras",
    .h2 "State free-algebra",
    .h2 "CrAnState free-algebra",
    .h2 "Proto operator algebra",
    .h1 "Contractions"
    ]

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let ymlString ← CoreM.withImportModules #[`HepLean] (perturbationTheory.toYML).run'
  let fileOut : System.FilePath := {toString := "./docs/_data/perturbationTheory.yml"}
  IO.println (s!"YML file made.")
  IO.FS.writeFile fileOut ymlString
  pure 0
