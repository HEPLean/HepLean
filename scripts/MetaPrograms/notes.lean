/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Basic
import HepLean.Meta.Remark.Properties
import HepLean.Meta.Notes.ToHTML
import Mathlib.Lean.CoreM
/-!

# Extracting notes from Lean files

-/

open Lean System Meta HepLean

inductive NotePart
  | h1 : String → NotePart
  | h2 : String → NotePart
  | p : String → NotePart
  | name : Name → NotePart
  | warning : String → NotePart

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

def DeclInfo.toYML (d : DeclInfo) : MetaM String := do
  let declStringIndent := d.declString.replace "\n" "\n      "
  let docStringIndent := d.docString.replace "\n" "\n      "
  let link := Name.toGitHubLink d.fileName d.line
  return s!"
  - type: name
    name: {d.name}
    line: {d.line}
    fileName: {d.fileName}
    link: \"{link}\"
    docString: |
      {docStringIndent}
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
  | x, NotePart.warning s =>
    let newString := s!"
  - type: warning
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
    link: \"{Name.toGitHubLink remarkInfo.fileName remarkInfo.line}\"
    content: |
      {contentIndent}"
    return ⟨x.1 ++ [newString], x.2⟩
  | false =>
  let newString ← (← DeclInfo.ofName n).toYML
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
    .warning "This note is a work in progress and is not finished. Use with caution.
      (5th Feb 2025)",
    .h1 "Introduction",
    .name `FieldSpecification.wicks_theorem_context,
    .p "In this note we walk through the important parts of the proof of Wick's theorem
      for both fermions and bosons,
      as it appears in HepLean. We start with some basic definitions.",
    .h1 "Field operators",
    .h2 "Field statistics",
    .name `FieldStatistic,
    .name `FieldStatistic.instCommGroup,
    .name `FieldStatistic.exchangeSign,
    .h2 "Field specifications",
    .name `fieldSpecification_intro,
    .name `FieldSpecification,
    .h2 "Field operators",
    .name `FieldSpecification.FieldOp,
    .name `FieldSpecification.statesStatistic,
    .name `FieldSpecification.CrAnFieldOp,
    .name `FieldSpecification.crAnStatistics,
    .name `FieldSpecification.notation_remark,
    .h2 "Field-operator free algebra",
    .name `FieldSpecification.FieldOpFreeAlgebra,
    .name `FieldSpecification.FieldOpFreeAlgebra.naming_convention,
    .name `FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF,
    .name `FieldSpecification.FieldOpFreeAlgebra.ofCrAnListF,
    .name `FieldSpecification.FieldOpFreeAlgebra.ofFieldOpF,
    .name `FieldSpecification.FieldOpFreeAlgebra.ofFieldOpListF,
    .name `FieldSpecification.FieldOpFreeAlgebra.fieldOpFreeAlgebraGrade,
    .name `FieldSpecification.FieldOpFreeAlgebra.superCommuteF,
    .name `FieldSpecification.FieldOpFreeAlgebra.superCommuteF_ofCrAnListF_ofFieldOpListF_eq_sum,
    .h2 "Field-operator algebra",
    .name `FieldSpecification.FieldOpAlgebra,
    .name `FieldSpecification.FieldOpAlgebra.ofCrAnFieldOp,
    .name `FieldSpecification.FieldOpAlgebra.ofCrAnFieldOpList,
    .name `FieldSpecification.FieldOpAlgebra.ofFieldOp,
    .name `FieldSpecification.FieldOpAlgebra.ofCrAnFieldOpList,
    .name `FieldSpecification.FieldOpAlgebra.fieldOpAlgebraGrade,
    .name `FieldSpecification.FieldOpAlgebra.superCommute,
    .h1 "Time ordering",
    .name `FieldSpecification.crAnTimeOrderRel,
    .name `FieldSpecification.crAnTimeOrderSign,
    .name `FieldSpecification.FieldOpFreeAlgebra.timeOrderF,
    .name `FieldSpecification.FieldOpAlgebra.timeOrder,
    .name `FieldSpecification.FieldOpAlgebra.timeOrder_eq_maxTimeField_mul_finset,
    .h1 "Normal ordering",
    .name `FieldSpecification.normalOrderRel,
    .name `FieldSpecification.normalOrderSign,
    .name `FieldSpecification.FieldOpFreeAlgebra.normalOrderF,
    .name `FieldSpecification.FieldOpAlgebra.normalOrder,
    .h2 "Some lemmas",
    .name `FieldSpecification.normalOrderSign_eraseIdx,
    .name `FieldSpecification.FieldOpAlgebra.ofCrAnFieldOp_superCommute_normalOrder_ofCrAnFieldOpList_sum,
    .name `FieldSpecification.FieldOpAlgebra.ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum,
    .h1 "Wick Contractions",
    .h2 "Definition",
    .name `WickContraction,
    .name `WickContraction.GradingCompliant,
    .h2 "Aside: Cardinality",
    .name `WickContraction.card_eq_cardFun,
    .h2 "Constructors",
    .p "There are a number of ways to construct a Wick contraction from
      other Wick contractions or single contractions.",
    .name `WickContraction.insertAndContract,
    .name `WickContraction.join,
    .h2 "Sign",
    .name `WickContraction.sign,
    .name `WickContraction.join_sign,
    .name `WickContraction.sign_insert_none,
    .name `WickContraction.sign_insert_none_zero,
    .name `WickContraction.sign_insert_some_of_not_lt,
    .name `WickContraction.sign_insert_some_of_lt,
    .name `WickContraction.sign_insert_some_zero,
    .h2 "Normal order",
    .name `FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_none,
    .name `FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_some,
    .h1 "Static contractions",
    .name `WickContraction.staticContract,
    .name `WickContraction.staticContract_insert_some_of_lt,
    .name `WickContraction.staticContract_insert_none,
    .h1 "Time contractions",
    .name `FieldSpecification.FieldOpAlgebra.timeContract,
    .name `WickContraction.timeContract,
    .name `WickContraction.timeContract_insert_none,
    .name `WickContraction.timeContract_insert_some_of_not_lt,
    .name `WickContraction.timeContract_insert_some_of_lt,
    .h1 "Wick terms",
    .name `WickContraction.wickTerm,
    .name `WickContraction.wickTerm_empty_nil,
    .name `WickContraction.wickTerm_insert_none,
    .name `WickContraction.wickTerm_insert_some,
    .name `WickContraction.mul_wickTerm_eq_sum,
    .h1 "Static wick terms",
    .name `WickContraction.staticWickTerm,
    .name `WickContraction.staticWickTerm_empty_nil,
    .name `WickContraction.staticWickTerm_insert_zero_none,
    .name `WickContraction.staticWickTerm_insert_zero_some,
    .name `WickContraction.mul_staticWickTerm_eq_sum,
    .h1 "The three Wick's theorems",
    .name `FieldSpecification.wicks_theorem,
    .name `FieldSpecification.FieldOpAlgebra.static_wick_theorem,
    .name `FieldSpecification.FieldOpAlgebra.wicks_theorem_normal_order
    ]

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let ymlString ← CoreM.withImportModules #[`HepLean] (perturbationTheory.toYML).run'
  let fileOut : System.FilePath := {toString := "./docs/_data/perturbationTheory.yml"}
  IO.println (s!"YML file made.")
  IO.FS.writeFile fileOut ymlString
  pure 0
