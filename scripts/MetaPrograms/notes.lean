/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Basic
import HepLean.Meta.Remark.Properties
import HepLean.Meta.Notes.ToHTML
import Mathlib.Lean.CoreM
import HepLean
/-!

# Extracting notes from Lean files

-/

open Lean System Meta HepLean

inductive NameStatus
  | complete : NameStatus
  | incomplete : NameStatus

instance : ToString NameStatus where
  toString
    | NameStatus.complete => "complete"
    | NameStatus.incomplete => "incomplete"

inductive NotePart
  | h1 : String → NotePart
  | h2 : String → NotePart
  | p : String → NotePart
  | name : Name → NameStatus → NotePart
  | warning : String → NotePart

structure DeclInfo where
  line : Nat
  fileName : Name
  name : Name
  status : NameStatus
  declString : String
  docString : String

def DeclInfo.ofName (n : Name) (ns : NameStatus): MetaM DeclInfo := do
  let line ← Name.lineNumber n
  let fileName ← Name.fileName n
  let declString ← Name.getDeclString n
  let docString ← Name.getDocString n
  pure {
    line := line,
    fileName := fileName,
    name := n,
    status := ns,
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
    status: \"{d.status}\"
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
  | x, NotePart.name n s => do
  match (← RemarkInfo.IsRemark n) with
  | true =>
    let remarkInfo ← RemarkInfo.getRemarkInfo n
    let content := remarkInfo.content
    let contentIndent := content.replace "\n" "\n      "
    let shortName := remarkInfo.name.toString
    let newString := s!"
  - type: remark
    name: \"{shortName}\"
    status : \"{s}\"
    link: \"{Name.toGitHubLink remarkInfo.fileName remarkInfo.line}\"
    content: |
      {contentIndent}"
    return ⟨x.1 ++ [newString], x.2⟩
  | false =>
  let newString ← (← DeclInfo.ofName n s).toYML
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
    .name `FieldSpecification.wicks_theorem_context .incomplete,
    .p "In this note we walk through the important parts of the proof of Wick's theorem
      for both fermions and bosons,
      as it appears in HepLean. We start with some basic definitions.",
    .h1 "Field operators",
    .h2 "Field statistics",
    .name ``FieldStatistic .complete,
    .name ``FieldStatistic.instCommGroup .complete,
    .name ``FieldStatistic.exchangeSign .complete,
    .h2 "Field specifications",
    .name ``FieldSpecification .complete,
    .h2 "Field operators",
    .name ``FieldSpecification.FieldOp .complete,
    .name ``FieldSpecification.fieldOpStatistic .complete,
    .name ``CreateAnnihilate .complete,
    .name ``FieldSpecification.CrAnFieldOp .complete,
    .name ``FieldSpecification.crAnStatistics .complete,
    .name `FieldSpecification.notation_remark .complete,
    .h2 "Field-operator free algebra",
    .name ``FieldSpecification.FieldOpFreeAlgebra .complete,
    .name `FieldSpecification.FieldOpFreeAlgebra.naming_convention .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.universality .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofCrAnListF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofFieldOpF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofFieldOpListF .complete,
    .name `FieldSpecification.FieldOpFreeAlgebra.notation_drop .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.fieldOpFreeAlgebraGrade .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.superCommuteF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum .complete,
    .h2 "Field-operator algebra",
    .name ``FieldSpecification.FieldOpAlgebra .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ι .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.universality .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnOp .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnList .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofFieldOp .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnList .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.anPart .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.crPart .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofFieldOp_eq_crPart_add_anPart .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.fieldOpAlgebraGrade .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.superCommute .incomplete,
    .h1 "Time ordering",
    .name ``FieldSpecification.crAnTimeOrderRel .incomplete,
    .name ``FieldSpecification.crAnTimeOrderSign .incomplete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.timeOrderF .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder_eq_maxTimeField_mul_finset .incomplete,
    .h1 "Normal ordering",
    .name ``FieldSpecification.normalOrderRel .incomplete,
    .name ``FieldSpecification.normalOrderSign .incomplete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.normalOrderF .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder .incomplete,
    .h2 "Some lemmas",
    .name ``FieldSpecification.normalOrderSign_eraseIdx .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnOp_superCommute_normalOrder_ofCrAnList_sum .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum .incomplete,
    .h1 "Wick Contractions",
    .h2 "Definition",
    .name ``WickContraction .incomplete,
    .name ``WickContraction.GradingCompliant .incomplete,
    .h2 "Aside: Cardinality",
    .name ``WickContraction.card_eq_cardFun .incomplete,
    .h2 "Constructors",
    .p "There are a number of ways to construct a Wick contraction from
      other Wick contractions or single contractions.",
    .name ``WickContraction.insertAndContract .incomplete,
    .name ``WickContraction.join .incomplete,
    .h2 "Sign",
    .name ``WickContraction.sign .incomplete,
    .name ``WickContraction.join_sign .incomplete,
    .name ``WickContraction.sign_insert_none .incomplete,
    .name ``WickContraction.sign_insert_none_zero .incomplete,
    .name ``WickContraction.sign_insert_some_of_not_lt .incomplete,
    .name ``WickContraction.sign_insert_some_of_lt .incomplete,
    .name ``WickContraction.sign_insert_some_zero .incomplete,
    .h2 "Normal order",
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_none .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_some .incomplete,
    .h1 "Static contractions",
    .name ``WickContraction.staticContract .incomplete,
    .name ``WickContraction.staticContract_insert_some_of_lt .incomplete,
    .name ``WickContraction.staticContract_insert_none .incomplete,
    .h1 "Time contractions",
    .name ``FieldSpecification.FieldOpAlgebra.timeContract .incomplete,
    .name ``WickContraction.timeContract .incomplete,
    .name ``WickContraction.timeContract_insert_none .incomplete,
    .name ``WickContraction.timeContract_insert_some_of_not_lt .incomplete,
    .name ``WickContraction.timeContract_insert_some_of_lt .incomplete,
    .h1 "Wick terms",
    .name ``WickContraction.wickTerm .incomplete,
    .name ``WickContraction.wickTerm_empty_nil .incomplete,
    .name ``WickContraction.wickTerm_insert_none .incomplete,
    .name ``WickContraction.wickTerm_insert_some .incomplete,
    .name ``WickContraction.mul_wickTerm_eq_sum .incomplete,
    .h1 "Static wick terms",
    .name ``WickContraction.staticWickTerm .incomplete,
    .name ``WickContraction.staticWickTerm_empty_nil .incomplete,
    .name ``WickContraction.staticWickTerm_insert_zero_none .incomplete,
    .name ``WickContraction.staticWickTerm_insert_zero_some .incomplete,
    .name ``WickContraction.mul_staticWickTerm_eq_sum .incomplete,
    .h1 "The three Wick's theorems",
    .name ``FieldSpecification.wicks_theorem .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.static_wick_theorem .incomplete,
    .name ``FieldSpecification.FieldOpAlgebra.wicks_theorem_normal_order .incomplete
    ]

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let ymlString ← CoreM.withImportModules #[`HepLean] (perturbationTheory.toYML).run'
  let fileOut : System.FilePath := {toString := "./docs/_data/perturbationTheory.yml"}
  IO.println (s!"YML file made.")
  IO.FS.writeFile fileOut ymlString
  pure 0
