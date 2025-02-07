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
  isDef : Bool

def DeclInfo.ofName (n : Name) (ns : NameStatus): MetaM DeclInfo := do
  let line ← Name.lineNumber n
  let fileName ← Name.fileName n
  let declString ← Name.getDeclStringNoDoc n
  let docString ← Name.getDocString n
  let constInfo ← getConstInfo n
  let isDef := constInfo.isDef ∨ Lean.isStructure (← getEnv) n ∨ constInfo.isInductive
  pure {
    line := line,
    fileName := fileName,
    name := n,
    status := ns,
    declString := declString,
    docString := docString,
    isDef := isDef}

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
    isDef: {d.isDef}
    docString: |
      {docStringIndent}
    declString: |
      {declStringIndent}"

/-- In `(List String) × Nat × Nat` the first `Nat` is section number, the second `Nat`
  is subsection number, and the third `Nat` is defn. or lemma number.
  Definitions and lemmas etc are done by section not subsection. -/
def NotePart.toYMLM : ((List String) × Nat × Nat × Nat) →  NotePart →
    MetaM ((List String) × Nat × Nat × Nat)
  | x, NotePart.h1 s =>
    let newString := s!"
  - type: h1
    sectionNo: {x.2.1.succ}
    content: \"{s}\""
    return ⟨x.1 ++ [newString], ⟨Nat.succ x.2.1, 0, 0⟩⟩
  | x, NotePart.h2 s =>
    let newString := s!"
  - type: h2
    sectionNo: \"{x.2.1}.{x.2.2.1.succ}\"
    content: \"{s}\""
    return ⟨x.1 ++ [newString], ⟨x.2.1, Nat.succ x.2.2.1, x.2.2.2⟩⟩
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
  let newString := newString ++ s!"\n    declNo: \"{x.2.1}.{x.2.2.2.succ}\""
  return ⟨x.1 ++ [newString], ⟨x.2.1, x.2.2.1, Nat.succ x.2.2.2⟩⟩

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
    .name `FieldSpecification.wicks_theorem_context .incomplete,
    .p "In this note we walk through the important parts of the proof of Wick's theorem
      for both fermions and bosons,
      as it appears in HepLean. Not every lemma or definition is covered here.
      The aim is to give just enough that the story can be understood.",
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
    .name ``FieldSpecification.FieldOpAlgebra .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ι .complete,
    .name ``FieldSpecification.FieldOpAlgebra.universality .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnOp .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnList .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofFieldOp .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnList .complete,
    .name `FieldSpecification.FieldOpAlgebra.notation_drop .complete,
    .name ``FieldSpecification.FieldOpAlgebra.anPart .complete,
    .name ``FieldSpecification.FieldOpAlgebra.crPart .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofFieldOp_eq_crPart_add_anPart .complete,
    .name ``FieldSpecification.FieldOpAlgebra.fieldOpAlgebraGrade .complete,
    .name ``FieldSpecification.FieldOpAlgebra.superCommute .complete,
    .h1 "Time ordering",
    .name ``FieldSpecification.crAnTimeOrderRel .complete,
    .name ``FieldSpecification.crAnTimeOrderList .complete,
    .name ``FieldSpecification.crAnTimeOrderSign .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.timeOrderF .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder_eq_maxTimeField_mul_finset .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder_timeOrder_mid .complete,
    .h1 "Normal ordering",
    .name ``FieldSpecification.normalOrderRel .complete,
    .name ``FieldSpecification.normalOrderList .complete,
    .name ``FieldSpecification.normalOrderSign .complete,
    .name ``FieldSpecification.normalOrderSign_eraseIdx .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.normalOrderF .complete,
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder .complete,
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder_superCommute_eq_zero .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofCrAnOp_superCommute_normalOrder_ofCrAnList_sum .complete,
    .name ``FieldSpecification.FieldOpAlgebra.ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum .complete,
    .h1 "Wick Contractions",
    .h2 "Definition",
    .name ``WickContraction .complete,
    .name `WickContraction.contraction_notation .complete,
    .name ``WickContraction.GradingCompliant .complete,
    .h2 "Aside: Cardinality",
    .name ``WickContraction.card_eq_cardFun .complete,
    .h2 "Uncontracted elements",
    .name ``WickContraction.uncontracted .complete,
    .name ``WickContraction.uncontractedListGet .complete,
    .h2 "Constructors",
    .name ``WickContraction.insertAndContract .complete,
    .name ``WickContraction.insertLift_sum .complete,
    .name ``WickContraction.join .complete,
    .h2 "Sign",
    .name ``WickContraction.sign .complete,
    .name ``WickContraction.join_sign .complete,
    .name ``WickContraction.sign_insert_none .complete,
    .name ``WickContraction.sign_insert_none_zero .complete,
    .name ``WickContraction.sign_insert_some_of_not_lt .complete,
    .name ``WickContraction.sign_insert_some_of_lt .complete,
    .name ``WickContraction.sign_insert_some_zero .complete,
    .h2 "Normal order",
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_none .complete,
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder_uncontracted_some .complete,
    .h1 "Static Wicks theorem",
    .h2 "Static contractions",
    .name ``WickContraction.staticContract .complete,
    .name ``WickContraction.staticContract_insert_none .complete,
    .name ``WickContraction.staticContract_insert_some .complete,
    .h2 "Static wick terms",
    .name ``WickContraction.staticWickTerm .complete,
    .name ``WickContraction.staticWickTerm_empty_nil .complete,
    .name ``WickContraction.staticWickTerm_insert_zero_none .complete,
    .name ``WickContraction.staticWickTerm_insert_zero_some .complete,
    .name ``WickContraction.mul_staticWickTerm_eq_sum .complete,
    .h2 "The Static Wicks theorem",
    .name ``FieldSpecification.FieldOpAlgebra.static_wick_theorem .complete,
    .h1 "Wick's theorem",
    .h2 "Time contractions",
    .name ``FieldSpecification.FieldOpAlgebra.timeContract .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeContract_of_timeOrderRel .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeContract_of_not_timeOrderRel_expand .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeContract_mem_center .complete,
    .name ``WickContraction.timeContract .complete,
    .name ``WickContraction.timeContract_insert_none .complete,
    .name ``WickContraction.timeContract_insert_some_of_not_lt .complete,
    .name ``WickContraction.timeContract_insert_some_of_lt .complete,
    .name ``WickContraction.join_sign_timeContract .complete,
    .h2 "Wick terms",
    .name ``WickContraction.wickTerm .complete,
    .name ``WickContraction.wickTerm_empty_nil .complete,
    .name ``WickContraction.wickTerm_insert_none .complete,
    .name ``WickContraction.wickTerm_insert_some .complete,
    .name ``WickContraction.mul_wickTerm_eq_sum .complete,
    .h2 "Wick's theorem",
    .name ``FieldSpecification.wicks_theorem .complete,
    .h1 "Normal-ordered Wick's theorem",
    .name ``WickContraction.EqTimeOnly.timeOrder_staticContract_of_not_mem .complete,
    .name ``WickContraction.EqTimeOnly.staticContract_eq_timeContract_of_eqTimeOnly .complete,
    .name ``WickContraction.EqTimeOnly.timeOrder_timeContract_mul_of_eqTimeOnly_left .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder_ofFieldOpList_eqTimeOnly .complete,
    .name ``FieldSpecification.FieldOpAlgebra.normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty .complete,
    .name ``FieldSpecification.FieldOpAlgebra.timeOrder_haveEqTime_split .complete,
    .name ``FieldSpecification.FieldOpAlgebra.wicks_theorem_normal_order .complete
    ]

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let ymlString ← CoreM.withImportModules #[`HepLean] (perturbationTheory.toYML).run'
  let fileOut : System.FilePath := {toString := "./docs/_data/perturbationTheory.yml"}
  IO.println (s!"YML file made.")
  IO.FS.writeFile fileOut ymlString
  pure 0
