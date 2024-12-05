/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Informal.Basic
import HepLean.Meta.Basic
/-!

## Informal definitions and lemmas

-/
open Lean Elab System

namespace Informal

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalLemma` or a
  `InformalDefinition`. -/
def isInformal (c : ConstantInfo) : Bool :=
  match c with
  | ConstantInfo.defnInfo c =>
    if c.type.isAppOf ``InformalDefinition ∨ c.type.isAppOf ``InformalLemma then true else false
  | _ => false

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalLemma`. -/
def isInformalLemma (c : ConstantInfo) : Bool :=
  match c with
  | ConstantInfo.defnInfo c =>
    if c.type.isAppOf ``InformalLemma then true else false
  | _ => false

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalDefinition`. -/
def isInformalDef (c : ConstantInfo) : Bool :=
  match c with
  | ConstantInfo.defnInfo c =>
    if c.type.isAppOf ``InformalDefinition then true else false
  | _ => false

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

end Informal

namespace HepLean

/-- The number of informal lemmas in HepLean. -/
def noInformalLemmas : MetaM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  let x := x.flatten
  let x := x.filter (Informal.isInformal)
  let x := x.filter (Informal.isInformalLemma)
  pure x.toList.length

/-- The number of informal definitions in HepLean. -/
def noInformalDefs : MetaM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  let x := x.flatten
  let x := x.filter (Informal.isInformal)
  let x := x.filter (Informal.isInformalDef)
  pure x.toList.length

end HepLean
