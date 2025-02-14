/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
import PhysLean.Meta.Informal.Basic
/-!

## Informal definitions and lemmas

-/
open Lean

namespace Informal

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalLemma` or a
  `InformalDefinition`. -/
def isInformal : ConstantInfo → Bool
  | .defnInfo c => c.type.isConstOf ``InformalDefinition ∨ c.type.isConstOf ``InformalLemma
  | _ => false

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalLemma`. -/
def isInformalLemma : ConstantInfo → Bool
  | .defnInfo c => c.type.isConstOf ``InformalLemma
  | _ => false

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalDefinition`. -/
def isInformalDef : ConstantInfo → Bool
  | .defnInfo c => c.type.isConstOf ``InformalDefinition
  | _ => false

/-- Takes a `ConstantInfo` corresponding to a `InformalLemma` and returns
  the corresponding `InformalLemma`. -/
unsafe def constantInfoToInformalLemma (c : ConstantInfo) : CoreM InformalLemma := do
  match c with
  | .defnInfo c => evalConstCheck InformalLemma ``InformalLemma c.name
  | _ => panic! "Passed constantInfoToInformalLemma a `ConstantInfo` that is not a `InformalLemma`"

/-- Takes a `ConstantInfo` corresponding to a `InformalDefinition` and returns
  the corresponding `InformalDefinition`. -/
unsafe def constantInfoToInformalDefinition (c : ConstantInfo) : CoreM InformalDefinition := do
  match c with
  | .defnInfo c => evalConstCheck InformalDefinition ``InformalDefinition c.name
  | _ => panic!
    "Passed constantInfoToInformalDefinition a `ConstantInfo` that is not a `InformalDefinition`"

end Informal

namespace PhysLean

/-- The number of informal lemmas in PhysLean. -/
def noInformalLemmas : CoreM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  x.flatFilterSizeM fun c => return Informal.isInformalLemma c

/-- The number of informal definitions in PhysLean. -/
def noInformalDefs : CoreM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  x.flatFilterSizeM fun c => return Informal.isInformalDef c

end PhysLean
