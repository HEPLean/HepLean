/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Remark.Basic
/-!

## Underlying structure for remarks
-/

namespace HepLean
open Lean System Meta

/-- All remarks in the enviroment. -/
def Name.allRemarkInfo : MetaM (List RemarkInfo) := do
  let env ← getEnv
  let allRemarks := (remarkExtension.getState env)
  pure allRemarks.toList

/-- The full name of a remark (name and namespace). -/
def RemarkInfo.toFullName (r : RemarkInfo) : Name :=
  if r.nameSpace != .anonymous then
    (r.nameSpace.toString ++ "." ++ r.name.toString).toName
  else
    r.name

/-- A Bool which is true if a name correponds to a remark. -/
def RemarkInfo.IsRemark (n : Name) : MetaM Bool := do
  let allRemarks ← Name.allRemarkInfo
  let r := allRemarks.find? (fun r => r.toFullName = n)
  match r with
  | some _ => pure true
  | none => pure false

/-- Gets the remarkInfo from a name corresponding to a remark.. -/
def RemarkInfo.getRemarkInfo (n : Name) : MetaM RemarkInfo := do
  let allRemarks ← Name.allRemarkInfo
  let r := allRemarks.find? (fun r => r.toFullName = n)
  match r with
  | some r => pure r
  | none => throwError s!"No remark named {n}"

end HepLean
