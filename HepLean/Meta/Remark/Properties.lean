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

def Name.allRemarkInfo : MetaM (List RemarkInfo) := do
  let env ← getEnv
  let allRemarks := (remarkExtension.getState env)
  pure allRemarks.toList

def RemarkInfo.toFullName (r : RemarkInfo) :  Name :=
  if r.nameSpace != .anonymous then
    (r.nameSpace.toString ++ "." ++ r.name.toString).toName
  else
    r.name

def RemarkInfo.IsRemark (n : Name) : MetaM Bool := do
  let allRemarks ← Name.allRemarkInfo
  let r := allRemarks.find? (fun r => r.toFullName = n)
  match r with
  | some _ => pure true
  | none => pure false

def RemarkInfo.getRemarkInfo (n : Name) : MetaM RemarkInfo := do
  let allRemarks ← Name.allRemarkInfo
  let r := allRemarks.find? (fun r => r.toFullName = n)
  match r with
  | some r => pure r
  | none => throwError s!"No remark named {n}"

end HepLean
