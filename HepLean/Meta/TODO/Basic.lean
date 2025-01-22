/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import ImportGraph.RequiredModules
/-!

# Basic underlying structure for TODOs.

-/

namespace HepLean
open Lean System Meta

/-- The information from a `TODO ...` command. -/
structure todoInfo where
  /-- The content of the note. -/
  content : String
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. -/
  line : Nat

/-- Environment extension to store `todo ...`. -/
initialize todoExtension : SimplePersistentEnvExtension todoInfo (Array todoInfo) ←
  registerSimplePersistentEnvExtension {
    name := `todoExtension
    addEntryFn := fun arr todoInfor => arr.push todoInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Syntax for the `TODO ...` command. -/
syntax (name := todo_comment) "TODO " str : command

/-- Elaborator for the `TODO ...` command -/
@[command_elab todo_comment]
def elabTODO : Lean.Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(TODO $s) => do
    let str : String := s.getString
    let pos := stx.getPos?
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let todoInfo : todoInfo := { content := str, fileName := modName, line := line }
      modifyEnv fun env => todoExtension.addEntry env todoInfo
    | none => throwError "Invalid syntax for `TODO` command"
  | _ => throwError "Invalid syntax for `TODO` command"

end HepLean
