/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import ImportGraph.RequiredModules
/-!

## Basic Lean meta programming commands

-/

namespace HepLean
open Lean System Meta

-- Define the structure to hold note information, including module name
structure NoteInfo where
  content : String
  fileName : Name
  line : Nat
  deriving Inhabited

-- Define the environment extension to store notes
initialize noteExtension : SimplePersistentEnvExtension NoteInfo (Array NoteInfo) ←
  registerSimplePersistentEnvExtension {
    name          := `noteExtension
    addEntryFn    := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]  -- Merge imported notes
  }

-- Define the syntax for the `note` command
syntax (name := note_comment) "note " str : command

-- Define the elaboration behavior (do nothing)
@[command_elab note_comment]
def elabNote : Lean.Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(note $s) => do

    let str : String := s.getString
    let pos := stx.getPos?
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let noteInfo : NoteInfo := { content := str, fileName := modName, line := line }
      modifyEnv fun env => noteExtension.addEntry env noteInfo

    | none => throwError "Invalid syntax for `note` command"
  | _ => throwError "Invalid syntax for `note` command"



/-!

## Note attribute

-/

initialize noteDeclExtension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name          := `noteDeclExtension
    addEntryFn    := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]  -- Merge imported notes
  }

initialize noteAttribute : Unit ←
  registerBuiltinAttribute {
    name  := `note_attr
    descr := "Note attribute"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _ _ => do
      modifyEnv fun env => noteDeclExtension.addEntry env declName
  }

initialize noteInformalDeclExtension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name          := `noteInformalDeclExtension
    addEntryFn    := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]  -- Merge imported notes
  }

initialize noteInformalAttribute : Unit ←
  registerBuiltinAttribute {
    name  := `note_attr_informal
    descr := "Informal note attribute"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _ _ => do
      modifyEnv fun env => noteInformalDeclExtension.addEntry env declName
  }

/-!

## Notes

-/

/-- A note consists of a title and a list of Lean files which make up the note. -/
structure NoteFile where
  title : String
  abstract : String
  authors : List String
  files : List Name

namespace NoteFile

variable (N : NoteFile)

/-- All imports associated to a note. -/
def imports : Array Import := (N.files.map fun f => {module := f}).toArray

end NoteFile

end HepLean
