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

/-- The information from a `note ...` command. To be used in a note file-/
structure NoteInfo where
  /-- The content of the note. -/
  content : String
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. -/
  line : Nat

/-- Enviroment extention to store `note ...`. -/
initialize noteExtension : SimplePersistentEnvExtension NoteInfo (Array NoteInfo) ←
  registerSimplePersistentEnvExtension {
    name := `noteExtension
    addEntryFn := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Syntax for the `note ...` command -/
syntax (name := note_comment) "note " str : command

/-- Elaborator for the `note ...` command -/
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

/-- Enviroment extention to store `note_attr`. -/
initialize noteDeclExtension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `noteDeclExtension
    addEntryFn := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- The `note_attr` attribute is used to display formally verified commands within a note. -/
initialize noteAttribute : Unit ←
  registerBuiltinAttribute {
    name := `note_attr
    descr := "Note attribute"
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName _ _ => do
      modifyEnv fun env => noteDeclExtension.addEntry env declName
  }


/-- Enviroment extention to store `note_attr_informal`. -/
initialize noteInformalDeclExtension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `noteInformalDeclExtension
    addEntryFn := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- The `note_attr_informal` attribute is used to display informal commands within a note. -/
initialize noteInformalAttribute : Unit ←
  registerBuiltinAttribute {
    name := `note_attr_informal
    descr := "Informal note attribute"
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName _ _ => do
      modifyEnv fun env => noteInformalDeclExtension.addEntry env declName
  }

/-!

## Notes

-/

/-- A note consists of a title and a list of Lean files which make up the note. -/
structure NoteFile where
  /-- The overall title of the note. -/
  title : String
  /-- The abstract of the note. -/
  abstract : String
  /-- A list of authors. -/
  authors : List String
  /-- The files making up the note in the order in which they should appear. -/
  files : List Name

namespace NoteFile

variable (N : NoteFile)

/-- All imports associated to a note. -/
def imports : Array Import := (N.files.map fun f => {module := f}).toArray

end NoteFile

end HepLean