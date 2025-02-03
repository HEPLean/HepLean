/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Basic
import HepLean.Meta.TODO.Basic
import Mathlib.Lean.CoreM
/-!

# Turning TODOs into YAML

-/

open Lean System Meta HepLean


unsafe def getTodoInfo : MetaM (List todoInfo) := do
  let env ← getEnv
  let todoInfo := (todoExtension.getState env)
  pure (todoInfo.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList

def todoToYAML (todo : todoInfo) : MetaM String := do
  return s!"
- content: \"{todo.content}\"
  file: {todo.fileName}
  githubLink: {Name.toGitHubLink todo.fileName todo.line}
  line: {todo.line}"

unsafe def todosToYAML : MetaM String := do
  let todos ← getTodoInfo
  let todosYAML ← todos.mapM todoToYAML
  return String.intercalate "\n" todosYAML

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let ymlString ← CoreM.withImportModules #[`HepLean] (todosToYAML).run'
  println! ymlString
  let fileOut : System.FilePath := {toString := "./docs/_data/TODO.yml"}
  if "mkFile" ∈ args then
    IO.println (s!"TODOList file made.")
    IO.FS.writeFile fileOut ymlString
  pure 0
