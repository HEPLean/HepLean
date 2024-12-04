/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Basic
import HepLean.Meta.Notes.ToHTML
/-!

# Extracting notes from Lean files

-/

open Lean System Meta HepLean

def pertubationTheory : NoteFile where
  title := "Notes on Perturbation Theory"
  abstract := "Notes on perturbation theory in quantum field theory."
  authors := ["Joseph Tooby-Smith"]
  files := [
    `HepLean.PerturbationTheory.Wick.Algebra,
    `HepLean.PerturbationTheory.Wick.Contract
    ]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let htmlString ← CoreM.withImportModules #[`HepLean] (pertubationTheory.toHTMLString).run'
  let htmlFile : System.FilePath := {toString := "./docs/PertubationTheory.html"}
  IO.FS.writeFile htmlFile htmlString
  IO.println (s!"HTML file made.")
  pure 0
