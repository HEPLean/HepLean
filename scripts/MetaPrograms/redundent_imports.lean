/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
import ImportGraph.Imports
/-!

# Extracting commands with no doc strings.

-/

open Lean System Meta PhysLean


def Imports.RedundentImports (imp : Import) : MetaM UInt32 := do
  let x ← redundantImports (some imp.module)
  if x.isEmpty then return 0
  println! "\n"
  println! (← Name.toFile imp.module)
  println! x.toList
  return 0

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports ← allImports
  let _ ← CoreM.withImportModules #[`PhysLean] (imports.mapM Imports.RedundentImports).run'
  return 0
