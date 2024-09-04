/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

## Getting an array of all file paths in HepLean.

-/

open Lean Elab System

/-! TODO: Make this definition more functional in style. -/

/-- The recursive function underlying `allFilePaths`. -/
partial def allFilePaths.go (prev : Array FilePath)
  (root : Name) (path : FilePath) : IO (Array FilePath) := do
  let mut r := prev
  for entry in ← path.readDir do
    if ← entry.path.isDir then
      r ← go r (root.mkStr entry.fileName) entry.path
    else
      r := r.push (root.toString.replace "." "/" ++ "/" ++ entry.fileName)
  pure r

/-- Gets an array of all file paths in `HepLean`. -/
partial def allFilePaths : IO (Array FilePath) := do
  allFilePaths.go (#[] : Array FilePath) `HepLean ("./HepLean" : FilePath)
