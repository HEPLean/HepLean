/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/

def main (_: List String) : IO UInt32 := do
  println! "Style lint ... "
  let styleLint ← IO.Process.output {cmd := "lake", args := #["exe", "hepLean_style_lint"]}
  println! styleLint.stdout
  println! "Building ... "
  let build ← IO.Process.output {cmd := "lake", args := #["build"]}
  println! build.stdout
  println! "File imports ... "
  let importCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_file_imports"]}
  println! importCheck.stdout
  println! "Lean linter ..."
  let leanCheck ← IO.Process.output {cmd := "lake", args := #["exe", "runLinter", "PhysLean"]}
  println! leanCheck.stdout
  pure 0
