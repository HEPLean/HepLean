/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Linter.TextBased
import Cli.Basic
/-!

# Text based style linters from Mathlib

This file is a copy of the `./scripts/lint_style.lean` executable from mathlib, adapted
to run text-based style linters from mathlib on HepLean.

That file is copyright Michael Rothgang, and is released under the Apache 2.0 license.
It is authored by Michael Rothgang.

-/

open Cli

/-- Implementation of the `lint_style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let errorStyle := match (args.hasFlag "github", args.hasFlag "update") with
    | (true, _) => ErrorFormat.github
    | (false, true) => ErrorFormat.exceptionsFile
    | (false, false) => ErrorFormat.humanReadable
  let mut numberErrorFiles : UInt32 := 0
  for s in ["HepLean.lean"] do
    let n ← lintAllFiles (System.mkFilePath [s]) errorStyle
    numberErrorFiles := numberErrorFiles + n
  return numberErrorFiles

/-- Setting up command line options and help text for `lake exe lint_style`. -/
-- so far, no help options or so: perhaps that is fine?
def heplean_lint_style : Cmd := `[Cli|
  lint_style VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in HepLean (adapted from mathlib's lint_style).
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    update;     "Print errors solely for the style exceptions file"
]

/-- The entry point to the `lake exe mathlib_textLint_on_hepLean` command. -/
def main (args : List String) : IO UInt32 := do heplean_lint_style.validate args
