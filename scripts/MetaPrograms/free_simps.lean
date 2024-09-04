/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Batteries.Data.String.Matcher
import Lean
import HepLean.Meta.AllFilePaths
import HepLean.Meta.TransverseTactics
/-!

This file checks for non-terminating `simp` tactics which do not appear as `simp only`.

See also:
- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E
-/
open Lean Elab System

namespace Lean.Elab.TacticInfo

def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSimp (t : TacticInfo) : Bool :=
  match t.name? with
  | some ``Lean.Parser.Tactic.simp => true
  | _ => false

end Lean.Elab.TacticInfo

def visitTacticInfo (file : FilePath) (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSimp then return ()
  let stx := ti.stx
  match stx.getHeadInfo? with
  | .some (.synthetic ..) =>
     -- Not actual concrete syntax the user wrote. Ignore.
    return ()
  | _ =>  pure ()
  let some sp := stx.getPos? | return ()
  let startPosition := ci.fileMap.toPosition sp
  let some ep := stx.getTailPos? | return ()
  let s := Substring.mk ci.fileMap.source sp ep
  if ti.goalsAfter.length ≠ 0  ∧ ¬ String.containsSubstr s.toString  "only" then
    println! "./{file}:{startPosition.line}"

/- See conversation here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E -/
unsafe def processAllFiles : IO Unit := do
  let files ← allFilePaths
  let tasks := files.map fun f =>
    ((IO.asTask $ IO.Process.run
    {cmd := "lake", args := #["exe", "free_simps", f.toString]}), f)
  tasks.toList.enum.forM fun (n, (t, path)) => do
    println! "{n} of {tasks.toList.length}: {path}"
    let tn ← IO.wait (← t)
    match tn with
    | .ok x => println! x
    | .error _ => println! "Error"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [path] => transverseTactics path visitTacticInfo
  | _ => processAllFiles
