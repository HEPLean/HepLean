/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
/-!

This file produces a list of places where `rfl` will complete the goal.



## References
The content of this file is based on the following sources (released under the Apache 2.0 license):

- https://github.com/dwrensha/tryAtEachStep/blob/main/tryAtEachStep.lean
- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

Modifications have been made to the original content of these files here.

See also:
- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E
-/
open Lean Elab System

partial def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  /- Very roughly, `Frontend.FrontendM (List (Environment × InfoState))` is equivalent
    to `Frontend.Context → Frontend.state → List (Environment × InfoState)`.

    The `←get` here is returning the inputted value of `Frontend.state`,
    from which we get the enviroment.
    -/
  let env := (←get).commandState.env
  /- Processes a single command, adding it to `env`. This is done using
    `modify fun s => { s with commands := s.commands.push cmd }` as part of
    `Frontend.processCommand`. -/
  let done ← Frontend.processCommand
  /- Gets the updated `Frontend.state`. -/
  let st := ← get
  /- Gets the infostate associated with the single command.  -/
  let infoState := st.commandState.infoState
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env, infoState)]
  else
    /- For each command, we return the enviroment before the command is processed,
      and the `infoState` associated with that command. -/
    return (env, infoState) :: (←processCommands)

namespace Lean.Elab.TacticInfo

def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Tactic.inductionAlt => false
  | some ``Lean.Parser.Tactic.case => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | some ``Lean.Parser.Tactic.exact => false
  | _ => true


end Lean.Elab.TacticInfo

def visitTacticInfo (file : FilePath) (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSubstantive then return ()
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
  for g in ti.goalsBefore do
    (← IO.getStdout).flush
    let mctx := ti.mctxBefore
    --let doprint : MetaM _ := Meta.ppGoal g
    --let x ← doprint.run' (s := { mctx := mctx })
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
              <| Tactic.run g (Tactic.evalTactic  (← `(tactic| rfl)))
    try
      let ((mvars, _tstate), _mstate) ← dotac.run {} { mctx := mctx }
      if mvars.length == 0 ∧ s.toString ≠ "rfl"
      then
        println! "./{file}:{startPosition.line}"
      pure ()
    catch _e =>
      pure ()
    pure ()

def visitInfo (file : FilePath)  (env : Environment) (ci : ContextInfo)
    (info : Info) (acc : List (IO Unit))
    : List (IO Unit) :=
  match info with
  | .ofTacticInfo ti =>
     (ci.runMetaM default
     (do setEnv env
         try visitTacticInfo file ci ti
         catch e =>
            println! "caught: {←e.toMessageData.toString}")) :: acc
  | _ =>   acc

def traverseForest (file : FilePath)  (steps : List (Environment × InfoState)) : List (IO Unit) :=
  let t := steps.map fun (env, infoState) ↦
    (infoState.trees.toList.map fun t ↦
      (Lean.Elab.InfoTree.foldInfo (visitInfo file env) [] t).reverse)
  t.join.join


unsafe def checkRfl (file : FilePath) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  /- This is equivalent to `(IO.FS.readFile file).bind (fun fileContent => do ...)`.  -/
  let fileContent ← IO.FS.readFile file
  enableInitializersExecution
  /- Get `Parser.InputContext` from file. -/
  let inputCtx := Parser.mkInputContext fileContent file.toString -- The input content of the file
  /- We parse the header. Recall that the parser is takes a string and
    outputs a Lean syntax object. -/
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  /- Recall that the elborator turns a Lean syntax object into a Lean Expr object.
    In the below, we process the header, creating an enviroment with the relevent imports.
    This can be thought of as creating an import only file.  -/
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  for msg in messages.toList do
    println! "{← msg.toString}"
  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  /- As part of the enviroment header is the module name. This is not included
    in our current `env`. So we include it now. -/
  let env1 := env.setMainModule (← moduleNameOfFileName file none)
  /- From the enviroment, we create a state of the `Command` monad. -/
  let commandState := {Command.mkState env1 messages {} with infoState.enabled := true}
  /- We create a state of the `Frontend` monad-/
  /- Runs the `processCommands` function on the context defined by `inputCtx`, and the
  state defined by `frontendState`. -/
  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
     { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }
  /- Note that for us, each `infoState.trees` is actually of length 1. -/
  for t in traverseForest file steps do
    try t
    catch e =>
      println! "caught top level: {e}"
  pure ()


/--  Recursively finds files in directory. -/
partial def addModulesIn (recurse : Bool) (prev : Array FilePath) (root : Name := .anonymous)
    (path : FilePath) : IO (Array FilePath) := do
  let mut r := prev
  let rootStr := root.toString.replace "." "/"
  for entry in ← path.readDir do
    if ← entry.path.isDir then
      if recurse then
        r ← addModulesIn recurse r (root.mkStr entry.fileName) entry.path
    else
      r := r.push (rootStr ++ "/" ++ entry.fileName)
  pure r

/-- Compute imports expected by `HepLean.lean` by looking at file structure. -/
def allFilePaths : IO (Array FilePath) := do
  let mut needed := #[]
  for top in ← FilePath.readDir "HepLean" do
    let nm := `HepLean
    let rootname := FilePath.withExtension top.fileName ""
    let root :=  nm.mkStr rootname.toString
    if ← top.path.isDir then
      needed ← addModulesIn (recurse := true) needed (root := root) top.path
    else
      needed := needed
  pure needed

/- See conversation here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E -/
unsafe def processAllFiles : IO Unit := do
  let files ← allFilePaths
  let tasks := files.map fun f =>
    ((IO.asTask $ IO.Process.run
    {cmd := "lake", args := #["exe", "check_rfl", f.toString]}), f)
  tasks.toList.enum.forM fun (n, (t, path)) => do
    println! "{n} of {tasks.toList.length}: {path}"
    let tn ← IO.wait (← t)
    match tn with
    | .ok x => println! x
    | .error _ => println! "Error"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [path] => checkRfl path
  | _ => processAllFiles
