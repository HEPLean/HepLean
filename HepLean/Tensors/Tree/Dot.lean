/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import Lean.Elab.Term
/-!

## Tensor trees to dot files

Dot files are used by graphviz to create visualizations of graphs. Here we define a function
that converts a tensor tree into a dot file.

-/

namespace TensorTree

/-- Turns a nodes of tensor trees into nodes and edges of a dot file. -/
def dotString (m : ℕ) (nt : ℕ) : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → String := fun
  | tensorNode _ =>
    " node" ++ toString m ++ " [label=\"T" ++ toString nt ++ "\"];\n"
  | vecNode T =>
    " node" ++ toString m ++ " [label=\"vec " ++ toString nt ++ "\"];\n"
  | twoNode T =>
    " node" ++ toString m ++ " [label=\"vec2\", shape=box];\n"
  | threeNode T =>
    " node" ++ toString m ++ " [label=\"vec3\", shape=box];\n"
  | constNode T =>
    " node" ++ toString m ++ " [label=\"const " ++ toString nt ++ "\"];\n"
  | constVecNode T =>
    " node" ++ toString m ++ " [label=\"constVec " ++ toString nt ++ "\"];\n"
  | constTwoNode T =>
    " node" ++ toString m ++ " [label=\"constVec2\", shape=box];\n"
  | constThreeNode T =>
    " node" ++ toString m ++ " [label=\"constVec3\", shape=box];\n"
  | add t1 t2 =>
    let addNode := " node" ++ toString m ++ " [label=\"+\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    let edge2 := " node" ++ toString m ++ " -> node" ++ toString (m + 2) ++ ";\n"
    addNode ++ dotString (m + 1) nt t1 ++ dotString (m + 2) (nt + 1) t2 ++ edge1 ++ edge2
  | perm σ t =>
    let permNode := " node" ++ toString m ++ " [label=\"perm\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    permNode ++ dotString (m + 1) nt t ++ edge1
  | prod t1 t2 =>
    let prodNode := " node" ++ toString m ++ " [label=\"⊗\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    let edge2 := " node" ++ toString m ++ " -> node" ++ toString (2 * t1.size + m + 2) ++ ";\n"
    prodNode ++ dotString (m + 1) nt t1 ++ dotString (2 * t1.size + m + 2) (nt + 1) t2
      ++ edge1 ++ edge2
  | neg t =>
    let negNode := " node" ++ toString m ++ " [label=\"neg\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    negNode ++ dotString (m + 1) nt t ++ edge1
  | smul k t =>
    let smulNode := " node" ++ toString m ++ " [label=\"smul\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    smulNode ++ dotString (m + 1) nt t ++ edge1
  | eval _ _ t1 =>
    let evalNode := " node" ++ toString m ++ " [label=\"eval\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    evalNode ++ dotString (m + 1) nt t1 ++ edge1
  | contr i j _ t1 =>
    let contrNode := " node" ++ toString m ++ " [label=\"contr " ++ toString i ++ " "
      ++ toString j ++ "\", shape=box];\n"
    let edge1 := " node" ++ toString m ++ " -> node" ++ toString (m + 1) ++ ";\n"
    contrNode ++ dotString (m + 1) nt t1 ++ edge1

/-- Used to form a dot graph from a tensor tree. use e.g.
  `#tensor_dot {T4 | i j l d ⊗ T5 | i j k a b}ᵀ.dot`.
  Dot files can be viewed by copying and pasting into: https://dreampuf.github.io/GraphvizOnline. -/
def dot {n : ℕ} {c : Fin n → S.C} (t : TensorTree S c) : String :=
  "// Dot file created by HepLean for a tensor expression.
// Can be viewed at https://dreampuf.github.io/GraphvizOnline/\n" ++
  "digraph G {\n" ++ dotString 0 0 t ++ "}"

section dotElab

open Lean.Elab.Command Lean Meta Lean.Elab

/-- Syntax for showing the dot file associated with a tensor tree.
  Use as `#tensor_dot {T4 | i j l d ⊗ T5 | i j k a b}ᵀ.dot`. -/
syntax (name := tensorDot) "#tensor_dot " term : command

/-- Adapted from `Lean.Elab.Command.elabReduce` in file copyright Microsoft Corporation. -/
unsafe def dotElab (term : Syntax) : CommandElabM Unit :=
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    withTheReader Core.Context (fun ctx =>
      { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <|
        reduce e (skipProofs := true) (skipTypes := true)
      let str ← Lean.Meta.evalExpr' String ``String e
      println! str

/-- Elaborator for the syntax tensorDot. -/
@[command_elab tensorDot]
unsafe def elabTensorDot: CommandElab
  | `(#tensor_dot $term) => dotElab term
  | _ => throwUnsupportedSyntax

end dotElab

end TensorTree
