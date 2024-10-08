/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import Lean.Elab.Term
/-!

## Elaboration of tensor trees

This file turns tensor expressions into tensor trees.

-/
open Lean
open Lean.Elab.Term

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term
open Lean Meta Elab Tactic

/-!

## Indexies

-/

/-- A syntax category for indices of tensor expressions. -/
declare_syntax_cat indexExpr

/-- A basic index is a ident. -/
syntax ident : indexExpr

/-- An index can be a num, which will be used to evaluate the tensor. -/
syntax num : indexExpr

/-- Notation to discribe the jiggle of a tensor index. -/
syntax "τ(" ident ")" : indexExpr

/-- Bool which is ture if an index is a num. -/
def indexExprIsNum (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|$_:num) => true
  | _ => false

/-- If an index is a num - the undelrying natural number. -/
def indexToNum (stx : Syntax) : TermElabM Nat :=
  match stx with
  | `(indexExpr|$a:num) =>
    match a.raw.isNatLit? with
    | some n => return n
    | none => throwError "Expected a natural number literal."
  | _ =>
    throwError "Unsupported tensor expression syntax in indexToNum: {stx}"

/-- When an index is not a num, the corresponding ident. -/
def indexToIdent (stx : Syntax) : TermElabM Ident :=
  match stx with
  | `(indexExpr|$a:ident) => return a
  | `(indexExpr| τ($a:ident)) => return a
  | _ =>
    throwError "Unsupported tensor expression syntax in indexToIdent: {stx}"

/-- Takes a pair ``a b : ℕ × TSyntax `indexExpr``. If `a.1 < b.1` and `a.2 = b.2` then
  outputs `some (a.1, b.1)`, otherwise `none`. -/
def indexPosEq (a b : ℕ × TSyntax `indexExpr) : TermElabM (Option (ℕ × ℕ)) := do
  let a' ← indexToIdent a.2
  let b' ← indexToIdent b.2
  if a.1 < b.1 ∧ Lean.TSyntax.getId a' = Lean.TSyntax.getId b' then
    return some (a.1, b.1)
  else
    return none

/-- Bool which is true if an index is of the form τ(i) that is, to be dualed. -/
def indexToDual (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr| τ($_)) => true
  | _ => false
/-!

## Tensor expressions

-/

/-- A syntax category for tensor expressions. -/
declare_syntax_cat tensorExpr

/-- The syntax for a tensor node. -/
syntax term "|" (ppSpace indexExpr)* : tensorExpr

/-- The syntax for tensor prod two tensor nodes. -/
syntax tensorExpr "⊗" tensorExpr : tensorExpr

/-- Allowing brackets to be used in a tensor expression. -/
syntax "(" tensorExpr ")" : tensorExpr

/-!

## For tensor nodes.

The operations are done in the following order:
- evaluation.
- dualization.
- contraction.
-/

namespace TensorNode

/-- The indices of a tensor node. Before contraction, dualisation, and evaluation. -/
partial def getIndicesNode (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      let indices ← args.toList.mapM fun arg => do
        match arg with
        | `(indexExpr|$t:indexExpr) => pure t
      return indices
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesNode: {stx}"

/-- The positions in getIndicesNode which get evaluated, and the value they take. -/
partial def getEvalPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndicesNode stx
  let indEnum := ind.enum
  let evals := indEnum.filter (fun x => indexExprIsNum x.2)
  let evals2 ← (evals.mapM (fun x => indexToNum x.2))
  return List.zip (evals.map (fun x => x.1)) evals2

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.eval` to the given term. -/
def evalSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x1, x2) => Syntax.mkApp (mkIdent ``TensorTree.eval)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x2), T']) T

/-- The positions in getIndicesNode which get dualized. -/
partial def getDualPos (stx : Syntax) : TermElabM (List ℕ) := do
  let ind ← getIndicesNode stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  let indEnum := indFilt.enum
  let duals := indEnum.filter (fun x => indexToDual x.2)
  return duals.map (fun x => x.1)

/-- For each element of `l : List ℕ` applies `TensorTree.jiggle` to the given term. -/
def dualSyntax (l : List ℕ) (T : Term) : Term :=
  l.foldl (fun T' x => Syntax.mkApp (mkIdent ``TensorTree.jiggle)
    #[Syntax.mkNumLit (toString x), T']) T

/-- The pairs of positions in getIndicesNode which get contracted. -/
partial def getContrPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndicesNode stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  let indEnum := indFilt.enum
  let bind := List.bind indEnum (fun a => indEnum.map (fun b => (a, b)))
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- The list of indices after contraction. -/
def withoutContr (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  let ind ← getIndicesNode stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return ind.filter (fun x => indFilt.count x ≤ 1)

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.contr` to the given term. -/
def contrSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x0, x1) => Syntax.mkApp (mkIdent ``TensorTree.contr)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x0), T']) T

/-- An elaborator for tensor nodes. This is to be generalized. -/
def elaborateTensorNode (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(tensorExpr| $T:term | $[$args]*) => do
      let tensorNodeSyntax := Syntax.mkApp (mkIdent ``TensorTree.tensorNode) #[T]
      let evalSyntax := evalSyntax (← getEvalPos stx) tensorNodeSyntax
      let dualSyntax := dualSyntax (← getDualPos stx) evalSyntax
      let contrSyntax := contrSyntax (← getContrPos stx) dualSyntax
      let tensorExpr ← elabTerm contrSyntax none
      return tensorExpr
  | _ =>
    throwError "Unsupported tensor expression syntax in elaborateTensorNode: {stx}"

/-- Syntax turning a tensor expression into a term. -/
syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

end TensorNode
