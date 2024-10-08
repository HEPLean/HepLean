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

declare_syntax_cat indexExpr

syntax ident : indexExpr

syntax num : indexExpr

syntax "τ(" ident ")" : indexExpr

def indexExprIsNum (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|$_:num) => true
  | _ => false

def indexToNum (stx : Syntax) : TermElabM Nat :=
  match stx with
  | `(indexExpr|$a:num) =>
    match a.raw.isNatLit? with
    | some n => return n
    | none   => throwError "Expected a natural number literal."
  | _ =>
    throwError "Unsupported tensor expression syntax (indexToNum): {stx}"

def indexToIdent (stx : Syntax) : TermElabM Ident :=
  match stx with
  | `(indexExpr|$a:ident) => return a
  | `(indexExpr| τ($a:ident)) => return a
  | _ =>
    throwError "Unsupported tensor expression syntax (indexToIdent): {stx}"

def indexPosEq (a b : ℕ × TSyntax `indexExpr) : TermElabM (Option (ℕ × ℕ)) := do
  let a' ← indexToIdent a.2
  let b' ← indexToIdent b.2
  if a.1 < b.1 ∧ Lean.TSyntax.getId a' = Lean.TSyntax.getId b' then
    return some (a.1, b.1)
  else
    return none

def indexToDual (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr| τ($_)) => true
  | _ => false
/-!

## Tensor expressions

-/
declare_syntax_cat tensorExpr

syntax term "|" (ppSpace indexExpr)* : tensorExpr

syntax tensorExpr "⊗" tensorExpr : tensorExpr

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
    throwError "Unsupported tensor expression syntax (getIndicesNode): {stx}"

/-- The positions in getIndicesNode which get evaluated, and the value they take. -/
partial def getEvalPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndicesNode stx
  let indEnum := ind.enum
  let evals := indEnum.filter (fun x => indexExprIsNum x.2)
  let evals2 ← (evals.mapM (fun x => indexToNum x.2))
  return List.zip (evals.map (fun x => x.1)) evals2

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

def dualSyntax (l : List ℕ) (T : Term) : Term :=
  l.foldl (fun T' x => Syntax.mkApp (mkIdent ``TensorTree.jiggle)
    #[Syntax.mkNumLit (toString x), T']) T

partial def getContrPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndicesNode stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  let indEnum := indFilt.enum
  let bind := List.bind indEnum (fun a => indEnum.map (fun b => (a, b)))
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧  (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

def withoutContr (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  let ind ← getIndicesNode stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return ind.filter (fun x => indFilt.count x ≤ 1)

def contrSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x0, x1) => Syntax.mkApp (mkIdent ``TensorTree.contr)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x0), T']) T

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
    throwError "Unsupported tensor expression syntax (elaborateTensorNode): {stx}"

syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

end TensorNode
