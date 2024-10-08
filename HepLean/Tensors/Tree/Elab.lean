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
open IndexNotation

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

/-- The syntax for tensor addition. -/
syntax tensorExpr "+" tensorExpr : tensorExpr

/-- Allowing brackets to be used in a tensor expression. -/
syntax "(" tensorExpr ")" : tensorExpr

namespace TensorNode

/-!

## For tensor nodes.

The operations are done in the following order:
- evaluation.
- dualization.
- contraction.

We also want to ensure the number of indices is correct.

-/

/-- The indices of a tensor node. Before contraction, dualisation, and evaluation. -/
partial def getIndices (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      let indices ← args.toList.mapM fun arg => do
        match arg with
        | `(indexExpr|$t:indexExpr) => pure t
      return indices
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesNode: {stx}"

/-- Uses the structure of the tensor to get the number of indices. -/
def getNoIndicesExact (stx : Syntax) : TermElabM ℕ := do
  let expr ← elabTerm stx none
  let type ← inferType expr
  match type with
  | Expr.app _ (Expr.app _ (Expr.app _ c)) =>
    let typeC ← inferType c
    match typeC with
    | Expr.forallE _ (Expr.app _ (Expr.app (Expr.app _ (Expr.lit (Literal.natVal n))) _)) _ _ =>
      return n
    | _ => throwError "Could not extract number of indices from tensor (getNoIndicesExact). "
  | _ =>
    throwError "Could not extract number of indices from tensor (getNoIndicesExact)."

/-- The positions in getIndicesNode which get evaluated, and the value they take. -/
partial def getEvalPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndices stx
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
  let ind ← getIndices stx
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
  let ind ← getIndices stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  let indEnum := indFilt.enum
  let bind := List.bind indEnum (fun a => indEnum.map (fun b => (a, b)))
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- The list of indices after contraction. -/
def withoutContr (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  let ind ← getIndices stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return ind.filter (fun x => indFilt.count x ≤ 1)

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.contr` to the given term. -/
def contrSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x0, x1) => Syntax.mkApp (mkIdent ``TensorTree.contr)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x0), T']) T

/-- Creates the syntax associated with a tensor node. -/
def syntaxFull (stx : Syntax) : TermElabM Term := do
  match stx with
  | `(tensorExpr| $T:term | $[$args]*) => do
      let indices ← getIndices stx
      let rawIndex ← getNoIndicesExact T
      if indices.length ≠ rawIndex then
        throwError "The number of indices does not match the tensor {T}."
      let tensorNodeSyntax := Syntax.mkApp (mkIdent ``TensorTree.tensorNode) #[T]
      let evalSyntax := evalSyntax (← getEvalPos stx) tensorNodeSyntax
      let dualSyntax := dualSyntax (← getDualPos stx) evalSyntax
      let contrSyntax := contrSyntax (← getContrPos stx) dualSyntax
      return contrSyntax
  | _ =>
    throwError "Unsupported tensor expression syntax in elaborateTensorNode: {stx}"

end TensorNode

namespace ProdNode

/-!

## For product nodes.

For a product node we can take the tensor product, and then contract the indices.

-/

/-- Gets the indices associated with a product node. -/
partial def getIndices (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      return (← TensorNode.withoutContr stx)
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let indicesA ← getIndices a
      let indicesB ← getIndices b
      return indicesA ++ indicesB
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← getIndices a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesProd: {stx}"

/-- The pairs of positions in getIndicesNode which get contracted. -/
partial def getContrPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndices stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  let indEnum := indFilt.enum
  let bind := List.bind indEnum (fun a => indEnum.map (fun b => (a, b)))
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- The list of indices after contraction. -/
def withoutContr (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  let ind ← getIndices stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return ind.filter (fun x => indFilt.count x ≤ 1)

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.contr` to the given term. -/
def contrSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x0, x1) => Syntax.mkApp (mkIdent ``TensorTree.contr)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x0), T']) T

/-- The syntax associated with a product of tensors. -/
def prodSyntax (T1 T2 : Term) : Term :=
  Syntax.mkApp (mkIdent ``TensorTree.prod) #[T1, T2]

/-- The full term taking tensor syntax into a term for products and single tensor nodes. -/
partial def syntaxFull (stx : Syntax) : TermElabM Term := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => TensorNode.syntaxFull stx
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let prodSyntax := prodSyntax (← syntaxFull a) (← syntaxFull b)
      let contrSyntax := contrSyntax (← getContrPos stx) prodSyntax
      return contrSyntax
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← syntaxFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in elaborateTensorNode: {stx}"

/-- An elaborator for tensor nodes. This is to be generalized. -/
def elaborateTensorNode (stx : Syntax) : TermElabM Expr := do
  let tensorExpr ← elabTerm (← syntaxFull stx) none
  return tensorExpr

/-- Syntax turning a tensor expression into a term. -/
syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

variable {S : TensorStruct} {c4 : Fin 4 → S.C} (T4 : S.F.obj (OverColor.mk c4))
  {c5 : Fin 5 → S.C} (T5 : S.F.obj (OverColor.mk c5))

/-!

# Checks

-/
/-
example : {T4 | i j k m}ᵀ = TensorTree.tensorNode T4 := by rfl

#check {T4 | i j l d ⊗ T5 | i j k a b}ᵀ

#check {(T4 | i j l a ⊗ T5 | i j k c d) ⊗ T5 | i1 i2 i3 e f}ᵀ
-/
end ProdNode
