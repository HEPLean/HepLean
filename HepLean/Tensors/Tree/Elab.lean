/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import Lean.Elab.Term
/-!

## Elaboration of tensor trees

This file turns

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

def indexToDual (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr| τ($_)) => true
  | _ => false
/-!

## Tensor expressions

-/
declare_syntax_cat tensorExpr

syntax term (ppSpace indexExpr)* : tensorExpr

syntax tensorExpr "⊗" tensorExpr : tensorExpr

syntax "(" tensorExpr ")" : tensorExpr

/-!

## For tensor nodes.

-/

partial def getIndicesNode (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:ident $[$args]*) => do
      let indices ← args.toList.mapM fun arg => do
        match arg with
        | `(indexExpr|$t:indexExpr) => pure t
      return indices
  | _ =>
    throwError "Unsupported tensor expression syntax: {stx}"

partial def getEvalPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndicesNode stx
  let indEnum := ind.enum

  let evals := indEnum.filter (fun x => indexExprIsNum x.2)
  println! "indEnum: {evals}"
  let evals2 ← (evals.mapM (fun x => indexToNum x.2))
  return List.zip (evals.map (fun x => x.1)) evals2

partial def getDualPos (stx : Syntax) : TermElabM (List ℕ) := do
  let ind ← getIndicesNode stx
  let indEnum := ind.enum
  let duals := indEnum.filter (fun x => indexToDual x.2)
  return duals.map (fun x => x.1)

syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term -- Pattern 1: Identifier with terms


def elaborateTensorNode (stx : Syntax) : TermElabM Expr := do
  let ind ← getIndicesNode stx
  let evalPos ← getEvalPos stx
  let dualPos ← getDualPos stx
  match stx with
  | `(tensorExpr| $T:ident $[$args]*) => do
      let tensor ← elabTerm T none
      return tensor
  | _ =>
    throwError "Unsupported tensor expression syntax: {stx}"

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

open IndexNotation

example {S : TensorStruct} {n : ℕ} {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    {T i j}ᵀ = T := by
  sorry
#eval do
  let stx ← `(tensorExpr| T τ(i) τ(k) 0)
  let indices ← getIndicesNode stx
  let evalPos ← getEvalPos stx
  let dualPos ← getDualPos stx
  IO.println s!"Indices: {indices},\nEval positions: {evalPos}\nDual positions: {dualPos}"

partial def dropEvalNode (stx : Syntax)  : TermElabM (List (TSyntax `ident)) := do
  let ind ← getIndicesNode stx
  let indIndent := ind.filter (fun x => ¬ indexExprIsNum x)

partial def getContrPairsNode (stx : Syntax) : TermElabM (Array (ℕ × ℕ)) := do
  let ind ← getIndicesNode stx
  let mut pairs : Array (ℕ × ℕ) := #[]
  for i in [:ind.length] do
    for j in [i+1:ind.length] do
      if Option.map Lean.TSyntax.getId (ind.get? i) = Option.map Lean.TSyntax.getId (ind.get? j) then
        pairs := pairs.push (i, j)
  /- Check on pairs. -/
  let x := pairs.toList
  if ¬ ((x.map Prod.fst).Nodup ∧  (x.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return pairs

def getContrIndicesNode (stx : Syntax) : TermElabM (List (TSyntax `ident)) := do
  let ind ← getIndicesNode stx
  let contrInd := ind.filter (fun x => ind.count x ≤ 1)
  return contrInd

partial def getIndicesProd (stx : Syntax) : TermElabM (List (TSyntax `ident)) := do
  match stx with
  | `(tensorExpr| $_:ident $[$args]*) => do
      getContrIndicesNode stx
  | `(tensorExpr| $e1:tensorExpr ⊗ $e2:tensorExpr) => do
      let ind1 ← getIndicesProd e1
      let ind2 ←  getIndicesProd e2
      return ind1 ++ ind2
  | `(tensorExpr| ($e:tensorExpr)) => do
      getIndicesProd e
  | _ =>
    throwError "Unsupported tensor expression syntax: {stx}"

def getContrIndices (stx : Syntax) : TermElabM (List (TSyntax `ident)) := do
  let ind ← getIndicesProd stx
  let contrInd := ind.filter (fun x => ind.count x ≤ 1)
  return contrInd

def getContrPairsProd (stx : Syntax) : TermElabM (Array (ℕ × ℕ)) := do
  let ind ← getIndicesProd stx
  let mut pairs : Array (ℕ × ℕ) := #[]
  for i in [:ind.length] do
    for j in [i+1:ind.length] do
      if Option.map Lean.TSyntax.getId (ind.get? i) = Option.map Lean.TSyntax.getId (ind.get? j) then
        pairs := pairs.push (i, j)
  /- Check on pairs. -/
  let x := pairs.toList
  if ¬ ((x.map Prod.fst).Nodup ∧  (x.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return pairs

/-! Some test cases. -/




#eval do
  let stx ← `(tensorExpr| (T i ⊗ B i i j ⊗ C k))
  let indices ← getIndicesProd stx
  let contrPairs ← getContrPairsProd stx
  let contrInd ← getContrIndices stx
  IO.println s!"Indices: {indices}\nContraction pairs: {contrPairs}\n Contraction list: {contrInd}"

variable (f : Fin 1 → Fin 4)
