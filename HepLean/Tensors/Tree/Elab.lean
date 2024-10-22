/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import Lean.Elab.Term
import HepLean.Tensors.Tree.Dot
import HepLean.Tensors.ComplexLorentz.Basic
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

namespace TensorTree

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

/-- Equality. -/
syntax:40 tensorExpr "=" tensorExpr:41 : tensorExpr

/-- The syntax for tensor prod two tensor nodes. -/
syntax:70 tensorExpr "⊗" tensorExpr:71 : tensorExpr

/-- The syntax for tensor addition. -/
syntax tensorExpr "+" tensorExpr : tensorExpr

/-- Allowing brackets to be used in a tensor expression. -/
syntax "(" tensorExpr ")" : tensorExpr

/-- Scalar multiplication for tensors. -/
syntax term "•" tensorExpr : tensorExpr

/-- Negation of a tensor tree. -/
syntax "-" tensorExpr : tensorExpr

namespace TensorNode

/-!

## For tensor nodes.

The operations are done in the following order:
- evaluation.
- dualization.
- contraction.

We also want to ensure the number of indices is correct.

-/

/-- The indices of a tensor node. Before contraction, and evaluation. -/
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
  let strType := toString type
  let n := (String.splitOn strType "CategoryTheory.MonoidalCategoryStruct.tensorObj").length
  match n with
  | 1 =>
    match type with
    | Expr.app _ (Expr.app _ (Expr.app _ c)) =>
      let typeC ← inferType c
      match typeC with
      | Expr.forallE _ (Expr.app _ (Expr.app (Expr.app _ (Expr.lit (Literal.natVal n))) _)) _ _ =>
        return n
      | _ => throwError "Could not extract number of indices from tensor (getNoIndicesExact). "
    | _ => return 1
  | k => return k

/-- The construction of an expression corresponding to the type of a given string once parsed. -/
def stringToType (str : String) : TermElabM Expr := do
  let env ← getEnv
  let stx := Parser.runParserCategory env `term str
  match stx with
  | Except.error _ => throwError "Could not create type from string (stringToType). "
  | Except.ok stx => elabTerm stx none

/-- The construction of an expression corresponding to the type of a given string once parsed. -/
def stringToTerm (str : String) : TermElabM Term := do
  let env ← getEnv
  let stx := Parser.runParserCategory env `term str
  match stx with
  | Except.error _ => throwError "Could not create type from string (stringToType). "
  | Except.ok stx =>
    match stx with
    | `(term| $e) => return e

/-- The syntax associated with a terminal node of a tensor tree. -/
def termNodeSyntax (T : Term) : TermElabM Term := do
  let expr ← elabTerm T none
  let type ← inferType expr
  let strType := toString type
  let n := (String.splitOn strType "CategoryTheory.MonoidalCategoryStruct.tensorObj").length
  let const := (String.splitOn strType "Quiver.Hom").length
  match ← isDefEq type (← stringToType "CoeSort.coe Lorentz.complexCo") with
  | true =>
    return Syntax.mkApp (mkIdent ``TensorTree.vecNodeE) #[mkIdent ``Fermion.complexLorentzTensor,
      mkIdent ``Fermion.Color.down, T]
  | _ =>
  match ← isDefEq type (← stringToType "CoeSort.coe Lorentz.complexContr") with
  | true =>
    return Syntax.mkApp (mkIdent ``TensorTree.vecNodeE) #[mkIdent ``Fermion.complexLorentzTensor,
      mkIdent ``Fermion.Color.up, T]
  | _ =>
  match n, const with
  | 1, 1 =>
    match type with
    | Expr.app _ (Expr.app _ (Expr.app _ c)) =>
      let typeC ← inferType c
      match typeC with
      | Expr.forallE _ (Expr.app _ (Expr.app (Expr.app _ (Expr.lit (Literal.natVal _))) _)) _ _ =>
        return Syntax.mkApp (mkIdent ``TensorTree.tensorNode) #[T]
      | _ => throwError "Could not create terminal node syntax (termNodeSyntax). "
    | _ => return Syntax.mkApp (mkIdent ``TensorTree.vecNode) #[T]
  | 2, 1 =>
    match ← isDefEq type (← stringToType
      "CoeSort.coe leftHanded ⊗ CoeSort.coe Lorentz.complexContr") with
    | true => return Syntax.mkApp (mkIdent ``TensorTree.twoNodeE)
                #[mkIdent ``Fermion.complexLorentzTensor,
                mkIdent ``Fermion.Color.upL, mkIdent ``Fermion.Color.up, T]
    | _ =>
    match ← isDefEq type (← stringToType "ModuleCat.carrier
      (Lorentz.complexContr ⊗ Lorentz.complexContr).V") with
    | true =>
      return Syntax.mkApp (mkIdent ``TensorTree.twoNodeE) #[mkIdent ``Fermion.complexLorentzTensor,
        mkIdent ``Fermion.Color.up, mkIdent ``Fermion.Color.up, T]
    | _ =>
    match ← isDefEq type (← stringToType "ModuleCat.carrier
      (Lorentz.complexCo ⊗ Lorentz.complexCo).V") with
    | true =>
      return Syntax.mkApp (mkIdent ``TensorTree.twoNodeE) #[mkIdent ``Fermion.complexLorentzTensor,
        mkIdent ``Fermion.Color.down, mkIdent ``Fermion.Color.down, T]
    | _ =>
      return Syntax.mkApp (mkIdent ``TensorTree.twoNode) #[T]
  | 3, 1 => return Syntax.mkApp (mkIdent ``TensorTree.threeNode) #[T]
  | 1, 2 => return Syntax.mkApp (mkIdent ``TensorTree.constVecNode) #[T]
  | 2, 2 =>
    match ← isDefEq type (← stringToType
      "𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Lorentz.complexCo ⊗ Lorentz.complexCo") with
    | true =>
      return Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
        mkIdent ``Fermion.complexLorentzTensor, mkIdent ``Fermion.Color.down,
        mkIdent ``Fermion.Color.down, T]
    | _ => return Syntax.mkApp (mkIdent ``TensorTree.constTwoNode) #[T]
  | 3, 2 =>
    /- Specific types. -/
    match ← isDefEq type (← stringToType
      "𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Lorentz.complexContr ⊗ Fermion.leftHanded ⊗ Fermion.rightHanded") with
    | true =>
      return Syntax.mkApp (mkIdent ``TensorTree.constThreeNodeE) #[
        mkIdent ``Fermion.complexLorentzTensor, mkIdent ``Fermion.Color.up,
        mkIdent ``Fermion.Color.upL, mkIdent ``Fermion.Color.upR, T]
    | _ =>
      return Syntax.mkApp (mkIdent ``TensorTree.constThreeNode) #[T]
  | _, _ => throwError "Could not create terminal node syntax (termNodeSyntax). "

/-- Adjusts a list `List ℕ` by subtracting from each natrual number the number
  of elements before it in the list which are less then itself. This is used
  to form a list of pairs which can be used for evaluating indices. -/
def evalAdjustPos (l : List ℕ) : List ℕ  :=
  let l' := List.mapAccumr
    (fun x (prev : List ℕ) =>
      let e := prev.countP (fun y => y < x)
      (x :: prev, x - e)) l.reverse []
  l'.2.reverse

/-- The positions in getIndicesNode which get evaluated, and the value they take. -/
partial def getEvalPos (stx : Syntax) : TermElabM (List (ℕ × ℕ)) := do
  let ind ← getIndices stx
  let indEnum := ind.enum
  let evals := indEnum.filter (fun x => indexExprIsNum x.2)
  let evals2 ← (evals.mapM (fun x => indexToNum x.2))
  let pos :=  evalAdjustPos (evals.map (fun x => x.1))
  return List.zip pos evals2

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.eval` to the given term. -/
def evalSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x1, x2) => Syntax.mkApp (mkIdent ``TensorTree.eval)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x2), T']) T

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

/-- The list of indices after contraction or evaluation. -/
def withoutContr (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  let ind ← getIndices stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return indFilt.filter (fun x => indFilt.count x ≤ 1)

/-- Takes a list and puts conseutive elements into pairs.
  e.g. [0, 1, 2, 3] becomes [(0, 1), (2, 3)]. -/
def toPairs (l : List ℕ) : List (ℕ × ℕ) :=
  match l with
  | x1 :: x2 :: xs => (x1, x2) :: toPairs xs
  | [] => []
  | [x] => [(x, 0)]

/-- Adjusts a list `List (ℕ × ℕ)` by subtracting from each natrual number the number
  of elements before it in the list which are less then itself. This is used
  to form a list of pairs which can be used for contracting indices. -/
def contrListAdjust (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let l' := l.bind (fun p => [p.1, p.2])
  let l'' := List.mapAccumr
    (fun x (prev : List ℕ) =>
      let e := prev.countP (fun y => y < x)
      (x :: prev, x - e)) l'.reverse []
  toPairs l''.2.reverse

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.contr` to the given term. -/
def contrSyntax (l : List (ℕ × ℕ)) (T : Term) : Term :=
  (contrListAdjust l).foldl (fun T' (x0, x1) => Syntax.mkApp (mkIdent ``TensorTree.contr)
    #[Syntax.mkNumLit (toString x0),
    Syntax.mkNumLit (toString x1), mkIdent ``rfl, T']) T

/-- Creates the syntax associated with a tensor node. -/
def syntaxFull (stx : Syntax) : TermElabM Term := do
  match stx with
  | `(tensorExpr| $T:term | $[$args]*) => do
      let indices ← getIndices stx
      let rawIndex ← getNoIndicesExact T
      if indices.length ≠ rawIndex then
        throwError "The expected number of indices {rawIndex} does not match the tensor {T}."
      let tensorNodeSyntax ← termNodeSyntax T
      let evalSyntax := evalSyntax (← getEvalPos stx) tensorNodeSyntax
      let contrSyntax := contrSyntax (← getContrPos stx) evalSyntax
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
  (TensorNode.contrListAdjust l).foldl (fun T' (x0, x1) => Syntax.mkApp (mkIdent ``TensorTree.contr)
    #[Syntax.mkNumLit (toString x0), Syntax.mkNumLit (toString x1), mkIdent ``rfl, T']) T

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

end ProdNode

namespace negNode

/-- The syntax associated with a product of tensors. -/
def negSyntax (T1 : Term) : Term :=
  Syntax.mkApp (mkIdent ``TensorTree.neg) #[T1]

end negNode

/-- Returns the full list of indices after contraction. TODO: Include evaluation. -/
partial def getIndicesFull (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      return (← TensorNode.withoutContr stx)
  | `(tensorExpr| $_:tensorExpr ⊗ $_:tensorExpr) => do
      return (← ProdNode.withoutContr stx)
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← getIndicesFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesProd: {stx}"

namespace Equality

/-!

## For equality.

-/

/-- Gets the indices associated with the LHS of an equality. -/
partial def getIndicesLeft (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $a:tensorExpr = $_:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesProd: {stx}"

/-- Gets the indices associated with the RHS of an equality. -/
partial def getIndicesRight (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:tensorExpr = $a:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesProd: {stx}"

/-- Given two lists of indices returns the `List (ℕ)` representing the how one list
  permutes into the other. -/
def getPermutation (l1 l2 : List (TSyntax `indexExpr)) : TermElabM (List (ℕ)) := do
  let l1' ← l1.mapM (fun x => indexToIdent x)
  let l2' ← l2.mapM (fun x => indexToIdent x)
  let l1enum := l1'.enum
  let l2'' := l2'.filterMap
    (fun x => l1enum.find? (fun y => Lean.TSyntax.getId y.2 = Lean.TSyntax.getId x))
  return l2''.map fun x => x.1

/-- Takes two maps `Fin n → Fin n` and returns the equivelance they form. -/
def finMapToEquiv (f1 f2 : Fin n → Fin n) (h : ∀ x, f1 (f2 x) = x := by decide)
  (h' : ∀ x, f2 (f1 x) = x := by decide) : Fin n ≃ Fin n where
  toFun := f1
  invFun := f2
  left_inv := h'
  right_inv := h

/-- Given two lists of indices returns the permutation between them based on `finMapToEquiv`. -/
def getPermutationSyntax (l1 l2 : List (TSyntax `indexExpr)) : TermElabM Term := do
  let lPerm ← getPermutation l1 l2
  let l2Perm ← getPermutation l1 l2
  let permString := "![" ++ String.intercalate ", " (lPerm.map toString) ++ "]"
  let perm2String := "![" ++ String.intercalate ", " (l2Perm.map toString) ++ "]"
  let P1 ← TensorNode.stringToTerm permString
  let P2 ← TensorNode.stringToTerm perm2String
  let stx := Syntax.mkApp (mkIdent ``finMapToEquiv) #[P1, P2]
  return stx

/-- The syntax for a equality of tensor trees. -/
def equalSyntax (permSyntax : Term) (T1 T2 : Term) : TermElabM Term := do
  let X1 := Syntax.mkApp (mkIdent ``TensorTree.tensor) #[T1]
  let P := Syntax.mkApp (mkIdent ``OverColor.equivToHomEq) #[permSyntax]
  let X2' := Syntax.mkApp (mkIdent ``TensorTree.perm) #[P, T2]
  let X2 := Syntax.mkApp (mkIdent ``TensorTree.tensor) #[X2']
  return Syntax.mkApp (mkIdent ``Eq) #[X1, X2]

/-- Creates the syntax associated with a tensor node. -/
partial def syntaxFull (stx : Syntax) : TermElabM Term := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) =>
    ProdNode.syntaxFull stx
  | `(tensorExpr| $_:tensorExpr ⊗ $_:tensorExpr) => do
      return ← ProdNode.syntaxFull stx
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← syntaxFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return negNode.negSyntax (← syntaxFull a)
  | `(tensorExpr| $a:tensorExpr = $b:tensorExpr) => do
      let indicesLeft ← getIndicesLeft stx
      let indicesRight ← getIndicesRight stx
      let permSyntax ← getPermutationSyntax indicesLeft indicesRight
      let equalSyntax ← equalSyntax permSyntax (← syntaxFull a) (← syntaxFull b)
      return equalSyntax
  | _ =>
    throwError "Unsupported tensor expression syntax in elaborateTensorNode: {stx}"

/-- An elaborator for tensor nodes. This is to be generalized. -/
def elaborateTensorNode (stx : Syntax) : TermElabM Expr := do
  println! "{(← syntaxFull stx)}"
  let tensorExpr ← elabTerm (← syntaxFull stx) none
  return tensorExpr

/-- Syntax turning a tensor expression into a term. -/
syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

variable {S : TensorSpecies} {c4 : Fin 4 → S.C} (T4 : S.F.obj (OverColor.mk c4))
  {c5 : Fin 5 → S.C} (T5 : S.F.obj (OverColor.mk c5)) (a : S.k)

variable (𝓣 : TensorTree S c4)

/-!

# Checks

-/

/-
#tensor_dot {T4 | i j τ(l) d ⊗ T5 | i j k m m}ᵀ.dot

#check {T4 | i j l d ⊗ T5 | i j k a b}ᵀ

#check {(T4 | i j l a ⊗ T5 | i j k c d) ⊗ T5 | i1 i2 i3 e f}ᵀ
-/
end Equality

end TensorTree
