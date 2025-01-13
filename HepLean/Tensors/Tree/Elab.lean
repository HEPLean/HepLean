/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.ComplexTensor.Basic
/-!

# Elaboration of tensor trees

- Syntax in Lean allows us to represent tensor expressions in a way close to what we expect to
  see on pen-and-paper.
- The elaborator turns this syntax into a tensor tree.

## Examples

- Suppose `T` and `T'` are tensors `S.F (OverColor.mk ![c1, c2])`.
- `{T | μ ν}ᵀ` is `tensorNode T`.
- We can also write e.g. `{T | μ ν}ᵀ.tensor` to get the tensor itself.
- `{- T | μ ν}ᵀ` is `neg (tensorNode T)`.
- `{T | 0 ν}ᵀ` is `eval 0 0 (tensorNode T)`.
- `{T | μ ν + T' | μ ν}ᵀ` is `addNode (tensorNode T) (perm _ (tensorNode T'))`, where
  here `_` will be the identity permutation so does nothing.
- `{T | μ ν = T' | μ ν}ᵀ` is `(tensorNode T).tensor = (perm _ (tensorNode T')).tensor`.
- If `a ∈ S.k` then `{a •ₜ T | μ ν}ᵀ` is `smulNode a (tensorNode T)`.
- If `g ∈ S.G` then `{g •ₐ T | μ ν}ᵀ` is `actionNode g (tensorNode T)`.
- Suppose `T2` is a tensor `S.F (OverColor.mk ![c3])`.
  Then `{T | μ ν ⊗ T2 | σ}ᵀ` is `prodNode (tensorNode T1) (tensorNode T2)`.
- If `T3` is a tensor `S.F (OverColor.mk ![S.τ c1, S.τ c2])`, then
  `{T | μ ν ⊗ T3 | μ σ}ᵀ` is `contr 0 1 _ (prodNode (tensorNode T1) (tensorNode T3))`.
  `{T | μ ν ⊗ T3 | μ ν }ᵀ` is
  `contr 0 0 _ (contr 0 1 _ (prodNode (tensorNode T1) (tensorNode T3)))`.
- If `T4` is a tensor `S.F (OverColor.mk ![c2, c1])` then
  `{T | μ ν + T4 | ν μ }ᵀ`is `addNode (tensorNode T) (perm _ (tensorNode T4))` where `_`
  is the permutation of the two indices of `T4`.
  `{T | μ ν = T4 | ν μ }ᵀ` is `(tensorNode T).tensor = (perm _ (tensorNode T4)).tensor` is the
  permutation of the two indices of `T4`.

## Comments

- In all of theses expressions `μ`, `ν` etc are free. It does not matter what they are called,
  Lean will elaborate them in the same way. I.e. `{T | μ ν ⊗ T3 | μ ν }ᵀ` is exactly the same
  to Lean as `{T | α β ⊗ T3 | α β }ᵀ`.
- Note that compared to ordinary index notation, we do not rise or lower the indices.
  This is for two reasons: 1) It is difficult to make this general for all tensor species,
  2) It is a redundancy in ordinary index notation, since the tensor `T` itself already tells you
  this information.

-/
open Lean
open Lean.Elab.Term

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term
open Lean Meta Elab Tactic
open IndexNotation
open complexLorentzTensor
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

/-- Notation to describe the jiggle of a tensor index. -/
syntax "τ(" ident ")" : indexExpr

/-- Bool which is ture if an index is a num. -/
def indexExprIsNum (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|$_:num) => true
  | _ => false

/-- If an index is a num - the underlying natural number. -/
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
syntax term "•ₜ" tensorExpr : tensorExpr

/-- group action for tensors. -/
syntax term "•ₐ" tensorExpr : tensorExpr

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
      | Expr.forallE _ (Expr.app _ a) _ _ =>
        let a' ← whnf a
        match a' with
        | Expr.lit (Literal.natVal n) => return n
        |_ => throwError s!"Could not extract number of indices from tensor
          {stx} (getNoIndicesExact). "
      | _ => throwError s!"Could not extract number of indices from tensor
        {stx} (getNoIndicesExact). "
    | _ => return 1
  | k => return k

/-- The construction of an expression corresponding to the type of a given string once parsed. -/
def stringToType (str : String) : TermElabM (Option Expr) := do
  let env ← getEnv
  let stx := Parser.runParserCategory env `term str
  match stx with
  | Except.error _ => return none
  | Except.ok stx => return (some (← elabTerm stx none))

/-- The construction of an expression corresponding to the type of a given string once parsed. -/
def stringToTerm (str : String) : TermElabM Term := do
  let env ← getEnv
  let stx := Parser.runParserCategory env `term str
  match stx with
  | Except.error _ => throwError "Could not create type from string (stringToTerm). "
  | Except.ok stx =>
    match stx with
    | `(term| $e) => return e

/-- Specific types of tensors which appear which we want to elaborate in specific ways. -/
def specialTypes : List (String × (Term → Term)) := [
  ("CoeSort.coe Lorentz.complexCo", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.vecNodeE) #[mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.down, T]),
  ("CoeSort.coe Lorentz.complexContr", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.vecNodeE) #[mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.up, T]),
  ("ModuleCat.carrier (Lorentz.complexContr ⊗ Lorentz.complexCo).V", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.twoNodeE) #[mkIdent ``complexLorentzTensor,
        mkIdent ``complexLorentzTensor.Color.up, mkIdent ``complexLorentzTensor.Color.down, T]),
  ("ModuleCat.carrier (Lorentz.complexContr ⊗ Lorentz.complexContr).V", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.twoNodeE) #[mkIdent ``complexLorentzTensor,
        mkIdent ``complexLorentzTensor.Color.up, mkIdent ``complexLorentzTensor.Color.up, T]),
  ("ModuleCat.carrier (Lorentz.complexCo ⊗ Lorentz.complexCo).V", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.twoNodeE) #[mkIdent ``complexLorentzTensor,
        mkIdent ``complexLorentzTensor.Color.down, mkIdent ``complexLorentzTensor.Color.down, T]),
  ("ModuleCat.carrier (Lorentz.complexCo ⊗ Lorentz.complexContr).V", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.twoNodeE) #[
        mkIdent ``complexLorentzTensor,
        mkIdent ``complexLorentzTensor.Color.down,
        mkIdent ``complexLorentzTensor.Color.up, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Lorentz.complexCo ⊗ Lorentz.complexCo", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
      mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.down,
      mkIdent ``complexLorentzTensor.Color.down, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Lorentz.complexContr ⊗ Lorentz.complexContr", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
      mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.up,
      mkIdent ``complexLorentzTensor.Color.up, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Lorentz.complexContr ⊗ Fermion.leftHanded ⊗ Fermion.rightHanded", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constThreeNodeE) #[
      mkIdent ``complexLorentzTensor, mkIdent ``complexLorentzTensor.Color.up,
      mkIdent ``complexLorentzTensor.Color.upL,
      mkIdent ``complexLorentzTensor.Color.upR, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Fermion.leftHanded ⊗ Fermion.leftHanded", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
      mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.upL,
      mkIdent ``complexLorentzTensor.Color.upL, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Fermion.altLeftHanded ⊗ Fermion.altLeftHanded", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
      mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.downL,
      mkIdent ``complexLorentzTensor.Color.downL, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Fermion.altRightHanded ⊗ Fermion.altRightHanded", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
      mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.downR,
      mkIdent ``complexLorentzTensor.Color.downR, T]),
  ("𝟙_ (Rep ℂ SL(2, ℂ)) ⟶ Fermion.rightHanded ⊗ Fermion.rightHanded", fun T =>
    Syntax.mkApp (mkIdent ``TensorTree.constTwoNodeE) #[
      mkIdent ``complexLorentzTensor,
      mkIdent ``complexLorentzTensor.Color.upR,
      mkIdent ``complexLorentzTensor.Color.upR, T])]

/-- The syntax associated with a terminal node of a tensor tree. -/
def termNodeSyntax (T : Term) : TermElabM Term := do
  let expr ← elabTerm T none
  let type ← inferType expr
  let defEqList ← specialTypes.filterM (fun x => do
    let type' ← stringToType x.1
    match type' with
    | none => return false
    | some type' =>
    let defEq ← isDefEq type type'
    return defEq)
  match defEqList with
  | [(_, f)] =>
    return f T
  | _ =>
  match type with
  | Expr.app _ (Expr.app _ (Expr.app _ _)) =>
      return Syntax.mkApp (mkIdent ``TensorTree.tensorNode) #[T]
  | _ => return Syntax.mkApp (mkIdent ``TensorTree.vecNode) #[T]

/-- Adjusts a list `List ℕ` by subtracting from each natural number the number
  of elements before it in the list which are less then itself. This is used
  to form a list of pairs which can be used for evaluating indices. -/
def evalAdjustPos (l : List ℕ) : List ℕ :=
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
  let pos := evalAdjustPos (evals.map (fun x => x.1))
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
  let bind := List.flatMap indEnum (fun a => indEnum.map (fun b => (a, b)))
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- The list of indices after contraction or evaluation. -/
def withoutContr (ind : List (TSyntax `indexExpr)) : TermElabM (List (TSyntax `indexExpr)) := do
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return indFilt.filter (fun x => indFilt.count x ≤ 1)

end TensorNode

/-- Takes a list and puts consecutive elements into pairs.
  e.g. [0, 1, 2, 3] becomes [(0, 1), (2, 3)]. -/
def toPairs (l : List ℕ) : List (ℕ × ℕ) :=
  match l with
  | x1 :: x2 :: xs => (x1, x2) :: toPairs xs
  | [] => []
  | [x] => [(x, 0)]

/-- Adjusts a list `List (ℕ × ℕ)` by subtracting from each natural number the number
  of elements before it in the list which are less then itself. This is used
  to form a list of pairs which can be used for contracting indices. -/
def contrListAdjust (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let l' := l.flatMap (fun p => [p.1, p.2])
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

namespace ProdNode

/-!

## For product nodes.

For a product node we can take the tensor product, and then contract the indices.

-/

/-- Gets the indices associated with a product node. -/
partial def getIndices (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      return (← TensorNode.withoutContr (← TensorNode.getIndices stx))
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let indicesA ← TensorNode.withoutContr (← getIndices a)
      let indicesB ← TensorNode.withoutContr (← getIndices b)
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
  let bind := List.flatMap indEnum (fun a => indEnum.map (fun b => (a, b)))
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- The list of indices after contraction. -/
def withoutContr (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  let ind ← getIndices stx
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return ind.filter (fun x => indFilt.count x ≤ 1)

/-- The syntax associated with a product of tensors. -/
def prodSyntax (T1 T2 : Term) : Term :=
  Syntax.mkApp (mkIdent ``TensorTree.prod) #[T1, T2]

end ProdNode

/-!

## Permutation constructions

-/
/-- Given two lists of indices returns the `List (ℕ)` representing the how one list
  permutes into the other. -/
def getPermutation (l1 l2 : List (TSyntax `indexExpr)) : TermElabM (List (ℕ)) := do
  let l1' ← l1.mapM (fun x => indexToIdent x)
  let l2' ← l2.mapM (fun x => indexToIdent x)
  let l1enum := l1'.enum
  let l2'' := l2'.filterMap
    (fun x => l1enum.find? (fun y => Lean.TSyntax.getId y.2 = Lean.TSyntax.getId x))
  return l2''.map fun x => x.1

open HepLean.Fin

/-- Given two lists of indices returns the permutation between them based on `finMapToEquiv`. -/
def getPermutationSyntax (l1 l2 : List (TSyntax `indexExpr)) : TermElabM Term := do
  let lPerm ← getPermutation l1 l2
  let l2Perm ← getPermutation l2 l1
  let permString := "![" ++ String.intercalate ", " (lPerm.map toString) ++ "]"
  let perm2String := "![" ++ String.intercalate ", " (l2Perm.map toString) ++ "]"
  let P1 ← TensorNode.stringToTerm permString
  let P2 ← TensorNode.stringToTerm perm2String
  let stx := Syntax.mkApp (mkIdent ``finMapToEquiv) #[P1, P2]
  return stx

namespace negNode

/-- The syntax associated with a product of tensors. -/
def negSyntax (T1 : Term) : Term :=
  Syntax.mkApp (mkIdent ``TensorTree.neg) #[T1]

end negNode

/-- Returns the full list of indices after contraction. TODO: Include evaluation. -/
partial def getIndicesFull (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      return (← TensorNode.withoutContr (← TensorNode.getIndices stx))
  | `(tensorExpr| $_:tensorExpr ⊗ $_:tensorExpr) => do
      return (← ProdNode.withoutContr stx)
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← getIndicesFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return (← getIndicesFull a)
  | `(tensorExpr| $_:term •ₜ $a) => do
      return (← getIndicesFull a)
  | `(tensorExpr| $a:tensorExpr + $_:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesProd: {stx}"

namespace SMul

/-- The syntax associated with the scalar multiplication of tensors. -/
def smulSyntax (c T : Term) : Term :=
  Syntax.mkApp (mkIdent ``TensorTree.smul) #[c, T]

end SMul

namespace Action

/-- The syntax associated with the group action of tensors. -/
def actionSyntax (c T : Term) : Term :=
  Syntax.mkApp (mkIdent ``TensorTree.action) #[c, T]

end Action

namespace Add

/-- Gets the indices associated with the LHS of an addition. -/
partial def getIndicesLeft (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $a:tensorExpr + $_:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in Add.getIndicesLeft: {stx}"

/-- Gets the indices associated with the RHS of an addition. -/
partial def getIndicesRight (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:tensorExpr + $a:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in Add.getIndicesRight: {stx}"

/-- The syntax for a equality of tensor trees. -/
def addSyntax (permSyntax : Term) (T1 T2 : Term) : TermElabM Term := do
  let P := Syntax.mkApp (mkIdent ``OverColor.equivToHomEq) #[permSyntax]
  let RHS := Syntax.mkApp (mkIdent ``TensorTree.perm) #[P, T2]
  return Syntax.mkApp (mkIdent ``add) #[T1, RHS]

end Add

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

/-- The syntax for a equality of tensor trees. -/
def equalSyntax (permSyntax : Term) (T1 T2 : Term) : TermElabM Term := do
  let X1 := Syntax.mkApp (mkIdent ``TensorTree.tensor) #[T1]
  let P := Syntax.mkApp (mkIdent ``OverColor.equivToHomEq) #[permSyntax]
  let X2' := Syntax.mkApp (mkIdent ``TensorTree.perm) #[P, T2]
  let X2 := Syntax.mkApp (mkIdent ``TensorTree.tensor) #[X2']
  return Syntax.mkApp (mkIdent ``Eq) #[X1, X2]

end Equality

/-- Creates the syntax associated with a tensor node. -/
partial def syntaxFull (stx : Syntax) : TermElabM Term := do
  match stx with
  | `(tensorExpr| $T:term | $[$args]*) =>
      let indices ← TensorNode.getIndices stx
      let rawIndex ← TensorNode.getNoIndicesExact T
      if indices.length ≠ rawIndex then
        throwError "The expected number of indices {rawIndex} does not match the tensor {T}."
      let tensorNodeSyntax ← TensorNode.termNodeSyntax T
      let evalSyntax := TensorNode.evalSyntax (← TensorNode.getEvalPos stx) tensorNodeSyntax
      let contrSyntax := contrSyntax (← TensorNode.getContrPos stx) evalSyntax
      return contrSyntax
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let prodSyntax := ProdNode.prodSyntax (← syntaxFull a) (← syntaxFull b)
      let contrSyntax := contrSyntax (← ProdNode.getContrPos stx) prodSyntax
      return contrSyntax
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← syntaxFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return negNode.negSyntax (← syntaxFull a)
  | `(tensorExpr| $c:term •ₜ $a:tensorExpr) => do
      return SMul.smulSyntax c (← syntaxFull a)
  | `(tensorExpr| $c:term •ₐ $a:tensorExpr) => do
      return Action.actionSyntax c (← syntaxFull a)
  | `(tensorExpr| $a + $b) => do
      let indicesLeft ← Add.getIndicesLeft stx
      let indicesRight ← Add.getIndicesRight stx
      let permSyntax ← getPermutationSyntax indicesLeft indicesRight
      let addSyntax ← Add.addSyntax permSyntax (← syntaxFull a) (← syntaxFull b)
      return addSyntax
  | `(tensorExpr| $a:tensorExpr = $b:tensorExpr) => do
      let indicesLeft ← Equality.getIndicesLeft stx
      let indicesRight ← Equality.getIndicesRight stx
      let permSyntax ← getPermutationSyntax indicesLeft indicesRight
      let equalSyntax ← Equality.equalSyntax permSyntax (← syntaxFull a) (← syntaxFull b)
      return equalSyntax
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
/-!

## Test cases

-/

/-
variable {S : TensorSpecies} {c : Fin (Nat.succ (Nat.succ 0)) → S.C} {t : S.F.obj (OverColor.mk c)}

#check {t | α β}ᵀ
-/
end TensorTree
