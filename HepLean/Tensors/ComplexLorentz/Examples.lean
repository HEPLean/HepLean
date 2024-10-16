/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.ComplexLorentz.Basic
/-!

## The tensor structure for complex Lorentz tensors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory

noncomputable section

namespace Fermion

/-!

## Example tensor trees

-/
open MatrixGroups
open Matrix
example (v : Fermion.leftHanded) : TensorTree complexLorentzTensor ![Color.upL] :=
  {v | i}ᵀ

example (v : Fermion.leftHanded ⊗ Lorentz.complexContr) :
    TensorTree complexLorentzTensor ![Color.upL, Color.up] :=
  {v | i j}ᵀ

example :
    TensorTree complexLorentzTensor ![Color.downR, Color.downR] :=
  {Fermion.altRightMetric | μ j}ᵀ

lemma fin_three_expand {R : Type} (f : Fin 3 → R) : f = ![f 0, f 1, f 2]:= by
  funext x
  fin_cases x <;> rfl
/-
example : True :=
  let f :=
    {Lorentz.coMetric |
      μ ν ⊗ PauliMatrix.asConsTensor | μ α β ⊗ PauliMatrix.asConsTensor | ν α' β'}ᵀ
  sorry
-/
end Fermion

end
