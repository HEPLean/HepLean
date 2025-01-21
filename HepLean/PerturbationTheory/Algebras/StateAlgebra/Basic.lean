/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.CreateAnnihilate
/-!

# State algebra

We define the state algebra of a field structure to be the free algebra
generated by the states.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-- The state free-algebra.
  The free algebra generated by `States`,
  that is a position based states or assymptotic states.
  As a module `StateAlgebra` is spanned by lists of `States`. -/
abbrev StateAlgebra (𝓕 : FieldSpecification) : Type := FreeAlgebra ℂ 𝓕.States

namespace StateAlgebra

open FieldStatistic

/-- The element of the states free-algebra generated by a single state. -/
def ofState (φ : 𝓕.States) : StateAlgebra 𝓕 :=
  FreeAlgebra.ι ℂ φ

/-- The element of the states free-algebra generated by a list of states. -/
def ofList (φs : List 𝓕.States) : StateAlgebra 𝓕 :=
  (List.map ofState φs).prod

@[simp]
lemma ofList_nil : ofList ([] : List 𝓕.States) = 1 := rfl

lemma ofList_singleton (φ : 𝓕.States) : ofList [φ] = ofState φ := by
  simp [ofList]

lemma ofList_append (φs ψs : List 𝓕.States) :
    ofList (φs ++ ψs) = ofList φs * ofList ψs := by
  rw [ofList, List.map_append, List.prod_append]
  rfl

lemma ofList_cons (φ : 𝓕.States) (φs : List 𝓕.States) :
    ofList (φ :: φs) = ofState φ * ofList φs := rfl

/-- The basis of the free state algebra formed by lists of states. -/
noncomputable def ofListBasis : Basis (List 𝓕.States) ℂ 𝓕.StateAlgebra where
  repr := FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv

@[simp]
lemma ofListBasis_eq_ofList (φs : List 𝓕.States) :
    ofListBasis φs = ofList φs := by
  simp only [ofListBasis, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    Basis.coe_ofRepr, AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.ofAlgHom_symm_apply, ofList]
  erw [MonoidAlgebra.lift_apply]
  simp only [zero_smul, Finsupp.sum_single_index, one_smul]
  rw [@FreeMonoid.lift_apply]
  simp only [List.prod]
  match φs with
  | [] => rfl
  | φ :: φs =>
    erw [List.map_cons]

/-!

## The super commutor on the state algebra.

-/

/-- The super commutor on the free state algebra. For two bosonic operators
  or a bosonic and fermionic operator this corresponds to the usual commutator
  whilst for two fermionic operators this corresponds to the anti-commutator. -/
noncomputable def superCommute : 𝓕.StateAlgebra →ₗ[ℂ] 𝓕.StateAlgebra →ₗ[ℂ] 𝓕.StateAlgebra :=
  Basis.constr ofListBasis ℂ fun φs =>
  Basis.constr ofListBasis ℂ fun φs' =>
  ofList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofList (φs' ++ φs)

local notation "⟨" φs "," φs' "⟩ₛ" => superCommute φs φs'

lemma superCommute_ofList (φs φs' : List 𝓕.States) : ⟨ofList φs, ofList φs'⟩ₛ =
    ofList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofList (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommute, Basis.constr_basis]

end StateAlgebra

end FieldSpecification
