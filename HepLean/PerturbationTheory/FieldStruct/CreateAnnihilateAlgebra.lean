/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Basic
import HepLean.PerturbationTheory.FieldStruct.StateAlgebra
import HepLean.PerturbationTheory.FieldStruct.CreateAnnihilateSect
/-!

# Creation and annihlation algebra

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

abbrev CrAnAlgebra (𝓕 : FieldStruct) : Type := FreeAlgebra ℂ 𝓕.CrAnStates

namespace CrAnAlgebra

open StateAlgebra

def ofCrAnState (φ : 𝓕.CrAnStates) : CrAnAlgebra 𝓕 :=
  FreeAlgebra.ι ℂ φ

def ofCrAnList  (φs : List 𝓕.CrAnStates) :  CrAnAlgebra 𝓕 := (List.map ofCrAnState φs).prod

@[simp]
lemma ofCrAnList_nil : ofCrAnList ([] : List 𝓕.CrAnStates) = 1 := rfl

lemma ofCrAnList_cons (φ : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates) :
    ofCrAnList (φ :: φs) = ofCrAnState φ * ofCrAnList φs := rfl

lemma ofCrAnList_append (φs φs' : List 𝓕.CrAnStates) :
    ofCrAnList (φs ++ φs') = ofCrAnList φs * ofCrAnList φs' := by
  dsimp [ofCrAnList]
  rw [List.map_append, List.prod_append]

lemma ofCrAnList_singleton (φ : 𝓕.CrAnStates) :
    ofCrAnList [φ] = ofCrAnState φ := by
  simp [ofCrAnList]

def ofState (φ : 𝓕.States) : CrAnAlgebra 𝓕 :=
  ∑ (i : 𝓕.statesToCrAnType φ), ofCrAnState ⟨φ, i⟩

def ofStateAlgebra : StateAlgebra 𝓕 →ₐ[ℂ] CrAnAlgebra 𝓕 :=
  FreeAlgebra.lift ℂ ofState

@[simp]
lemma ofStateAlgebra_ofState (φ : 𝓕.States) :
    ofStateAlgebra (StateAlgebra.ofState φ) = ofState φ := by
  simp [ofStateAlgebra, StateAlgebra.ofState]

def ofStateList : (φs : List 𝓕.States) → CrAnAlgebra 𝓕
  | [] => 1
  | φ :: φs => ofState φ * ofStateList φs

@[simp]
lemma ofStateList_nil : ofStateList ([] : List 𝓕.States) = 1 := rfl

lemma ofStateList_cons (φ : 𝓕.States) (φs : List 𝓕.States) :
    ofStateList (φ :: φs) = ofState φ * ofStateList φs := rfl

lemma ofStateAlgebra_ofList_eq_ofStateList : (φs : List 𝓕.States) →
    ofStateAlgebra (ofList φs) = ofStateList φs
  | [] => by
    simp [ofStateList]
  | φ :: φs => by
    rw [ofStateList_cons, StateAlgebra.ofList_cons]
    rw [map_mul]
    simp only [ofStateAlgebra_ofState, mul_eq_mul_left_iff]
    apply Or.inl (ofStateAlgebra_ofList_eq_ofStateList φs)

lemma ofStateList_sum (φs : List 𝓕.States) :
    ofStateList φs = ∑ (s : CreateAnnihilateSect φs), ofCrAnList s.1 := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
    rw [CreateAnnihilateSect.sum_cons]
    dsimp [CreateAnnihilateSect.cons, ofCrAnList_cons]
    conv_rhs =>
      enter [2, x]
      rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ofStateList_cons, ← ih]
    rfl

def crPart  : 𝓕.StateAlgebra →ₐ[ℂ] 𝓕.CrAnAlgebra :=
  FreeAlgebra.lift ℂ fun φ =>
  match φ with
  | States.negAsymp φ => ofCrAnState ⟨States.negAsymp φ, ()⟩
  | States.position φ => ofCrAnState ⟨States.position φ, CreateAnnihilate.create⟩
  | States.posAsymp _ => 0

@[simp]
lemma crPart_negAsymp (φ : 𝓕.AsymptoticNegTime) :
    crPart (StateAlgebra.ofState (States.negAsymp φ)) = ofCrAnState ⟨States.negAsymp φ, ()⟩ := by
  dsimp [crPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma crPart_position (φ : 𝓕.PositionStates) :
    crPart (StateAlgebra.ofState (States.position φ)) =
    ofCrAnState ⟨States.position φ, CreateAnnihilate.create⟩ := by
  dsimp [crPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma crPart_posAsymp (φ : 𝓕.AsymptoticPosTime) :
    crPart (StateAlgebra.ofState (States.posAsymp φ)) = 0 := by
  dsimp [crPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]


def anPart  : 𝓕.StateAlgebra →ₐ[ℂ] 𝓕.CrAnAlgebra :=
  FreeAlgebra.lift ℂ fun φ =>
  match φ with
  | States.negAsymp _ => 0
  | States.position φ => ofCrAnState ⟨States.position φ, CreateAnnihilate.annihilate⟩
  | States.posAsymp φ => ofCrAnState ⟨States.posAsymp φ, ()⟩

@[simp]
lemma anPart_negAsymp (φ : 𝓕.AsymptoticNegTime) :
    anPart (StateAlgebra.ofState (States.negAsymp φ)) = 0 := by
  dsimp [anPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma anPart_position (φ : 𝓕.PositionStates) :
    anPart (StateAlgebra.ofState (States.position φ)) =
    ofCrAnState ⟨States.position φ, CreateAnnihilate.annihilate⟩ := by
  dsimp [anPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma anPart_posAsymp (φ : 𝓕.AsymptoticPosTime) :
    anPart (StateAlgebra.ofState (States.posAsymp φ)) = ofCrAnState ⟨States.posAsymp φ, ()⟩ := by
  dsimp [anPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

lemma ofState_eq_crPart_add_anPart (φ : 𝓕.States) :
    ofState φ = crPart (StateAlgebra.ofState φ) + anPart (StateAlgebra.ofState φ) := by
  rw [ofState]
  cases φ with
  | negAsymp φ =>
    dsimp [statesToCrAnType]
    simp
  | position φ =>
    dsimp [statesToCrAnType]
    rw [CreateAnnihilate.sum_eq]
    simp
  | posAsymp φ =>
    dsimp [statesToCrAnType]
    simp

noncomputable def ofCrAnListBasis : Basis (List 𝓕.CrAnStates) ℂ (CrAnAlgebra 𝓕) where
  repr := FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv

@[simp]
lemma ofListBasis_eq_ofList (φs : List 𝓕.CrAnStates) :
    ofCrAnListBasis φs = ofCrAnList φs := by
  simp [ofCrAnListBasis, ofCrAnList, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  erw [MonoidAlgebra.lift_apply]
  simp
  rw [@FreeMonoid.lift_apply]
  simp [List.prod]
  match φs with
  | [] => rfl
  | φ :: φs =>
    erw [List.map_cons]

noncomputable def mulLinearMap  : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 where
  toFun a := {
    toFun := fun b => a * b,
    map_add' := fun c d => by
      simp [mul_add]
    map_smul' := by simp}
  map_add' := fun a b => by
    ext c
    simp [add_mul]
  map_smul' := by
    intros
    ext c
    simp [smul_mul']


lemma mulLinearMap_apply (a b : CrAnAlgebra 𝓕) :
    mulLinearMap a b = a * b := by rfl

noncomputable def smulLinearMap (c : ℂ) :  CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 where
  toFun a := c • a
  map_add' := by simp
  map_smul' m x := by
    simp [smul_smul]
    rw [NonUnitalNormedCommRing.mul_comm]


/-!

## The super commutor on the state algebra.

-/

open FieldStatistic

noncomputable def superCommute :
   𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  Basis.constr ofCrAnListBasis ℂ fun φs' =>
  ofCrAnList (φs ++ φs') - pairedSign (FieldStatistic.ofList 𝓕.crAnStatesStatistics φs)
    (FieldStatistic.ofList 𝓕.crAnStatesStatistics φs') • ofCrAnList (φs' ++ φs)

local notation "⟨" φs "," φs' "⟩ₛca" => superCommute φs φs'

lemma superCommute_ofCrAnList (φs φs' : List 𝓕.CrAnStates) : ⟨ofCrAnList φs, ofCrAnList φs'⟩ₛca =
    ofCrAnList (φs ++ φs') - pairedSign (FieldStatistic.ofList 𝓕.crAnStatesStatistics φs)
    (FieldStatistic.ofList 𝓕.crAnStatesStatistics φs') • ofCrAnList (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommute, Basis.constr_basis]


lemma superCommute_ofCrAnState (φ φ' :  𝓕.CrAnStates) : ⟨ofCrAnState φ, ofCrAnState φ'⟩ₛca =
    ofCrAnState φ * ofCrAnState φ'  - pairedSign (𝓕.crAnStatesStatistics φ)
    (𝓕.crAnStatesStatistics φ') • ofCrAnState φ' * ofCrAnState φ := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [superCommute_ofCrAnList, ofCrAnList_append]
  congr
  rw [ofCrAnList_append]
  rw [FieldStatistic.ofList_singleton, FieldStatistic.ofList_singleton, smul_mul_assoc]

lemma superCommute_ofCrAnState_symm (φ φ' :  𝓕.CrAnStates) :
    ⟨ofCrAnState φ, ofCrAnState φ'⟩ₛca =
    (- pairedSign (𝓕.crAnStatesStatistics φ) (𝓕.crAnStatesStatistics φ')) •
    ⟨ofCrAnState φ', ofCrAnState φ⟩ₛca := by
  rw [superCommute_ofCrAnState, superCommute_ofCrAnState]
  rw [smul_sub]
  simp
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [pairedSign_symm, pairedSign_mul_self]
  simp
  abel


end CrAnAlgebra

end FieldStruct
