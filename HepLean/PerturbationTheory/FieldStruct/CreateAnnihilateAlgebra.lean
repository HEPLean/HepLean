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

def ofStateList (φs : List 𝓕.States) : CrAnAlgebra 𝓕 :=  (List.map ofState φs).prod

@[simp]
lemma ofStateList_nil : ofStateList ([] : List 𝓕.States) = 1 := rfl

lemma ofStateList_cons (φ : 𝓕.States) (φs : List 𝓕.States) :
    ofStateList (φ :: φs) = ofState φ * ofStateList φs := rfl

lemma ofStateList_singleton (φ  :  𝓕.States) :
    ofStateList [φ] = ofState φ  := by
  simp [ofStateList]

lemma ofStateList_append (φs φs' : List 𝓕.States) :
    ofStateList (φs ++ φs') = ofStateList φs * ofStateList φs' := by
  dsimp [ofStateList]
  rw [List.map_append, List.prod_append]

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

## The super commutor on the creation and annihlation algebra.

-/

open FieldStatistic

noncomputable def superCommute :
   𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  Basis.constr ofCrAnListBasis ℂ fun φs' =>
  ofCrAnList (φs ++ φs') - pairedSign (𝓕 |>ₛ φs)
    (𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs)

scoped[FieldStruct.CrAnAlgebra] notation "⟨" φs "," φs' "⟩ₛca" => superCommute φs φs'

lemma superCommute_ofCrAnList (φs φs' : List 𝓕.CrAnStates) : ⟨ofCrAnList φs, ofCrAnList φs'⟩ₛca =
    ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommute, Basis.constr_basis]

lemma superCommute_ofCrAnList_ofStatesList (φcas : List 𝓕.CrAnStates) (φs : List 𝓕.States) :
    ⟨ofCrAnList φcas, ofStateList φs⟩ₛca = ofCrAnList φcas * ofStateList φs -
    pairedSign (𝓕 |>ₛ φcas)
    (FieldStatistic.ofList 𝓕.statesStatistic φs) • ofStateList φs * ofCrAnList φcas := by
  conv_lhs => rw [ofStateList_sum]
  rw [map_sum]
  conv_lhs =>
    enter [2, x]
    rw [superCommute_ofCrAnList, CreateAnnihilateSect.statistics_eq_state_statistics,
      ofCrAnList_append, ofCrAnList_append]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.smul_sum,
    ← Finset.sum_mul, ← ofStateList_sum]
  simp

lemma superCommute_ofStateList_ofStatesList (φ : List 𝓕.States) (φs : List 𝓕.States) :
    ⟨ofStateList φ, ofStateList φs⟩ₛca = ofStateList φ * ofStateList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs * ofStateList φ := by
  conv_lhs => rw [ofStateList_sum]
  simp
  conv_lhs =>
    enter [2, x]
    rw [superCommute_ofCrAnList_ofStatesList]
  simp [CreateAnnihilateSect.statistics_eq_state_statistics]
  rw [← Finset.sum_mul, ← Finset.smul_sum, ← Finset.mul_sum, ← ofStateList_sum]

lemma superCommute_ofState_ofStatesList (φ :  𝓕.States) (φs : List 𝓕.States) :
    ⟨ofState φ, ofStateList φs⟩ₛca = ofState φ * ofStateList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs * ofState φ := by
  rw [← ofStateList_singleton, superCommute_ofStateList_ofStatesList, ofStateList_singleton]
  simp

lemma superCommute_ofStateList_ofStates (φs :  List 𝓕.States) (φ : 𝓕.States) :
    ⟨ofStateList φs, ofState φ⟩ₛca = ofStateList φs * ofState φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ofStateList φs := by
  rw [← ofStateList_singleton, superCommute_ofStateList_ofStatesList, ofStateList_singleton]
  simp

lemma ofCrAnList_mul_ofCrAnList_eq_superCommute (φs φs' : List 𝓕.CrAnStates) :
    ofCrAnList φs * ofCrAnList φs' = pairedSign (𝓕 |>ₛ φs)
    (𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnList φs
    + ⟨ofCrAnList φs, ofCrAnList φs'⟩ₛca := by
  rw [superCommute_ofCrAnList]
  simp [ofCrAnList_append]

lemma ofCrAnState_mul_ofCrAnList_eq_superCommute (φ : 𝓕.CrAnStates) (φs' : List 𝓕.CrAnStates) :
    ofCrAnState φ *  ofCrAnList φs' = pairedSign ( 𝓕.crAnStatistics φ)
    (𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnState φ
    + ⟨ofCrAnState φ, ofCrAnList φs'⟩ₛca := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp

lemma ofStateList_mul_ofStateList_eq_superCommute (φs φs' : List 𝓕.States) :
    ofStateList φs * ofStateList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofStateList φs' * ofStateList φs
    + ⟨ofStateList φs, ofStateList φs'⟩ₛca := by
  rw [superCommute_ofStateList_ofStatesList]
  simp

lemma ofState_mul_ofStateList_eq_superCommute (φ : 𝓕.States) (φs' : List 𝓕.States) :
    ofState φ * ofStateList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofStateList φs' * ofState φ
    + ⟨ofState φ, ofStateList φs'⟩ₛca := by
  rw [superCommute_ofState_ofStatesList]
  simp

lemma ofStateList_mul_ofState_eq_superCommute (φs : List 𝓕.States) (φ : 𝓕.States) :
    ofStateList φs * ofState φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ofStateList φs
    + ⟨ofStateList φs, ofState φ⟩ₛca := by
  rw [superCommute_ofStateList_ofStates]
  simp


lemma superCommute_anPart_crPart (φ φ' : 𝓕.States) :
    ⟨anPart (StateAlgebra.ofState φ), crPart (StateAlgebra.ofState φ')⟩ₛca =
    anPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ') -
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    crPart (StateAlgebra.ofState φ') * anPart (StateAlgebra.ofState φ) := by
  match φ, φ'  with
  | States.negAsymp φ, _ =>
    simp
  | _, States.posAsymp φ =>
    simp
  | States.position φ, States.position φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.posAsymp φ, States.position φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.negAsymp φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.posAsymp φ, States.negAsymp φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_crPart_anPart (φ φ' : 𝓕.States) :
    ⟨crPart (StateAlgebra.ofState φ), anPart (StateAlgebra.ofState φ')⟩ₛca =
    crPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') -
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    anPart (StateAlgebra.ofState φ') * crPart (StateAlgebra.ofState φ) := by
    match φ, φ' with
    | States.posAsymp φ, _ =>
    simp
    | _, States.negAsymp φ =>
    simp
    | States.position φ, States.position φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.position φ, States.posAsymp φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.negAsymp φ, States.position φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.negAsymp φ, States.posAsymp φ' =>
    simp
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_crPart_crPart (φ φ' : 𝓕.States) :
    ⟨crPart (StateAlgebra.ofState φ), crPart (StateAlgebra.ofState φ')⟩ₛca =
    crPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ') -
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    crPart (StateAlgebra.ofState φ') * crPart (StateAlgebra.ofState φ) := by
  match φ, φ' with
  | States.posAsymp φ, _ =>
  simp
  | _, States.posAsymp φ =>
  simp
  | States.position φ, States.position φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.negAsymp φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.negAsymp φ, States.position φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.negAsymp φ, States.negAsymp φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_anPart_anPart (φ φ' : 𝓕.States) :
    ⟨anPart (StateAlgebra.ofState φ), anPart (StateAlgebra.ofState φ')⟩ₛca =
    anPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') -
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    anPart (StateAlgebra.ofState φ') * anPart (StateAlgebra.ofState φ) := by
  match φ, φ' with
  | States.negAsymp φ, _ =>
  simp
  | _, States.negAsymp φ =>
  simp
  | States.position φ, States.position φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.posAsymp φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.posAsymp φ, States.position φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.posAsymp φ, States.posAsymp φ' =>
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]

lemma crPart_anPart_eq_superCommute (φ φ' : 𝓕.States) :
    crPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') =
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    anPart (StateAlgebra.ofState φ') * crPart (StateAlgebra.ofState φ) +
    ⟨crPart (StateAlgebra.ofState φ), anPart (StateAlgebra.ofState φ')⟩ₛca  := by
  rw [superCommute_crPart_anPart]
  simp

lemma anPart_crPart_eq_superCommute (φ φ' : 𝓕.States) :
    anPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ') =
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    crPart (StateAlgebra.ofState φ') * anPart (StateAlgebra.ofState φ) +
    ⟨anPart (StateAlgebra.ofState φ), crPart (StateAlgebra.ofState φ')⟩ₛca  := by
  rw [superCommute_anPart_crPart]
  simp

lemma crPart_crPart_eq_superCommute (φ φ' : 𝓕.States) :
    crPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ') =
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    crPart (StateAlgebra.ofState φ') * crPart (StateAlgebra.ofState φ) +
    ⟨crPart (StateAlgebra.ofState φ), crPart (StateAlgebra.ofState φ')⟩ₛca  := by
  rw [superCommute_crPart_crPart]
  simp

lemma anPart_anPart_eq_superCommute (φ φ' : 𝓕.States) :
    anPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') =
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    anPart (StateAlgebra.ofState φ') * anPart (StateAlgebra.ofState φ) +
    ⟨anPart (StateAlgebra.ofState φ), anPart (StateAlgebra.ofState φ')⟩ₛca  := by
  rw [superCommute_anPart_anPart]
  simp

lemma superCommute_crPart_ofStatesList (φ : 𝓕.States) (φs : List 𝓕.States) :
    ⟨crPart (StateAlgebra.ofState φ), ofStateList φs⟩ₛca = crPart (StateAlgebra.ofState φ) * ofStateList φs -
    pairedSign (𝓕.statesStatistic φ)
    (FieldStatistic.ofList 𝓕.statesStatistic φs) • ofStateList φs * crPart (StateAlgebra.ofState φ) := by
  match φ with
  | States.negAsymp φ =>
    simp
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.position φ =>
    simp
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.posAsymp φ =>
    simp

lemma superCommute_anPart_ofStatesList (φ : 𝓕.States) (φs : List 𝓕.States) :
    ⟨anPart (StateAlgebra.ofState φ), ofStateList φs⟩ₛca = anPart (StateAlgebra.ofState φ) * ofStateList φs -
    pairedSign (𝓕.statesStatistic φ)
    (FieldStatistic.ofList 𝓕.statesStatistic φs) • ofStateList φs * anPart (StateAlgebra.ofState φ) := by
  match φ with
  | States.negAsymp φ =>
    simp
  | States.position φ =>
    simp
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.posAsymp φ =>
    simp
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]

lemma superCommute_crPart_ofState (φ φ' : 𝓕.States) :
    ⟨crPart (StateAlgebra.ofState φ), ofState φ'⟩ₛca = crPart (StateAlgebra.ofState φ) * ofState φ' -
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    ofState φ' * crPart (StateAlgebra.ofState φ) := by
  rw [← ofStateList_singleton, superCommute_crPart_ofStatesList]
  simp

lemma superCommute_anPart_ofState (φ φ' : 𝓕.States) :
    ⟨anPart (StateAlgebra.ofState φ), ofState φ'⟩ₛca = anPart (StateAlgebra.ofState φ) * ofState φ' -
    pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    ofState φ' * anPart (StateAlgebra.ofState φ) := by
  rw [← ofStateList_singleton, superCommute_anPart_ofStatesList]
  simp

lemma superCommute_ofCrAnState (φ φ' :  𝓕.CrAnStates) : ⟨ofCrAnState φ, ofCrAnState φ'⟩ₛca =
    ofCrAnState φ * ofCrAnState φ'  - pairedSign (𝓕.crAnStatistics φ)
    (𝓕.crAnStatistics φ') • ofCrAnState φ' * ofCrAnState φ := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [superCommute_ofCrAnList, ofCrAnList_append]
  congr
  rw [ofCrAnList_append]
  rw [FieldStatistic.ofList_singleton, FieldStatistic.ofList_singleton, smul_mul_assoc]

lemma superCommute_ofCrAnList_symm (φs φs' : List 𝓕.CrAnStates) :
    ⟨ofCrAnList φs, ofCrAnList φs'⟩ₛca =
    (- pairedSign (𝓕 |>ₛ φs) (𝓕 |>ₛ φs')) •
    ⟨ofCrAnList φs', ofCrAnList φs⟩ₛca := by
  rw [superCommute_ofCrAnList, superCommute_ofCrAnList]
  rw [smul_sub]
  simp
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [pairedSign_symm, pairedSign_mul_self]
  simp
  abel

lemma superCommute_ofCrAnState_symm (φ φ' :  𝓕.CrAnStates) :
    ⟨ofCrAnState φ, ofCrAnState φ'⟩ₛca =
    (- pairedSign (𝓕.crAnStatistics φ) (𝓕.crAnStatistics φ')) •
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

lemma superCommute_ofCrAnList_ofCrAnList_cons (φ : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    ⟨ofCrAnList φs, ofCrAnList (φ :: φs')⟩ₛca =
    ⟨ofCrAnList φs, ofCrAnState φ⟩ₛca * ofCrAnList φs' +
    pairedSign (𝓕 |>ₛ φs) (𝓕.crAnStatistics φ)
    • ofCrAnState φ * ⟨ofCrAnList φs, ofCrAnList φs'⟩ₛca := by
  rw [superCommute_ofCrAnList]
  conv_rhs =>
    lhs
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList, sub_mul, ← ofCrAnList_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofCrAnList_append, ofCrAnList_singleton, smul_mul_assoc,
      mul_assoc, ← ofCrAnList_append]
  conv_rhs =>
    rhs
    rw [superCommute_ofCrAnList, mul_sub, smul_mul_assoc]
  simp only [instCommGroup.eq_1, List.cons_append, List.append_assoc, List.nil_append,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sub_add_sub_cancel, sub_right_inj]
  rw [← ofCrAnList_cons, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp only [instCommGroup, map_mul, mul_comm]

lemma superCommute_ofCrAnList_ofStateList_cons  (φ : 𝓕.States) (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : ⟨ofCrAnList φs, ofStateList (φ :: φs')⟩ₛca =
    ⟨ofCrAnList φs, ofState φ⟩ₛca * ofStateList φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ⟨ofCrAnList φs, ofStateList φs'⟩ₛca := by
  rw [superCommute_ofCrAnList_ofStatesList]
  conv_rhs =>
    lhs
    rw [← ofStateList_singleton, superCommute_ofCrAnList_ofStatesList, sub_mul, mul_assoc,
      ← ofStateList_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofStateList_singleton, smul_mul_assoc,
      smul_mul_assoc, mul_assoc]
  conv_rhs =>
    rhs
    rw [superCommute_ofCrAnList_ofStatesList, mul_sub, smul_mul_assoc]
  simp
  rw [ofStateList_cons, mul_assoc, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp [mul_comm]

lemma ofCrAnList_mul_ofStateList_eq_superCommute (φs : List 𝓕.CrAnStates) (φs' : List 𝓕.States) :
    ofCrAnList φs * ofStateList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofStateList φs' * ofCrAnList φs
    + ⟨ofCrAnList φs, ofStateList φs'⟩ₛca := by
  rw [superCommute_ofCrAnList_ofStatesList]
  simp

lemma superCommute_ofCrAnList_ofCrAnList_eq_sum (φs  : List 𝓕.CrAnStates) :
    (φs' : List 𝓕.CrAnStates) →
    ⟨ofCrAnList φs, ofCrAnList φs'⟩ₛca =
    ∑ (n : Fin φs'.length), pairedSign (𝓕 |>ₛ φs)
    (𝓕 |>ₛ (List.take n φs')) •
    ofCrAnList (φs'.take n) * ⟨ofCrAnList φs, ofCrAnState (φs'.get n)⟩ₛca *
    ofCrAnList (φs'.drop (n + 1))
  | [] => by
    simp [← ofCrAnList_nil, superCommute_ofCrAnList]
  | φ :: φs' => by
    rw [superCommute_ofCrAnList_ofCrAnList_cons, superCommute_ofCrAnList_ofCrAnList_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofCrAnList_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]

lemma superCommute_ofCrAnList_ofStateList_eq_sum (φs  : List 𝓕.CrAnStates) :
    (φs' : List 𝓕.States) →
    ⟨ofCrAnList φs, ofStateList φs'⟩ₛca =
    ∑ (n : Fin φs'.length), pairedSign (𝓕 |>ₛ φs)
      (FieldStatistic.ofList 𝓕.statesStatistic (List.take n φs')) •
      ofStateList (φs'.take n) * ⟨ofCrAnList φs, ofState (φs'.get n)⟩ₛca *
      ofStateList (φs'.drop (n + 1))
  | [] => by
    simp only [superCommute_ofCrAnList_ofStatesList, instCommGroup, ofList_empty,
      pairedSign_bosonic, one_smul, List.length_nil, Finset.univ_eq_empty, List.take_nil,
      List.get_eq_getElem, List.drop_nil, Finset.sum_empty]
    simp
  | φ :: φs' => by
    rw [superCommute_ofCrAnList_ofStateList_cons, superCommute_ofCrAnList_ofStateList_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofStateList_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]


end CrAnAlgebra

end FieldStruct
