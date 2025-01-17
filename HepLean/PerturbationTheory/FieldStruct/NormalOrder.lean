/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.OperatorAlgebra
import HepLean.PerturbationTheory.Wick.Signs.KoszulSign
/-!

# Normal Ordering

The normal ordering puts all creation operators to the left and all annihilation operators to the
right. It acts on `CrAnStates` and defines a linear map from the `CrAnAlgebra` to itself.

The normal ordering satisfies a number of nice properties with relation to the operator
algebra 𝓞.A.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

/-- The normal ordering on creation and annihlation states. -/
def normalOrderProp : 𝓕.CrAnStates → 𝓕.CrAnStates → Prop :=
  fun a b => CreateAnnihilate.normalOrder (𝓕.crAnStatesToCreateAnnihilate a)
    (𝓕.crAnStatesToCreateAnnihilate b)

/-- Normal ordering is total. -/
instance : IsTotal 𝓕.CrAnStates 𝓕.normalOrderProp where
  total _ _ := total_of CreateAnnihilate.normalOrder _ _

/-- Normal ordering is transitive. -/
instance : IsTrans 𝓕.CrAnStates 𝓕.normalOrderProp where
  trans _ _ _ := fun h h' => IsTrans.trans (α := CreateAnnihilate) _ _ _ h h'

instance (φ φ' : 𝓕.CrAnStates) :  Decidable (normalOrderProp φ φ') :=
  CreateAnnihilate.instDecidableNormalOrder (𝓕.crAnStatesToCreateAnnihilate φ)
    (𝓕.crAnStatesToCreateAnnihilate φ')

/-!

## Normal order sign.

-/
def normalOrderSign (φs : List 𝓕.CrAnStates) : ℂ :=
  Wick.koszulSign 𝓕.crAnStatistics 𝓕.normalOrderProp φs

@[simp]
lemma normalOrderSign_mul_self (φs : List 𝓕.CrAnStates) :
    normalOrderSign φs * normalOrderSign φs = 1 := by
  simp [normalOrderSign, Wick.koszulSign, Wick.koszulSign_mul_self]

lemma koszulSignInsert_create  (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) : (φs : List 𝓕.CrAnStates) →
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φ φs = 1
  | [] => rfl
  | φ' :: φs => by
    dsimp [Wick.koszulSignInsert]
    rw [if_pos]
    · exact koszulSignInsert_create φ hφ φs
    · dsimp [normalOrderProp]
      rw [hφ]
      dsimp [CreateAnnihilate.normalOrder]

lemma normalOrderSign_cons_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φ :: φs) = normalOrderSign φs := by
  dsimp [normalOrderSign, Wick.koszulSign]
  rw [koszulSignInsert_create φ hφ φs]
  simp

@[simp]
lemma normalOrderSign_singleton (φ : 𝓕.CrAnStates) :
    normalOrderSign [φ] = 1 := by
  simp [normalOrderSign]

@[simp]
lemma normalOrderSign_nil :
    normalOrderSign (𝓕 := 𝓕) [] = 1 := by
  simp [normalOrderSign, Wick.koszulSign]

lemma koszulSignInsert_append_annihilate (φ' φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) →
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φ' (φs ++ [φ]) =
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φ' φs
  | [] => by
    simp [Wick.koszulSignInsert, normalOrderProp, hφ]
  | φ'' :: φs => by
    dsimp [Wick.koszulSignInsert]
    rw [koszulSignInsert_append_annihilate φ' φ hφ φs]

lemma normalOrderSign_append_annihlate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate)  :
    (φs : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ [φ]) = normalOrderSign φs
  | [] => by simp
  | φ' :: φs => by
    dsimp [normalOrderSign, Wick.koszulSign]
    have hi := normalOrderSign_append_annihlate φ hφ φs
    dsimp [normalOrderSign] at hi
    rw [hi, koszulSignInsert_append_annihilate φ' φ hφ φs]

lemma koszulSignInsert_annihilate_cons_create (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φa (φc :: φs)
    = FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) *
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φa φs := by
  rw [Wick.koszulSignInsert_cons]
  simp
  apply Or.inl
  rw [Wick.koszulSignCons, if_neg, FieldStatistic.pairedSign_symm, FieldStatistic.pairedSign_eq_if]
  rw [normalOrderProp, hφa, hφc]
  simp [CreateAnnihilate.normalOrder]

lemma normalOrderSign_swap_create_annihlate_fst (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φc :: φa :: φs) =
    FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) *
    normalOrderSign (φa :: φc :: φs) := by
  rw [normalOrderSign_cons_create φc hφc (φa :: φs)]
  conv_rhs =>
    rw [normalOrderSign]
    rw [Wick.koszulSign]
    rw [← normalOrderSign]
    rw [koszulSignInsert_annihilate_cons_create φc φa hφc hφa φs]
  rw [← mul_assoc, ← mul_assoc, FieldStatistic.pairedSign_mul_self]
  simp
  rw [normalOrderSign_cons_create φc hφc φs]
  rfl

lemma koszulSignInsert_swap (φ φc φa : 𝓕.CrAnStates)
    : (φs φs' : List 𝓕.CrAnStates) →
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φ (φs ++ φa :: φc :: φs')
    = Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderProp φ  (φs ++ φc :: φa :: φs') := by
  intro φs φs'
  apply Wick.koszulSignInsert_eq_perm
  refine List.Perm.append_left φs ?h.a
  exact List.Perm.swap φc φa φs'


lemma normalOrderSign_swap_create_annihlate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
     : (φs φs' : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ φc :: φa :: φs') =
    FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) *
    normalOrderSign (φs ++ φa :: φc :: φs')
  | [], φs' => by
    exact normalOrderSign_swap_create_annihlate_fst φc φa hφc hφa φs'
  | φ :: φs, φs' => by
    rw [normalOrderSign]
    dsimp [Wick.koszulSign]
    rw [← normalOrderSign]
    rw [normalOrderSign_swap_create_annihlate φc φa hφc hφa φs φs']
    rw [← mul_assoc, mul_comm _ (FieldStatistic.pairedSign _ _), mul_assoc]
    simp
    apply Or.inl
    conv_rhs =>
      rw [normalOrderSign]
      dsimp [Wick.koszulSign]
      rw [← normalOrderSign]
    simp
    apply Or.inl
    rw [koszulSignInsert_swap]


lemma normalOrderSign_swap_create_create_fst (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφc' : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.create)
    (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φc :: φc' :: φs) =
    normalOrderSign (φc' :: φc :: φs) := by
  rw [normalOrderSign_cons_create φc hφc, normalOrderSign_cons_create φc' hφc']
  rw [normalOrderSign_cons_create φc' hφc', normalOrderSign_cons_create φc hφc]

lemma normalOrderSign_swap_create_create (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφc' : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.create)
    :  (φs φs' : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ φc :: φc' :: φs') =
    normalOrderSign (φs ++ φc' :: φc :: φs')
  | [], φs' => by
    exact normalOrderSign_swap_create_create_fst φc φc' hφc hφc' φs'
  | φ :: φs, φs' => by
    rw [normalOrderSign]
    dsimp [Wick.koszulSign]
    rw [← normalOrderSign]
    rw [normalOrderSign_swap_create_create φc φc' hφc hφc']
    dsimp [normalOrderSign, Wick.koszulSign]
    rw [← normalOrderSign]
    simp
    apply Or.inl
    apply Wick.koszulSignInsert_eq_perm
    refine List.Perm.append_left φs ?h.h.a
    exact List.Perm.swap φc' φc φs'

lemma normalOrderSign_swap_annihilate_annihilate_fst (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕.crAnStatesToCreateAnnihilate φa' = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φa :: φa' :: φs) =
    normalOrderSign (φa' :: φa :: φs) := by
  rw [normalOrderSign, normalOrderSign]
  dsimp [Wick.koszulSign]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [Wick.koszulSignInsert_cons, Wick.koszulSignInsert_cons]
  rw [mul_assoc, mul_assoc]
  congr 1
  · dsimp [Wick.koszulSignCons]
    rw [if_pos, if_pos]
    · simp [normalOrderProp, hφa, hφa', CreateAnnihilate.normalOrder]
    · simp [normalOrderProp, hφa, hφa', CreateAnnihilate.normalOrder]
  · rw [NonUnitalNormedCommRing.mul_comm]

lemma normalOrderSign_swap_annihilate_annihilate (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕.crAnStatesToCreateAnnihilate φa' = CreateAnnihilate.annihilate)
    :  (φs φs' : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ φa :: φa' :: φs') =
    normalOrderSign (φs ++ φa' :: φa :: φs')
  | [], φs' => by
    exact normalOrderSign_swap_annihilate_annihilate_fst φa φa' hφa hφa' φs'
  | φ :: φs, φs' => by
    rw [normalOrderSign]
    dsimp [Wick.koszulSign]
    rw [← normalOrderSign]
    rw [normalOrderSign_swap_annihilate_annihilate φa φa' hφa hφa']
    dsimp [normalOrderSign, Wick.koszulSign]
    rw [← normalOrderSign]
    simp
    apply Or.inl
    apply Wick.koszulSignInsert_eq_perm
    refine List.Perm.append_left φs ?h.h.a
    exact List.Perm.swap φa' φa φs'
open FieldStatistic

/-!

## Normal order of lists

-/

def normalOrderList (φs : List 𝓕.CrAnStates) : List 𝓕.CrAnStates :=
  List.insertionSort 𝓕.normalOrderProp φs


@[simp]
lemma normalOrderList_nil : normalOrderList (𝓕 := 𝓕) [] = [] := by
  simp [normalOrderList]

@[simp]
lemma normalOrderList_statistics (φs : List 𝓕.CrAnStates) :
    (𝓕 |>ₛ (normalOrderList φs)) = 𝓕 |>ₛ φs := by
  simp [normalOrderList, List.insertionSort]

lemma orderedInsert_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) :
    (φs : List 𝓕.CrAnStates) → List.orderedInsert normalOrderProp φ φs = φ :: φs
  | [] => rfl
  | φ' :: φs => by
    dsimp [List.orderedInsert]
    rw [if_pos]
    dsimp [normalOrderProp]
    rw [hφ]
    dsimp [CreateAnnihilate.normalOrder]

lemma normalOrderList_cons_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    normalOrderList (φ :: φs) = φ :: normalOrderList φs := by
  simp [normalOrderList, List.insertionSort]
  rw [orderedInsert_create φ hφ]

lemma orderedInsert_append_annihilate (φ' φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) → List.orderedInsert normalOrderProp φ' (φs ++ [φ]) =
    List.orderedInsert normalOrderProp φ' φs ++ [φ]
  | [] => by
    simp [Wick.koszulSignInsert, normalOrderProp, hφ]
  | φ'' :: φs => by
    dsimp [List.orderedInsert]
    have hi := orderedInsert_append_annihilate φ' φ hφ φs
    rw [hi]
    split
    next h => simp_all only [List.cons_append]
    next h => simp_all only [List.cons_append]

lemma normalOrderList_append_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) →
    normalOrderList (φs ++ [φ]) = normalOrderList φs ++ [φ]
  | [] => by simp [normalOrderList]
  | φ' :: φs => by
    simp [normalOrderList, List.insertionSort]
    have hi := normalOrderList_append_annihilate φ hφ φs
    dsimp [normalOrderList] at hi
    rw [hi, orderedInsert_append_annihilate φ' φ hφ]

lemma normalOrder_swap_create_annihlate_fst (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    normalOrderList (φc :: φa :: φs) = normalOrderList (φa :: φc :: φs) := by
  rw [normalOrderList_cons_create φc hφc (φa :: φs)]
  conv_rhs =>
    rw [normalOrderList]
    rw [List.insertionSort]
  have hi := normalOrderList_cons_create φc hφc φs
  rw [normalOrderList] at hi
  rw [hi]
  dsimp
  split
  · rename_i h
    rw [normalOrderProp, hφa, hφc] at h
    dsimp [CreateAnnihilate.normalOrder] at h
  · rfl

lemma normalOrderList_swap_create_annihlate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate) :
    (φs φs' : List 𝓕.CrAnStates) →
    normalOrderList (φs ++ φc :: φa :: φs') = normalOrderList (φs ++ φa :: φc :: φs')
  | [], φs' => by
    exact normalOrder_swap_create_annihlate_fst φc φa hφc hφa φs'
  | φ :: φs, φs' => by
    dsimp [normalOrderList]
    have hi := normalOrderList_swap_create_annihlate φc φa hφc hφa φs φs'
    dsimp [normalOrderList] at hi
    rw [hi]

-- HepLean.List.insertionSortEquiv
def normalOrderEquiv {φs : List 𝓕.CrAnStates} : Fin φs.length ≃ Fin (normalOrderList φs).length :=
  HepLean.List.insertionSortEquiv 𝓕.normalOrderProp φs

lemma sum_normalOrderList_length {M : Type} [AddCommMonoid M]
    (φs : List 𝓕.CrAnStates) (f : Fin (normalOrderList φs).length → M) :
    ∑ (n : Fin (normalOrderList φs).length), f n =
    ∑ (n : Fin φs.length), f (normalOrderEquiv n) := by
  exact Eq.symm (Equiv.sum_comp normalOrderEquiv f)

@[simp]
lemma normalOrderList_get_normalOrderEquiv {φs : List 𝓕.CrAnStates} (n : Fin φs.length) :
    (normalOrderList φs)[(normalOrderEquiv n).val] = φs[n.val] := by
  change (normalOrderList φs).get (normalOrderEquiv n) = _
  simp only [normalOrderList, normalOrderEquiv]
  erw [← HepLean.List.insertionSortEquiv_get]
  simp

@[simp]
lemma normalOrderList_eraseIdx_normalOrderEquiv {φs : List 𝓕.CrAnStates} (n : Fin φs.length) :
    (normalOrderList φs).eraseIdx (normalOrderEquiv n).val =
    normalOrderList (φs.eraseIdx n.val) := by
  simp [normalOrderList, normalOrderEquiv]
  rw [HepLean.List.eraseIdx_insertionSort_fin]

lemma normalOrderSign_eraseIdx (φs : List 𝓕.CrAnStates) (n : Fin φs.length) :
    normalOrderSign (φs.eraseIdx n) = normalOrderSign φs *
    𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ (φs.take n)) *
    𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ ((normalOrderList φs).take (normalOrderEquiv n))) := by
  rw [normalOrderSign, Wick.koszulSign_eraseIdx, ← normalOrderSign]
  rfl

def createFilter (φs : List 𝓕.CrAnStates) : List 𝓕.CrAnStates :=
  List.filter (fun φ => 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) φs

lemma createFilter_cons_create {φ : 𝓕.CrAnStates}
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    createFilter (φ :: φs) = φ :: createFilter φs := by
  simp [createFilter]
  rw [List.filter_cons_of_pos]
  simp [hφ]

lemma createFilter_cons_annihilate {φ : 𝓕.CrAnStates}
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnStates) :
    createFilter (φ :: φs) = createFilter φs := by
  simp [createFilter]
  rw [List.filter_cons_of_neg]
  simp [hφ]

lemma createFilter_append (φs φs' : List 𝓕.CrAnStates) :
    createFilter (φs ++ φs') = createFilter φs ++ createFilter φs' := by
  rw [createFilter, List.filter_append]
  rfl

lemma createFilter_singleton_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) :
    createFilter [φ] = [φ] := by
  simp [createFilter, hφ]

lemma createFilter_singleton_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) :
    createFilter [φ] = [] := by
  simp [createFilter, hφ]

def annihilateFilter (φs : List 𝓕.CrAnStates) : List 𝓕.CrAnStates :=
  List.filter (fun φ => 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) φs

lemma annihilateFilter_cons_create {φ : 𝓕.CrAnStates}
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    annihilateFilter (φ :: φs) = annihilateFilter φs := by
  simp [annihilateFilter]
  rw [List.filter_cons_of_neg]
  simp [hφ]

lemma annihilateFilter_cons_annihilate {φ : 𝓕.CrAnStates}
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnStates) :
    annihilateFilter (φ :: φs) = φ :: annihilateFilter φs := by
  simp [annihilateFilter]
  rw [List.filter_cons_of_pos]
  simp [hφ]

lemma annihilateFilter_append (φs φs' : List 𝓕.CrAnStates) :
    annihilateFilter (φs ++ φs') = annihilateFilter φs ++ annihilateFilter φs' := by
  rw [annihilateFilter, List.filter_append]
  rfl

lemma annihilateFilter_singleton_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) :
    annihilateFilter [φ] = [] := by
  simp [annihilateFilter, hφ]

lemma annihilateFilter_singleton_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) :
    annihilateFilter [φ] = [φ] := by
  simp [annihilateFilter, hφ]

lemma orderedInsert_createFilter_append_annihilate  (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate)
     : (φs φs' : List 𝓕.CrAnStates) →
    List.orderedInsert normalOrderProp φ (createFilter φs ++ φs') =
    createFilter φs ++ List.orderedInsert normalOrderProp φ φs'
  | [], φs' => by simp [createFilter]
  | φ' :: φs, φs' => by
    rcases CreateAnnihilate.eq_create_or_annihilate (𝓕.crAnStatesToCreateAnnihilate φ') with hφ' | hφ'
    · rw [createFilter_cons_create hφ']
      dsimp
      rw [if_neg]
      rw [orderedInsert_createFilter_append_annihilate φ hφ φs φs']
      simp [normalOrderProp, hφ, hφ', CreateAnnihilate.normalOrder]
    · rw [createFilter_cons_annihilate hφ']
      rw [orderedInsert_createFilter_append_annihilate φ hφ φs]

lemma orderedInsert_annihilateFilter  (φ : 𝓕.CrAnStates)
     : (φs : List 𝓕.CrAnStates) →
    List.orderedInsert normalOrderProp φ (annihilateFilter φs ) =
    φ :: annihilateFilter φs
  | [] => by simp [annihilateFilter]
  | φ' :: φs  => by
    rcases CreateAnnihilate.eq_create_or_annihilate (𝓕.crAnStatesToCreateAnnihilate φ') with hφ' | hφ'
    · rw [annihilateFilter_cons_create hφ']
      rw [orderedInsert_annihilateFilter φ φs]
    · rw [annihilateFilter_cons_annihilate hφ']
      dsimp
      rw [if_pos]
      dsimp [normalOrderProp]
      rw [hφ']
      rcases CreateAnnihilate.eq_create_or_annihilate (𝓕.crAnStatesToCreateAnnihilate φ) with hφ | hφ
      · rw [hφ]
        simp [CreateAnnihilate.normalOrder]
      · rw [hφ]
        simp [CreateAnnihilate.normalOrder]


lemma orderedInsert_createFilter_append_annihilateFilter_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) →
     List.orderedInsert normalOrderProp φ (createFilter φs ++ annihilateFilter φs) =
    createFilter φs ++ φ :: annihilateFilter φs := by
  intro φs
  rw [orderedInsert_createFilter_append_annihilate φ hφ, orderedInsert_annihilateFilter]

lemma normalOrderList_eq_createFilter_append_annihilateFilter : (φs : List 𝓕.CrAnStates) →
    normalOrderList φs = createFilter φs ++ annihilateFilter φs
  | [] => by simp [normalOrderList, createFilter, annihilateFilter]
  | φ :: φs => by
    by_cases hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create
    · rw [normalOrderList_cons_create φ hφ φs]
      dsimp [createFilter]
      rw [List.filter_cons_of_pos]
      swap
      simp [hφ]
      dsimp [annihilateFilter]
      rw [List.filter_cons_of_neg]
      swap
      simp [hφ]
      rw [normalOrderList_eq_createFilter_append_annihilateFilter φs]
      rfl
    · dsimp [normalOrderList]
      rw [← normalOrderList]
      have hφ' : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate := by
        have hx := CreateAnnihilate.eq_create_or_annihilate (𝓕.crAnStatesToCreateAnnihilate φ)
        simp_all
      rw [normalOrderList_eq_createFilter_append_annihilateFilter φs]
      rw [orderedInsert_createFilter_append_annihilateFilter_annihilate φ hφ']
      rw [createFilter_cons_annihilate hφ']
      rw [annihilateFilter_cons_annihilate hφ']

/-!

## Normal order on the CrAnAlgebra

-/
namespace CrAnAlgebra

noncomputable section

/-- The normal ordering of elements of `CrAnAlgebra` as a linear map.  -/
def normalOrder : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕  :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  normalOrderSign φs • ofCrAnList (normalOrderList φs)

lemma normalOrder_ofCrAnList (φs : List 𝓕.CrAnStates) :
    normalOrder (ofCrAnList φs) = normalOrderSign φs • ofCrAnList (normalOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [normalOrder, Basis.constr_basis]

lemma ofCrAnList_eq_normalOrder (φs : List 𝓕.CrAnStates) :
    ofCrAnList (normalOrderList φs) = normalOrderSign φs • normalOrder (ofCrAnList φs) := by
  rw [normalOrder_ofCrAnList, normalOrderList]
  rw [smul_smul]
  simp [normalOrderSign]
  rw [Wick.koszulSign_mul_self]
  simp

lemma normalOrder_one : normalOrder (𝓕 := 𝓕) 1 = 1 := by
  rw [← ofCrAnList_nil, normalOrder_ofCrAnList]
  simp

lemma normalOrder_ofCrAnList_cons_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    normalOrder (ofCrAnList (φ :: φs)) =
    ofCrAnState φ * normalOrder (ofCrAnList φs) := by
  rw [normalOrder_ofCrAnList]
  rw [normalOrderSign_cons_create φ hφ, normalOrderList_cons_create φ hφ φs]
  rw [ofCrAnList_cons, normalOrder_ofCrAnList, mul_smul_comm]

lemma normalOrder_create_mul  (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.create)
    (a : CrAnAlgebra 𝓕) :
    normalOrder (ofCrAnState φ * a) = ofCrAnState φ * normalOrder a := by
  change (normalOrder ∘ₗ mulLinearMap (ofCrAnState φ)) a =
    (mulLinearMap (ofCrAnState φ) ∘ₗ normalOrder) a
  refine LinearMap.congr_fun ?h a
  apply ofCrAnListBasis.ext
  intro l
  simp [mulLinearMap]
  rw [← ofCrAnList_cons]
  rw [normalOrder_ofCrAnList_cons_create φ hφ]

lemma normalOrder_ofCrAnList_append_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnStates) :
    normalOrder (ofCrAnList (φs ++ [φ])) =
    normalOrder (ofCrAnList φs) * ofCrAnState φ := by
  rw [normalOrder_ofCrAnList]
  rw [normalOrderSign_append_annihlate φ hφ φs, normalOrderList_append_annihilate φ hφ φs]
  rw [ofCrAnList_append, ofCrAnList_singleton, normalOrder_ofCrAnList, smul_mul_assoc]

lemma normalOrder_mul_annihilate  (φ : 𝓕.CrAnStates)
    (hφ : 𝓕.crAnStatesToCreateAnnihilate φ = CreateAnnihilate.annihilate)
    (a : CrAnAlgebra 𝓕) :
    normalOrder (a * ofCrAnState φ) = normalOrder a * ofCrAnState φ := by
  change (normalOrder ∘ₗ mulLinearMap.flip (ofCrAnState φ)) a =
    (mulLinearMap.flip (ofCrAnState φ) ∘ₗ normalOrder) a
  refine LinearMap.congr_fun ?h a
  apply ofCrAnListBasis.ext
  intro l
  simp [mulLinearMap]
  rw [← ofCrAnList_singleton, ← ofCrAnList_append, ofCrAnList_singleton]
  rw [normalOrder_ofCrAnList_append_annihilate φ hφ]

lemma normalOrder_swap_create_annihlate_ofCrAnList_ofCrAnList (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnStates) :
    normalOrder (ofCrAnList φs' * ofCrAnState φc * ofCrAnState φa * ofCrAnList φs) =
    FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) •
    normalOrder (ofCrAnList φs' * ofCrAnState φa * ofCrAnState φc * ofCrAnList φs)  := by
  rw [mul_assoc, mul_assoc, ← ofCrAnList_cons, ← ofCrAnList_cons, ← ofCrAnList_append]
  rw [normalOrder_ofCrAnList, normalOrderSign_swap_create_annihlate φc φa hφc hφa]
  rw [normalOrderList_swap_create_annihlate φc φa hφc hφa]
  rw [← smul_smul, ← normalOrder_ofCrAnList]
  congr
  rw [ofCrAnList_append, ofCrAnList_cons, ofCrAnList_cons]
  noncomm_ring

lemma normalOrder_swap_create_annihlate_ofCrAnList (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) (a : 𝓕.CrAnAlgebra) :
    normalOrder (ofCrAnList φs * ofCrAnState φc * ofCrAnState φa * a) =
    FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) •
    normalOrder (ofCrAnList φs * ofCrAnState φa * ofCrAnState φc * a)  := by
  change (normalOrder ∘ₗ mulLinearMap (ofCrAnList φs * ofCrAnState φc * ofCrAnState φa)) a =
    (smulLinearMap _ ∘ₗ normalOrder ∘ₗ mulLinearMap (ofCrAnList φs * ofCrAnState φa * ofCrAnState φc)) a
  refine LinearMap.congr_fun ?h a
  apply ofCrAnListBasis.ext
  intro l
  simp [mulLinearMap]
  rw [normalOrder_swap_create_annihlate_ofCrAnList_ofCrAnList φc φa hφc hφa ]
  rfl

lemma normalOrder_swap_create_annihlate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.CrAnAlgebra) :
    normalOrder (a * ofCrAnState φc * ofCrAnState φa * b) =
    FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) •
    normalOrder (a * ofCrAnState φa * ofCrAnState φc * b)  := by
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  change (normalOrder ∘ₗ mulLinearMap.flip (ofCrAnState φc * (ofCrAnState φa * b))) a =
    (smulLinearMap (FieldStatistic.pairedSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa)) ∘ₗ normalOrder ∘ₗ mulLinearMap.flip (ofCrAnState φa * (ofCrAnState φc * b))) a
  apply LinearMap.congr_fun
  apply ofCrAnListBasis.ext
  intro l
  simp [mulLinearMap]
  repeat rw [← mul_assoc]
  rw [normalOrder_swap_create_annihlate_ofCrAnList φc φa hφc hφa ]
  rfl

lemma normalOrder_superCommute_create_annihilate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.CrAnAlgebra) :
    normalOrder (a * superCommute (ofCrAnState φc) (ofCrAnState φa) * b) = 0 := by
  rw [superCommute_ofCrAnState]
  simp
  rw [mul_sub, sub_mul, map_sub, ←  smul_mul_assoc]
  rw [← mul_assoc, ← mul_assoc]
  rw [normalOrder_swap_create_annihlate φc φa hφc hφa]
  simp only [FieldStatistic.instCommGroup.eq_1, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    map_smul, sub_self]

lemma normalOrder_superCommute_annihilate_create (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.CrAnAlgebra) :
    normalOrder (a * superCommute (ofCrAnState φa) (ofCrAnState φc) * b) = 0 := by
  rw [superCommute_ofCrAnState_symm]
  simp
  apply Or.inr
  exact normalOrder_superCommute_create_annihilate φc φa hφc hφa a b

lemma normalOrder_crPart_mul (φ : 𝓕.States) (a : CrAnAlgebra 𝓕) :
    normalOrder (crPart (StateAlgebra.ofState φ) * a) =
    crPart (StateAlgebra.ofState φ) * normalOrder a := by
  match φ with
  | .negAsymp φ =>
    dsimp [crPart, StateAlgebra.ofState]
    simp
    exact normalOrder_create_mul ⟨States.negAsymp φ, ()⟩ rfl a
  | .position φ =>
    dsimp [crPart, StateAlgebra.ofState]
    simp
    refine normalOrder_create_mul _ ?_ _
    simp [crAnStatesToCreateAnnihilate]
  | .posAsymp φ =>
    simp

lemma normalOrder_mul_anPart (φ : 𝓕.States) (a : CrAnAlgebra 𝓕) :
    normalOrder (a * anPart (StateAlgebra.ofState φ)) =
    normalOrder a * anPart (StateAlgebra.ofState φ) := by
  match φ with
  | .negAsymp φ =>
    simp
  | .position φ =>
    dsimp [anPart, StateAlgebra.ofState]
    simp
    refine normalOrder_mul_annihilate _ ?_ _
    simp [crAnStatesToCreateAnnihilate]
  | .posAsymp φ =>
    dsimp [anPart, StateAlgebra.ofState]
    simp
    refine normalOrder_mul_annihilate _ ?_ _
    simp [crAnStatesToCreateAnnihilate]

lemma normalOrder_swap_crPart_anPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
    normalOrder (a * (crPart (StateAlgebra.ofState φ))  *  (anPart (StateAlgebra.ofState φ')) * b) =
    FieldStatistic.pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    normalOrder (a * (anPart (StateAlgebra.ofState φ')) * (crPart (StateAlgebra.ofState φ)) * b)  := by
  match φ, φ' with
  | _, .negAsymp φ' =>
    simp
  | .posAsymp φ, _ =>
    simp
  | .position φ, .position φ' =>
    simp
    rw [normalOrder_swap_create_annihlate ]
    simp [crAnStatistics]
    rfl
    rfl
  | .negAsymp φ, .posAsymp φ' =>
    simp
    rw [normalOrder_swap_create_annihlate ]
    simp [crAnStatistics]
    rfl
    rfl
  | .negAsymp φ, .position φ' =>
    simp
    rw [normalOrder_swap_create_annihlate ]
    simp [crAnStatistics]
    rfl
    rfl
  | .position φ, .posAsymp φ' =>
    simp
    rw [normalOrder_swap_create_annihlate ]
    simp [crAnStatistics]
    rfl
    rfl

lemma normalOrder_swap_anPart_crPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
    normalOrder (a * (anPart (StateAlgebra.ofState φ))  *  (crPart (StateAlgebra.ofState φ')) * b) =
    FieldStatistic.pairedSign (𝓕.statesStatistic φ) (𝓕.statesStatistic φ') •
    normalOrder (a * (crPart (StateAlgebra.ofState φ')) * (anPart (StateAlgebra.ofState φ)) * b)  := by
  rw [normalOrder_swap_crPart_anPart]
  rw [smul_smul, FieldStatistic.pairedSign_symm, FieldStatistic.pairedSign_mul_self]
  simp

lemma normalOrder_superCommute_crPart_anPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
  normalOrder (a * superCommute
    (crPart (StateAlgebra.ofState φ)) (anPart (StateAlgebra.ofState φ')) * b) = 0 := by
  match φ, φ' with
  | _,  .negAsymp φ' =>
    simp
  | .posAsymp φ', _ =>
    simp
  | .position φ, .position φ' =>
    simp
    refine normalOrder_superCommute_create_annihilate _ _ (by rfl) (by rfl) _ _
  | .negAsymp φ, .posAsymp φ' =>
    simp
    refine normalOrder_superCommute_create_annihilate _ _ (by rfl) (by rfl) _ _
  | .negAsymp φ, .position φ' =>
    simp
    refine normalOrder_superCommute_create_annihilate _ _ (by rfl) (by rfl) _ _
  | .position φ, .posAsymp φ' =>
    simp
    refine normalOrder_superCommute_create_annihilate _ _ (by rfl) (by rfl) _ _

lemma normalOrder_superCommute_anPart_crPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
  normalOrder (a * superCommute
    (anPart (StateAlgebra.ofState φ)) (crPart (StateAlgebra.ofState φ')) * b) = 0 := by
  match φ, φ' with
  | .negAsymp φ',  _ =>
    simp
  | _, .posAsymp φ' =>
    simp
  | .position φ, .position φ' =>
    simp
    refine normalOrder_superCommute_annihilate_create _ _ (by rfl) (by rfl) _ _
  |  .posAsymp φ', .negAsymp φ =>
    simp
    refine normalOrder_superCommute_annihilate_create _ _ (by rfl) (by rfl) _ _
  | .position φ', .negAsymp φ =>
    simp
    refine normalOrder_superCommute_annihilate_create _ _ (by rfl) (by rfl) _ _
  | .posAsymp φ, .position φ' =>
    simp
    refine normalOrder_superCommute_annihilate_create _ _ (by rfl) (by rfl) _ _


lemma normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList
    (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφc' : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.create)
    (φs φs' : List 𝓕.CrAnStates) :
     (normalOrder (ofCrAnList φs * superCommute (ofCrAnState φc) (ofCrAnState φc') * ofCrAnList φs')) =
     normalOrderSign (φs ++ φc' :: φc :: φs') •
    (ofCrAnList (createFilter φs) * superCommute (ofCrAnState φc) (ofCrAnState φc') *
     ofCrAnList (createFilter φs') * ofCrAnList (annihilateFilter (φs ++ φs'))) := by
  rw [superCommute_ofCrAnState]
  rw [mul_sub, sub_mul, map_sub]
  conv_lhs =>
    lhs
    rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    lhs
    rw [normalOrder_ofCrAnList]
    rw [normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_create _ hφc, createFilter_singleton_create _ hφc']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_create _ hφc, annihilateFilter_singleton_create _ hφc']
    enter [2, 1, 2]
    simp
    rw [← annihilateFilter_append]
  conv_lhs =>
    rhs
    rhs
    rw [smul_mul_assoc]
    rw [Algebra.mul_smul_comm, smul_mul_assoc]
    rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    rhs
    rw [map_smul]
    rhs
    rw [normalOrder_ofCrAnList]
    rw [normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_create _ hφc, createFilter_singleton_create _ hφc']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_create _ hφc, annihilateFilter_singleton_create _ hφc']
    enter [2, 1, 2]
    simp
    rw [← annihilateFilter_append]
  conv_lhs =>
    lhs
    lhs
    simp
  conv_lhs =>
    rhs
    rhs
    lhs
    simp
  rw [normalOrderSign_swap_create_create φc φc' hφc hφc']
  rw [smul_smul, mul_comm, ← smul_smul]
  rw [← smul_sub, ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
  conv_lhs =>
    rhs
    rhs
    rw [ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
    rw [← smul_mul_assoc, ← smul_mul_assoc, ← Algebra.mul_smul_comm]
  rw [← sub_mul, ← sub_mul, ← mul_sub]
  congr
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton]
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton, smul_mul_assoc]


lemma normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList
    (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕.crAnStatesToCreateAnnihilate φa' = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnStates) :
     (normalOrder (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') * ofCrAnList φs')) =
     normalOrderSign (φs ++ φa' :: φa :: φs') •
    (ofCrAnList (createFilter (φs ++ φs'))
      * ofCrAnList (annihilateFilter φs) * superCommute (ofCrAnState φa) (ofCrAnState φa')
      * ofCrAnList (annihilateFilter φs')) := by
  rw [superCommute_ofCrAnState]
  rw [mul_sub, sub_mul, map_sub]
  conv_lhs =>
    lhs
    rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    lhs
    rw [normalOrder_ofCrAnList]
    rw [normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_annihilate _ hφa, createFilter_singleton_annihilate _ hφa']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_annihilate _ hφa, annihilateFilter_singleton_annihilate _ hφa']
    enter [2, 1, 1]
    simp
    rw [← createFilter_append]
  conv_lhs =>
    rhs
    rhs
    rw [smul_mul_assoc]
    rw [Algebra.mul_smul_comm, smul_mul_assoc]
    rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    rhs
    rw [map_smul]
    rhs
    rw [normalOrder_ofCrAnList]
    rw [normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_annihilate _ hφa, createFilter_singleton_annihilate _ hφa']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_annihilate _ hφa, annihilateFilter_singleton_annihilate _ hφa']
    enter [2, 1, 1]
    simp
    rw [← createFilter_append]
  conv_lhs =>
    lhs
    lhs
    simp
  conv_lhs =>
    rhs
    rhs
    lhs
    simp
  rw [normalOrderSign_swap_annihilate_annihilate φa φa' hφa hφa']
  rw [smul_smul, mul_comm, ← smul_smul]
  rw [← smul_sub, ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
  conv_lhs =>
    rhs
    rhs
    rw [ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
    rw [← Algebra.mul_smul_comm, ← smul_mul_assoc, ← Algebra.mul_smul_comm]
  rw [← mul_sub, ← sub_mul, ← mul_sub, ]
  apply congrArg
  conv_rhs => rw [mul_assoc, mul_assoc]
  apply congrArg
  rw [mul_assoc]
  apply congrArg
  congr
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton]
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton, smul_mul_assoc]


@[simp]
lemma normalOrder_crPart_mul_crPart (φ φ' : 𝓕.States) :
    normalOrder (crPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ')) =
    crPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ') := by
  rw [normalOrder_crPart_mul]
  conv_lhs => rw [← mul_one (crPart (StateAlgebra.ofState φ'))]
  rw [normalOrder_crPart_mul, normalOrder_one]
  simp

@[simp]
lemma normalOrder_anPart_mul_anPart (φ φ' : 𝓕.States) :
    normalOrder (anPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ')) =
    anPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') := by
  rw [normalOrder_mul_anPart]
  conv_lhs => rw [← one_mul (anPart (StateAlgebra.ofState φ))]
  rw [normalOrder_mul_anPart, normalOrder_one]
  simp

@[simp]
lemma normalOrder_crPart_mul_anPart (φ φ' : 𝓕.States) :
    normalOrder (crPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ')) =
    crPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') := by
  rw [normalOrder_crPart_mul]
  conv_lhs => rw [← one_mul (anPart (StateAlgebra.ofState φ'))]
  rw [normalOrder_mul_anPart, normalOrder_one]
  simp

@[simp]
lemma normalOrder_anPart_mul_crPart (φ φ' : 𝓕.States) :
    normalOrder (anPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ')) =
    (FieldStatistic.pairedSign (𝓕.statesStatistic φ)) (𝓕.statesStatistic φ') •
    (crPart (StateAlgebra.ofState φ') * anPart (StateAlgebra.ofState φ)) := by
  conv_lhs => rw [← one_mul (anPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ'))]
  conv_lhs => rw [← mul_one (1 * (anPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ')))]
  rw [← mul_assoc, normalOrder_swap_anPart_crPart]
  simp

lemma normalOrder_ofState_mul_ofState (φ φ' : 𝓕.States) :
    normalOrder (ofState φ * ofState φ') =
    crPart (StateAlgebra.ofState φ) * crPart (StateAlgebra.ofState φ') +
    (FieldStatistic.pairedSign (𝓕.statesStatistic φ)) (𝓕.statesStatistic φ') •
      (crPart (StateAlgebra.ofState φ') * anPart (StateAlgebra.ofState φ)) +
    crPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ') +
    anPart (StateAlgebra.ofState φ) * anPart (StateAlgebra.ofState φ')  := by
  rw [ofState_eq_crPart_add_anPart, ofState_eq_crPart_add_anPart]
  rw [mul_add, add_mul, add_mul]
  simp
  abel

lemma ofCrAnList_superCommute_normalOrder_ofCrAnList (φs φs' : List 𝓕.CrAnStates) :
    ⟨ofCrAnList φs, normalOrder (ofCrAnList φs')⟩ₛca =
    ofCrAnList φs * normalOrder (ofCrAnList φs') -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • normalOrder (ofCrAnList φs') * ofCrAnList φs := by
  simp [normalOrder_ofCrAnList, map_smul, superCommute_ofCrAnList, ofCrAnList_append,
    smul_sub, smul_smul, mul_comm]

lemma ofCrAnList_superCommute_normalOrder_ofStateList (φs  : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States ): ⟨ofCrAnList φs, normalOrder (ofStateList φs')⟩ₛca =
    ofCrAnList φs * normalOrder (ofStateList φs') -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • normalOrder (ofStateList φs') * ofCrAnList φs := by
  rw [ofStateList_sum, map_sum, Finset.mul_sum,  Finset.smul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, map_sum]
  congr
  funext n
  rw [ofCrAnList_superCommute_normalOrder_ofCrAnList,
    CreateAnnihilateSect.statistics_eq_state_statistics]

lemma ofCrAnList_mul_normalOrder_ofStateList_eq_superCommute (φs  : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States ):
    ofCrAnList φs * normalOrder (ofStateList φs') =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • normalOrder (ofStateList φs') * ofCrAnList φs
    + ⟨ofCrAnList φs, normalOrder (ofStateList φs')⟩ₛca  := by
  rw [ofCrAnList_superCommute_normalOrder_ofStateList]
  simp

lemma ofCrAnState_mul_normalOrder_ofStateList_eq_superCommute (φ : 𝓕.CrAnStates)
    (φs' : List 𝓕.States ):
    ofCrAnState φ * normalOrder (ofStateList φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • normalOrder (ofStateList φs') * ofCrAnState φ
    + ⟨ofCrAnState φ, normalOrder (ofStateList φs')⟩ₛca  := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_normalOrder_ofStateList_eq_superCommute]
  simp [ofCrAnList_singleton]

lemma anPart_mul_normalOrder_ofStateList_eq_superCommute (φ : 𝓕.States)
    (φs' : List 𝓕.States ):
    anPart (StateAlgebra.ofState φ) * normalOrder (ofStateList φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • normalOrder (ofStateList φs' * anPart (StateAlgebra.ofState φ))
    + ⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φs')⟩ₛca  := by
  rw [normalOrder_mul_anPart]
  match φ with
  | .negAsymp φ =>
    simp
  | .position φ =>
    simp
    rw [ofCrAnState_mul_normalOrder_ofStateList_eq_superCommute]
    simp [crAnStatistics]
  | .posAsymp φ =>
    simp
    rw [ofCrAnState_mul_normalOrder_ofStateList_eq_superCommute]
    simp [crAnStatistics]

end

end CrAnAlgebra

namespace OperatorAlgebra
variable {𝓞 : OperatorAlgebra 𝓕}
open CrAnAlgebra

lemma crAnF_normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList
    (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (hφc' : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.create)
    (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder (ofCrAnList φs * superCommute (ofCrAnState φc) (ofCrAnState φc') * ofCrAnList φs'))
    = 0 := by
  rw [normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList φc φc' hφc hφc' φs φs']
  rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_create_create φc φc' hφc hφc']
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList
    (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕.crAnStatesToCreateAnnihilate φa' = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') * ofCrAnList φs'))
    = 0 := by
  rw [normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
  rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_annihilate_annihilate φa φa' hφa hφa']
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') * ofCrAnList φs'))
    = 0 := by
  rcases CreateAnnihilate.eq_create_or_annihilate (𝓕.crAnStatesToCreateAnnihilate φa) with hφa | hφa
  <;> rcases CreateAnnihilate.eq_create_or_annihilate (𝓕.crAnStatesToCreateAnnihilate φa') with hφa' | hφa'
  · rw [normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_create_create φa φa' hφa hφa']
    simp
  · rw [normalOrder_superCommute_create_annihilate φa φa' hφa hφa' (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrder_superCommute_annihilate_create φa' φa hφa' hφa (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_annihilate_annihilate φa φa' hφa hφa']
    simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates)
    (a : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') * a))
    = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap ( (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') ))) a =
    0
  have hf : 𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap ( (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa'))) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp
    exact crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero φa φa' φs l
  rw [hf]
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnState_eq_zero_mul (φa φa' : 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnState φa) (ofCrAnState φa') * b)) = 0 := by
  rw [mul_assoc]
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap.flip ((superCommute (ofCrAnState φa) (ofCrAnState φa') * b ))) a =
    0
  have hf :  (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap.flip ((superCommute (ofCrAnState φa) (ofCrAnState φa') * b ))) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp [mulLinearMap]
    rw [← mul_assoc]
    exact crAnF_normalOrder_superCommute_ofCrAnList_eq_zero φa φa' _ _
  rw [hf]
  simp


lemma crAnF_normalOrder_superCommute_ofCrAnState_ofCrAnList_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnState φa) (ofCrAnList φs) * b)) = 0 := by
  rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b, ofCrAnList_singleton]
  rw [crAnF_normalOrder_superCommute_ofCrAnState_eq_zero_mul]

lemma crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnState_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnList φs)  (ofCrAnState φa) * b)) = 0 := by
  rw [← ofCrAnList_singleton, superCommute_ofCrAnList_symm, ofCrAnList_singleton]
  simp only [FieldStatistic.instCommGroup.eq_1, FieldStatistic.ofList_singleton,  mul_neg,
    Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, map_neg, map_smul]
  rw [crAnF_normalOrder_superCommute_ofCrAnState_ofCrAnList_eq_zero_mul]
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero_mul
    (φs φs' : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnList φs) (ofCrAnList φs') * b)) = 0 := by
  rw [ superCommute_ofCrAnList_ofCrAnList_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b]
  rw [crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnState_eq_zero_mul]

lemma crAnF_normalOrder_superCommute_ofCrAnList_eq_zero_mul
    (φs : List 𝓕.CrAnStates)
    (a b c : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnList φs) c * b)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute (ofCrAnList φs)) c = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute (ofCrAnList φs)) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs'
    simp [mulLinearMap]
    rw [crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero_mul
    (a b c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (a * superCommute d c * b)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute.flip c) d = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute.flip c) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs
    simp [mulLinearMap]
    rw [crAnF_normalOrder_superCommute_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero_mul_right
    (b c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (superCommute d c * b)) = 0 := by
  rw [← crAnF_normalOrder_superCommute_eq_zero_mul 1 b c d]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero_mul_left
    (a c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (a * superCommute d c)) = 0 := by
  rw [← crAnF_normalOrder_superCommute_eq_zero_mul a 1 c d]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero
    (c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (superCommute d c)) = 0 := by
  rw [← crAnF_normalOrder_superCommute_eq_zero_mul 1 1 c d]
  simp


lemma crAnF_normalOrder_ofState_ofState_swap (φ φ' : 𝓕.States) :
    𝓞.crAnF (normalOrder (ofState φ * ofState φ')) =
    (FieldStatistic.pairedSign (𝓕.statesStatistic φ)) (𝓕.statesStatistic φ') •
    𝓞.crAnF (normalOrder (ofState φ' * ofState φ)) := by
  conv_lhs =>
    rhs
    rhs
    rw [ofState_eq_crPart_add_anPart, ofState_eq_crPart_add_anPart]
    rw [mul_add, add_mul, add_mul]
    rw [crPart_crPart_eq_superCommute, crPart_anPart_eq_superCommute,
      anPart_anPart_eq_superCommute, anPart_crPart_eq_superCommute]
  simp only [FieldStatistic.instCommGroup.eq_1, Algebra.smul_mul_assoc, map_add, map_smul,
    normalOrder_crPart_mul_crPart, normalOrder_crPart_mul_anPart, normalOrder_anPart_mul_crPart,
    normalOrder_anPart_mul_anPart, map_mul, crAnF_normalOrder_superCommute_eq_zero, add_zero]
  rw [normalOrder_ofState_mul_ofState]
  simp
  rw [smul_smul]
  simp
  abel
open FieldStatistic
lemma crAnF_normalOrder_ofCrAnState_ofCrAnList_swap (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder (ofCrAnState φ * ofCrAnList φs)) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓞.crAnF (normalOrder (ofCrAnList φs * ofCrAnState φ)) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp

lemma crAnF_normalOrder_ofCrAnState_ofStatesList_swap (φ  : 𝓕.CrAnStates)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrder (ofCrAnState φ * ofStateList φ')) =
    (FieldStatistic.pairedSign (𝓕.crAnStatistics φ)) (FieldStatistic.ofList 𝓕.statesStatistic φ') •
    𝓞.crAnF (normalOrder (ofStateList φ' * ofCrAnState φ)) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofStateList_eq_superCommute ]
  simp

lemma crAnF_normalOrder_anPart_ofStatesList_swap  (φ  : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrder (ofStateList φ' * anPart (StateAlgebra.ofState φ))) := by
  match φ with
  | .negAsymp φ =>
    simp
  | .position φ =>
    simp
    rw [crAnF_normalOrder_ofCrAnState_ofStatesList_swap]
    rfl
  | .posAsymp φ =>
    simp
    rw [crAnF_normalOrder_ofCrAnState_ofStatesList_swap]
    rfl

lemma crAnF_normalOrder_ofStatesList_anPart_swap (φ  : 𝓕.States)
    (φ' : List 𝓕.States) :
     𝓞.crAnF (normalOrder  (ofStateList φ' * anPart (StateAlgebra.ofState φ)))
    = (FieldStatistic.pairedSign (𝓕.statesStatistic φ)) (FieldStatistic.ofList 𝓕.statesStatistic φ') •
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) := by
  rw [crAnF_normalOrder_anPart_ofStatesList_swap]
  simp [smul_smul, FieldStatistic.pairedSign_mul_self]

lemma crAnF_normalOrder_ofStatesList_mul_anPart_swap  (φ  : 𝓕.States)
    (φ' : List 𝓕.States) :
     𝓞.crAnF (normalOrder (ofStateList φ') * anPart (StateAlgebra.ofState φ)) =
    (FieldStatistic.pairedSign (𝓕.statesStatistic φ)) (FieldStatistic.ofList 𝓕.statesStatistic φ') •
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) := by
  rw [← normalOrder_mul_anPart]
  rw [crAnF_normalOrder_ofStatesList_anPart_swap]

lemma crAnF_ofCrAnState_superCommute_normalOrder_ofCrAnList_eq_sum (φ  : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) : 𝓞.crAnF (⟨ofCrAnState φ, normalOrder (ofCrAnList φs)⟩ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
      𝓞.crAnF (⟨ofCrAnState φ, ofCrAnState φs[n]⟩ₛca)
      * 𝓞.crAnF (normalOrder (ofCrAnList (φs.eraseIdx n))) := by
  rw [normalOrder_ofCrAnList, map_smul, map_smul]
  rw [crAnF_superCommute_ofCrAnState_ofCrAnList_eq_sum, sum_normalOrderList_length]
  simp [Finset.smul_sum]
  congr
  funext n
  rw [ofCrAnList_eq_normalOrder, map_smul, mul_smul_comm, smul_smul, smul_smul]
  by_cases hs : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[n])
  · congr
    erw [normalOrderSign_eraseIdx, ←  hs]
    trans (normalOrderSign φs * normalOrderSign φs) *
      (𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ ((normalOrderList φs).take (normalOrderEquiv n))) *
      𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ ((normalOrderList φs).take (normalOrderEquiv n))))
      *  𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ (φs.take n))
    · ring_nf
      rw [hs]
      rfl
    · simp [hs]
  · erw [𝓞.superCommute_different_statistics _ _ hs]
    simp

lemma crAnF_ofCrAnState_superCommute_normalOrder_ofStateList_eq_sum (φ  : 𝓕.CrAnStates)
      (φs : List 𝓕.States) : 𝓞.crAnF (⟨ofCrAnState φ, normalOrder (ofStateList φs)⟩ₛca) =
      ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
      𝓞.crAnF (⟨ofCrAnState φ, ofState φs[n]⟩ₛca)
      * 𝓞.crAnF (normalOrder (ofStateList (φs.eraseIdx n))) := by
  conv_lhs =>
    rw [ofStateList_sum, map_sum, map_sum, map_sum]
    enter [2, s]
    rw [crAnF_ofCrAnState_superCommute_normalOrder_ofCrAnList_eq_sum,
      CreateAnnihilateSect.sum_over_length]
    enter [2, n]
    rw [CreateAnnihilateSect.take_statistics_eq_take_state_statistics, smul_mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp [← Finset.smul_sum, CreateAnnihilateSect.sum_eraseIdxEquiv n _ n.prop]
  conv_lhs =>
    enter [2, 2, n]
    rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← ofState, ← map_sum, ← map_sum, ← ofStateList_sum]


lemma crAnF_anPart_superCommute_normalOrder_ofStateList_eq_sum (φ  : 𝓕.States)
      (φs : List 𝓕.States) : 𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φs)⟩ₛca) =
      ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
      𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), ofState φs[n]⟩ₛca)
      * 𝓞.crAnF (normalOrder (ofStateList (φs.eraseIdx n))) := by
  match φ with
  | .negAsymp φ =>
    simp
  | .position φ =>
    simp
    rw [crAnF_ofCrAnState_superCommute_normalOrder_ofStateList_eq_sum]
    simp [crAnStatistics]
  | .posAsymp φ =>
    simp
    rw [crAnF_ofCrAnState_superCommute_normalOrder_ofStateList_eq_sum]
    simp [crAnStatistics]

lemma crAnF_anPart_mul_normalOrder_ofStatesList_eq_superCommute (φ  : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (anPart (StateAlgebra.ofState φ) * normalOrder (ofStateList φ')) =
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) +
    𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φ')⟩ₛca) := by
  rw [anPart_mul_normalOrder_ofStateList_eq_superCommute]
  simp
  congr
  rw [crAnF_normalOrder_anPart_ofStatesList_swap]

lemma crAnF_ofState_mul_normalOrder_ofStatesList_eq_superCommute (φ  : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (ofState φ * normalOrder (ofStateList φ')) =
    𝓞.crAnF (normalOrder (ofState φ * ofStateList φ')) +
    𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φ')⟩ₛca) := by
  conv_lhs => rw [ofState_eq_crPart_add_anPart]
  rw [add_mul, map_add, crAnF_anPart_mul_normalOrder_ofStatesList_eq_superCommute, ← add_assoc,
    ← normalOrder_crPart_mul, ← map_add]
  conv_lhs =>
    lhs
    rw [← map_add, ← add_mul, ← ofState_eq_crPart_add_anPart]


noncomputable def contractMemList (φ  : 𝓕.States) (φs : List 𝓕.States) (n : Option (Fin φs.length))  :
  𝓞.A :=
  match n with
  | none => 1
  | some n => 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
        𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), ofState φs[n]⟩ₛca)

lemma crAnF_ofState_mul_normalOrder_ofStatesList_eq_sum (φ  : 𝓕.States)
    (φs : List 𝓕.States) :
    𝓞.crAnF (ofState φ * normalOrder (ofStateList φs)) =
    ∑ n : Option (Fin φs.length),
      contractMemList φ φs n *
      𝓞.crAnF (normalOrder (ofStateList (HepLean.List.optionEraseZ φs φ n))) := by
  rw [crAnF_ofState_mul_normalOrder_ofStatesList_eq_superCommute]
  rw [crAnF_anPart_superCommute_normalOrder_ofStateList_eq_sum]
  simp [contractMemList]
  rfl

lemma crAnF_ofState_normalOrder_insert (φ  : 𝓕.States) (φs : List 𝓕.States) (k : Fin φs.length.succ) :
    𝓞.crAnF (normalOrder (ofStateList (φ :: φs))) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs.take k) • 𝓞.crAnF (normalOrder (ofStateList (φs.insertIdx k φ))) := by
  have hl : φs.insertIdx k φ =  φs.take k ++ [φ] ++  φs.drop k := by
    rw [HepLean.List.insertIdx_eq_take_drop]
    simp
  rw [hl]
  rw [ofStateList_append, ofStateList_append]
  rw [ofStateList_mul_ofStateList_eq_superCommute, add_mul]
  simp [smul_smul]
  rw [← ofStateList_append, ← ofStateList_append]
  simp

end OperatorAlgebra

end FieldStruct
