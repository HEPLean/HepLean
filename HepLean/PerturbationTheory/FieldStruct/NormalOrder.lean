/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.Basic
import HepLean.PerturbationTheory.Koszul.KoszulSign
import HepLean.PerturbationTheory.FieldStruct.Filters
/-!

# Normal Ordering

The normal ordering puts all creation operators to the left and all annihilation operators to the
right. It acts on `CrAnStates` and defines a linear map from the `CrAnAlgebra` to itself.

The normal ordering satisfies a number of nice properties with relation to the operator
algebra 𝓞.A.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

/-- The normal ordering relation on creation and annihlation operators.
  For a list of creation and annihlation states, this relation is designed
  to move all creation states to the left, and all annihlation operators to the right.
  We have that `normalOrderRel φ1 φ2` is true if
  - `φ1` is a creation operator
  or
  - `φ2` is an annihlate operator. -/
def normalOrderRel : 𝓕.CrAnStates → 𝓕.CrAnStates → Prop :=
  fun a b => CreateAnnihilate.normalOrder (𝓕 |>ᶜ a) (𝓕 |>ᶜ b)

/-- Normal ordering is total. -/
instance : IsTotal 𝓕.CrAnStates 𝓕.normalOrderRel where
  total _ _ := total_of CreateAnnihilate.normalOrder _ _

/-- Normal ordering is transitive. -/
instance : IsTrans 𝓕.CrAnStates 𝓕.normalOrderRel where
  trans _ _ _ := fun h h' => IsTrans.trans (α := CreateAnnihilate) _ _ _ h h'

/-- A decidable instance on the normal ordering relation. -/
instance (φ φ' : 𝓕.CrAnStates) : Decidable (normalOrderRel φ φ') :=
  CreateAnnihilate.instDecidableNormalOrder (𝓕 |>ᶜ φ) (𝓕 |>ᶜ φ')

/-!

## Normal order sign.

-/

/-- The sign associated with putting a list of creation and annihlation states into normal order
  (with the creation operators on the left).
  We pick up a minus sign for every fermion paired crossed. -/
def normalOrderSign (φs : List 𝓕.CrAnStates) : ℂ :=
  Wick.koszulSign 𝓕.crAnStatistics 𝓕.normalOrderRel φs

@[simp]
lemma normalOrderSign_mul_self (φs : List 𝓕.CrAnStates) :
    normalOrderSign φs * normalOrderSign φs = 1 := by
  simp [normalOrderSign, Wick.koszulSign, Wick.koszulSign_mul_self]

lemma koszulSignInsert_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) : (φs : List 𝓕.CrAnStates) →
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φ φs = 1
  | [] => rfl
  | φ' :: φs => by
    dsimp only [Wick.koszulSignInsert]
    rw [if_pos]
    · exact koszulSignInsert_create φ hφ φs
    · dsimp only [normalOrderRel]
      rw [hφ]
      dsimp [CreateAnnihilate.normalOrder]

lemma normalOrderSign_cons_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φ :: φs) = normalOrderSign φs := by
  dsimp only [normalOrderSign, Wick.koszulSign]
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
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) →
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φ' (φs ++ [φ]) =
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φ' φs
  | [] => by
    simp only [Wick.koszulSignInsert, normalOrderRel, hφ, ite_eq_left_iff,
      CreateAnnihilate.not_normalOrder_annihilate_iff_false, ite_eq_right_iff, and_imp,
      IsEmpty.forall_iff]
  | φ'' :: φs => by
    dsimp only [List.cons_append, Wick.koszulSignInsert]
    rw [koszulSignInsert_append_annihilate φ' φ hφ φs]

lemma normalOrderSign_append_annihlate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ [φ]) = normalOrderSign φs
  | [] => by simp
  | φ' :: φs => by
    dsimp only [List.cons_append, normalOrderSign, Wick.koszulSign]
    have hi := normalOrderSign_append_annihlate φ hφ φs
    dsimp only [normalOrderSign] at hi
    rw [hi, koszulSignInsert_append_annihilate φ' φ hφ φs]

lemma koszulSignInsert_annihilate_cons_create (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φa (φc :: φs)
    = FieldStatistic.exchangeSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) *
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φa φs := by
  rw [Wick.koszulSignInsert_cons]
  simp only [FieldStatistic.instCommGroup.eq_1, mul_eq_mul_right_iff]
  apply Or.inl
  rw [Wick.koszulSignCons, if_neg, FieldStatistic.exchangeSign_symm,
    FieldStatistic.exchangeSign_eq_if]
  rw [normalOrderRel, hφa, hφc]
  simp [CreateAnnihilate.normalOrder]

lemma normalOrderSign_swap_create_annihlate_fst (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φc :: φa :: φs) =
    FieldStatistic.exchangeSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) *
    normalOrderSign (φa :: φc :: φs) := by
  rw [normalOrderSign_cons_create φc hφc (φa :: φs)]
  conv_rhs =>
    rw [normalOrderSign, Wick.koszulSign, ← normalOrderSign]
    rw [koszulSignInsert_annihilate_cons_create φc φa hφc hφa φs]
  rw [← mul_assoc, ← mul_assoc, FieldStatistic.exchangeSign_mul_self]
  rw [one_mul, normalOrderSign_cons_create φc hφc φs]
  rfl

lemma koszulSignInsert_swap (φ φc φa : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φ (φs ++ φa :: φc :: φs')
    = Wick.koszulSignInsert 𝓕.crAnStatistics normalOrderRel φ (φs ++ φc :: φa :: φs') := by
  apply Wick.koszulSignInsert_eq_perm
  refine List.Perm.append_left φs ?h.a
  exact List.Perm.swap φc φa φs'

lemma normalOrderSign_swap_create_annihlate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate) :
    (φs φs' : List 𝓕.CrAnStates) → normalOrderSign (φs ++ φc :: φa :: φs') =
    FieldStatistic.exchangeSign (𝓕.crAnStatistics φc) (𝓕.crAnStatistics φa) *
    normalOrderSign (φs ++ φa :: φc :: φs')
  | [], φs' => normalOrderSign_swap_create_annihlate_fst φc φa hφc hφa φs'
  | φ :: φs, φs' => by
    rw [normalOrderSign]
    dsimp only [List.cons_append, Wick.koszulSign, FieldStatistic.instCommGroup.eq_1]
    rw [← normalOrderSign, normalOrderSign_swap_create_annihlate φc φa hφc hφa φs φs']
    rw [← mul_assoc, mul_comm _ (FieldStatistic.exchangeSign _ _), mul_assoc]
    simp only [FieldStatistic.instCommGroup.eq_1, mul_eq_mul_left_iff]
    apply Or.inl
    conv_rhs =>
      rw [normalOrderSign]
      dsimp [Wick.koszulSign]
      rw [← normalOrderSign]
    simp only [mul_eq_mul_right_iff]
    apply Or.inl
    rw [koszulSignInsert_swap]

lemma normalOrderSign_swap_create_create_fst (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφc' : 𝓕 |>ᶜ φc' = CreateAnnihilate.create)
    (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φc :: φc' :: φs) = normalOrderSign (φc' :: φc :: φs) := by
  rw [normalOrderSign_cons_create φc hφc, normalOrderSign_cons_create φc' hφc']
  rw [normalOrderSign_cons_create φc' hφc', normalOrderSign_cons_create φc hφc]

lemma normalOrderSign_swap_create_create (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφc' : 𝓕 |>ᶜ φc' = CreateAnnihilate.create) :
    (φs φs' : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ φc :: φc' :: φs') = normalOrderSign (φs ++ φc' :: φc :: φs')
  | [], φs' => by
    exact normalOrderSign_swap_create_create_fst φc φc' hφc hφc' φs'
  | φ :: φs, φs' => by
    rw [normalOrderSign]
    dsimp only [List.cons_append, Wick.koszulSign]
    rw [← normalOrderSign, normalOrderSign_swap_create_create φc φc' hφc hφc']
    dsimp only [normalOrderSign, Wick.koszulSign]
    rw [← normalOrderSign]
    simp only [mul_eq_mul_right_iff]
    apply Or.inl (Wick.koszulSignInsert_eq_perm _ _ _ _ _ _)
    exact List.Perm.append_left φs (List.Perm.swap φc' φc φs')

lemma normalOrderSign_swap_annihilate_annihilate_fst (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕 |>ᶜ φa' = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    normalOrderSign (φa :: φa' :: φs) =
    normalOrderSign (φa' :: φa :: φs) := by
  rw [normalOrderSign, normalOrderSign]
  dsimp only [Wick.koszulSign]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [Wick.koszulSignInsert_cons, Wick.koszulSignInsert_cons, mul_assoc, mul_assoc]
  congr 1
  · dsimp only [Wick.koszulSignCons]
    rw [if_pos, if_pos]
    · simp [normalOrderRel, hφa, hφa', CreateAnnihilate.normalOrder]
    · simp [normalOrderRel, hφa, hφa', CreateAnnihilate.normalOrder]
  · rw [NonUnitalNormedCommRing.mul_comm]

lemma normalOrderSign_swap_annihilate_annihilate (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕 |>ᶜ φa' = CreateAnnihilate.annihilate) : (φs φs' : List 𝓕.CrAnStates) →
    normalOrderSign (φs ++ φa :: φa' :: φs') = normalOrderSign (φs ++ φa' :: φa :: φs')
  | [], φs' => by
    exact normalOrderSign_swap_annihilate_annihilate_fst φa φa' hφa hφa' φs'
  | φ :: φs, φs' => by
    rw [normalOrderSign]
    dsimp only [List.cons_append, Wick.koszulSign]
    rw [← normalOrderSign]
    rw [normalOrderSign_swap_annihilate_annihilate φa φa' hφa hφa']
    dsimp only [normalOrderSign, Wick.koszulSign]
    rw [← normalOrderSign]
    simp only [mul_eq_mul_right_iff]
    apply Or.inl
    apply Wick.koszulSignInsert_eq_perm
    refine List.Perm.append_left φs ?h.h.a
    exact List.Perm.swap φa' φa φs'
open FieldStatistic

/-!

## Normal order of lists

-/

/-- The normal ordering of a list of creation and annihilation states.
  To give some schematic. For example:
  - `normalOrderList [φ1c, φ1a, φ2c, φ2a] = [φ1c, φ2c, φ1a, φ2a]`
-/
def normalOrderList (φs : List 𝓕.CrAnStates) : List 𝓕.CrAnStates :=
  List.insertionSort 𝓕.normalOrderRel φs

@[simp]
lemma normalOrderList_nil : normalOrderList (𝓕 := 𝓕) [] = [] := by
  simp [normalOrderList]

@[simp]
lemma normalOrderList_statistics (φs : List 𝓕.CrAnStates) :
    (𝓕 |>ₛ (normalOrderList φs)) = 𝓕 |>ₛ φs := by
  simp [normalOrderList, List.insertionSort]

lemma orderedInsert_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) :
    (φs : List 𝓕.CrAnStates) → List.orderedInsert normalOrderRel φ φs = φ :: φs
  | [] => rfl
  | φ' :: φs => by
    dsimp only [List.orderedInsert.eq_2]
    rw [if_pos]
    dsimp only [normalOrderRel]
    rw [hφ]
    dsimp [CreateAnnihilate.normalOrder]

lemma normalOrderList_cons_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    normalOrderList (φ :: φs) = φ :: normalOrderList φs := by
  simp only [normalOrderList, List.insertionSort]
  rw [orderedInsert_create φ hφ]

lemma orderedInsert_append_annihilate (φ' φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) → List.orderedInsert normalOrderRel φ' (φs ++ [φ]) =
    List.orderedInsert normalOrderRel φ' φs ++ [φ]
  | [] => by
    simp [Wick.koszulSignInsert, normalOrderRel, hφ]
  | φ'' :: φs => by
    dsimp only [List.cons_append, List.orderedInsert.eq_2]
    have hi := orderedInsert_append_annihilate φ' φ hφ φs
    rw [hi]
    split
    next h => simp_all only [List.cons_append]
    next h => simp_all only [List.cons_append]

lemma normalOrderList_append_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) :
    (φs : List 𝓕.CrAnStates) →
    normalOrderList (φs ++ [φ]) = normalOrderList φs ++ [φ]
  | [] => by simp [normalOrderList]
  | φ' :: φs => by
    simp only [normalOrderList, List.insertionSort, List.append_eq]
    have hi := normalOrderList_append_annihilate φ hφ φs
    dsimp only [normalOrderList] at hi
    rw [hi, orderedInsert_append_annihilate φ' φ hφ]

lemma normalOrder_swap_create_annihlate_fst (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) :
    normalOrderList (φc :: φa :: φs) = normalOrderList (φa :: φc :: φs) := by
  rw [normalOrderList_cons_create φc hφc (φa :: φs)]
  conv_rhs =>
    rw [normalOrderList, List.insertionSort]
  have hi := normalOrderList_cons_create φc hφc φs
  rw [normalOrderList] at hi
  rw [hi]
  dsimp only [List.orderedInsert.eq_2]
  split
  · rename_i h
    rw [normalOrderRel, hφa, hφc] at h
    dsimp [CreateAnnihilate.normalOrder] at h
  · rfl

lemma normalOrderList_swap_create_annihlate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate) :
    (φs φs' : List 𝓕.CrAnStates) →
    normalOrderList (φs ++ φc :: φa :: φs') = normalOrderList (φs ++ φa :: φc :: φs')
  | [], φs' => normalOrder_swap_create_annihlate_fst φc φa hφc hφa φs'
  | φ :: φs, φs' => by
    dsimp only [List.cons_append, normalOrderList, List.insertionSort]
    have hi := normalOrderList_swap_create_annihlate φc φa hφc hφa φs φs'
    dsimp only [normalOrderList] at hi
    rw [hi]

/-- For a list of creation and annihlation states, the equivalence between
  `Fin φs.length` and `Fin (normalOrderList φs).length` taking each position in `φs`
  to it's corresponding position in the normal ordered list. This assumes that
  we are using the insertion sort method.
  For example:
  - For `[φ1c, φ1a, φ2c, φ2a]` this equivalence sends `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 1`, `3 ↦ 3`.
-/
def normalOrderEquiv {φs : List 𝓕.CrAnStates} : Fin φs.length ≃ Fin (normalOrderList φs).length :=
  HepLean.List.insertionSortEquiv 𝓕.normalOrderRel φs

lemma sum_normalOrderList_length {M : Type} [AddCommMonoid M]
    (φs : List 𝓕.CrAnStates) (f : Fin (normalOrderList φs).length → M) :
    ∑ (n : Fin (normalOrderList φs).length), f n = ∑ (n : Fin φs.length), f (normalOrderEquiv n) :=
  Eq.symm (Equiv.sum_comp normalOrderEquiv f)

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
  simp only [normalOrderList, normalOrderEquiv]
  rw [HepLean.List.eraseIdx_insertionSort_fin]

lemma normalOrderSign_eraseIdx (φs : List 𝓕.CrAnStates) (n : Fin φs.length) :
    normalOrderSign (φs.eraseIdx n) = normalOrderSign φs *
    𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ (φs.take n)) *
    𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ ((normalOrderList φs).take (normalOrderEquiv n))) := by
  rw [normalOrderSign, Wick.koszulSign_eraseIdx, ← normalOrderSign]
  rfl

lemma orderedInsert_createFilter_append_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) : (φs φs' : List 𝓕.CrAnStates) →
    List.orderedInsert normalOrderRel φ (createFilter φs ++ φs') =
    createFilter φs ++ List.orderedInsert normalOrderRel φ φs'
  | [], φs' => by simp [createFilter]
  | φ' :: φs, φs' => by
    rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φ') with hφ' | hφ'
    · rw [createFilter_cons_create hφ']
      dsimp only [List.cons_append, List.orderedInsert.eq_2]
      rw [if_neg, orderedInsert_createFilter_append_annihilate φ hφ φs φs']
      simp [normalOrderRel, hφ, hφ', CreateAnnihilate.normalOrder]
    · rw [createFilter_cons_annihilate hφ', orderedInsert_createFilter_append_annihilate φ hφ φs]

lemma orderedInsert_annihilateFilter (φ : 𝓕.CrAnStates) : (φs : List 𝓕.CrAnStates) →
    List.orderedInsert normalOrderRel φ (annihilateFilter φs) =
    φ :: annihilateFilter φs
  | [] => by simp [annihilateFilter]
  | φ' :: φs => by
    rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φ') with hφ' | hφ'
    · rw [annihilateFilter_cons_create hφ', orderedInsert_annihilateFilter φ φs]
    · rw [annihilateFilter_cons_annihilate hφ']
      dsimp only [List.orderedInsert.eq_2]
      rw [if_pos]
      dsimp only [normalOrderRel]
      rw [hφ']
      rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φ) with hφ | hφ
      · rw [hφ]
        simp only [CreateAnnihilate.normalOrder]
      · rw [hφ]
        simp [CreateAnnihilate.normalOrder]

lemma orderedInsert_createFilter_append_annihilateFilter_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnStates) :
    List.orderedInsert normalOrderRel φ (createFilter φs ++ annihilateFilter φs) =
    createFilter φs ++ φ :: annihilateFilter φs := by
  rw [orderedInsert_createFilter_append_annihilate φ hφ, orderedInsert_annihilateFilter]

lemma normalOrderList_eq_createFilter_append_annihilateFilter : (φs : List 𝓕.CrAnStates) →
    normalOrderList φs = createFilter φs ++ annihilateFilter φs
  | [] => by simp [normalOrderList, createFilter, annihilateFilter]
  | φ :: φs => by
    by_cases hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create
    · rw [normalOrderList_cons_create φ hφ φs]
      dsimp only [createFilter]
      rw [List.filter_cons_of_pos]
      swap
      simp only [hφ, decide_true]
      dsimp only [annihilateFilter, List.cons_append]
      rw [List.filter_cons_of_neg]
      swap
      simp only [hφ, reduceCtorEq, decide_false, Bool.false_eq_true, not_false_eq_true]
      rw [normalOrderList_eq_createFilter_append_annihilateFilter φs]
      rfl
    · dsimp only [normalOrderList, List.insertionSort]
      rw [← normalOrderList]
      have hφ' : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate := by
        have hx := CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φ)
        simp_all
      rw [normalOrderList_eq_createFilter_append_annihilateFilter φs]
      rw [orderedInsert_createFilter_append_annihilateFilter_annihilate φ hφ']
      rw [createFilter_cons_annihilate hφ', annihilateFilter_cons_annihilate hφ']

end FieldStruct
