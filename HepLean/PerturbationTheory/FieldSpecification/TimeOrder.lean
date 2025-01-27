/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List.InsertionSort
import HepLean.PerturbationTheory.FieldSpecification.NormalOrder
/-!

# Time ordering of states

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-!

## Time ordering for states

-/

/-- The time ordering relation on states. We have that `timeOrderRel φ0 φ1` is true
  if and only if `φ1` has a time less-then or equal to `φ0`, or `φ1` is a negative
  asymptotic state, or `φ0` is a positive asymptotic state. -/
def timeOrderRel : 𝓕.States → 𝓕.States → Prop
  | States.outAsymp _, _ => True
  | States.position φ0, States.position φ1 => φ1.2 0 ≤ φ0.2 0
  | States.position _, States.inAsymp _ => True
  | States.position _, States.outAsymp _ => False
  | States.inAsymp _, States.outAsymp _ => False
  | States.inAsymp _, States.position _ => False
  | States.inAsymp _, States.inAsymp _ => True

/-- The relation `timeOrderRel` is decidable, but not computablly so due to
  `Real.decidableLE`. -/
noncomputable instance : (φ φ' : 𝓕.States) → Decidable (timeOrderRel φ φ')
  | States.outAsymp _, _ => isTrue True.intro
  | States.position φ0, States.position φ1 => inferInstanceAs (Decidable (φ1.2 0 ≤ φ0.2 0))
  | States.position _, States.inAsymp _ => isTrue True.intro
  | States.position _, States.outAsymp _ => isFalse (fun a => a)
  | States.inAsymp _, States.outAsymp _ => isFalse (fun a => a)
  | States.inAsymp _, States.position _ => isFalse (fun a => a)
  | States.inAsymp _, States.inAsymp _ => isTrue True.intro

/-- Time ordering is total. -/
instance : IsTotal 𝓕.States 𝓕.timeOrderRel where
  total a b := by
    cases a <;> cases b <;>
      simp only [or_self, or_false, or_true, timeOrderRel, Fin.isValue, implies_true, imp_self,
        IsEmpty.forall_iff]
    exact LinearOrder.le_total _ _

/-- Time ordering is transitive. -/
instance : IsTrans 𝓕.States 𝓕.timeOrderRel where
  trans a b c := by
    cases a <;> cases b <;> cases c <;>
      simp only [timeOrderRel, Fin.isValue, implies_true, imp_self, IsEmpty.forall_iff]
    exact fun h1 h2 => Preorder.le_trans _ _ _ h2 h1

noncomputable section

open FieldStatistic
open HepLean.List

/-- Given a list `φ :: φs` of states, the (zero-based) position of the state which is
  of maximum time. For example
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `1`.
  This is defined for a list `φ :: φs` instead of `φs` to ensure that such a position exists.
-/
def maxTimeFieldPos (φ : 𝓕.States) (φs : List 𝓕.States) : ℕ :=
  insertionSortMinPos timeOrderRel φ φs

lemma maxTimeFieldPos_lt_length (φ : 𝓕.States) (φs : List 𝓕.States) :
    maxTimeFieldPos φ φs < (φ :: φs).length := by
  simp [maxTimeFieldPos]

/-- Given a list `φ :: φs` of states, the left-most state of maximum time, if there are more.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `φ2(t = 5)`.
  It is the state at the position `maxTimeFieldPos φ φs`.
-/
def maxTimeField (φ : 𝓕.States) (φs : List 𝓕.States) : 𝓕.States :=
  insertionSortMin timeOrderRel φ φs

/-- Given a list `φ :: φs` of states, the list with the left-most state of maximum
  time removed.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return
    `[φ1(t = 4), φ3(t = 3), φ4(t = 5)]`.
-/
def eraseMaxTimeField (φ : 𝓕.States) (φs : List 𝓕.States) : List 𝓕.States :=
  insertionSortDropMinPos timeOrderRel φ φs

@[simp]
lemma eraseMaxTimeField_length (φ : 𝓕.States) (φs : List 𝓕.States) :
    (eraseMaxTimeField φ φs).length = φs.length := by
  simp [eraseMaxTimeField, insertionSortDropMinPos, eraseIdx_length']

lemma maxTimeFieldPos_lt_eraseMaxTimeField_length_succ (φ : 𝓕.States) (φs : List 𝓕.States) :
    maxTimeFieldPos φ φs < (eraseMaxTimeField φ φs).length.succ := by
  simp only [eraseMaxTimeField_length, Nat.succ_eq_add_one]
  exact maxTimeFieldPos_lt_length φ φs

/-- Given a list `φ :: φs` of states, the position of the left-most state of maximum
  time as an eement of `Fin (eraseMaxTimeField φ φs).length.succ`.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `⟨1,...⟩`.
-/
def maxTimeFieldPosFin (φ : 𝓕.States) (φs : List 𝓕.States) :
    Fin (eraseMaxTimeField φ φs).length.succ :=
  insertionSortMinPosFin timeOrderRel φ φs

lemma lt_maxTimeFieldPosFin_not_timeOrder (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin (eraseMaxTimeField φ φs).length)
    (hi : (maxTimeFieldPosFin φ φs).succAbove i < maxTimeFieldPosFin φ φs) :
    ¬ timeOrderRel ((eraseMaxTimeField φ φs)[i.val]) (maxTimeField φ φs) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt timeOrderRel φ φs i hi

lemma timeOrder_maxTimeField (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin (eraseMaxTimeField φ φs).length) :
    timeOrderRel (maxTimeField φ φs) ((eraseMaxTimeField φ φs)[i.val]) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos timeOrderRel φ φs _

/-- The sign associated with putting a list of states into time order (with
  the state of greatest time to the left).
  We pick up a minus sign for every fermion paired crossed. -/
def timeOrderSign (φs : List 𝓕.States) : ℂ :=
  Wick.koszulSign 𝓕.statesStatistic 𝓕.timeOrderRel φs

@[simp]
lemma timeOrderSign_nil : timeOrderSign (𝓕 := 𝓕) [] = 1 := by
  simp only [timeOrderSign]
  rfl

lemma timeOrderSign_pair_ordered {φ ψ : 𝓕.States} (h : timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 1 := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, ite_eq_left_iff,
    ite_eq_right_iff, and_imp]
  exact fun h' => False.elim (h' h)

lemma timeOrderSign_pair_not_ordered {φ ψ : 𝓕.States} (h : ¬ timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, instCommGroup.eq_1]
  rw [if_neg h]
  simp [FieldStatistic.exchangeSign_eq_if]

lemma timerOrderSign_of_eraseMaxTimeField (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrderSign (eraseMaxTimeField φ φs) = timeOrderSign (φ :: φs) *
    𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ (φ :: φs).take (maxTimeFieldPos φ φs)) := by
  rw [eraseMaxTimeField, insertionSortDropMinPos, timeOrderSign,
    Wick.koszulSign_eraseIdx_insertionSortMinPos]
  rw [← timeOrderSign, ← maxTimeField]
  rfl

/-- The time ordering of a list of states. A schematic example is:
  - `normalOrderList [φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` is equal to
    `[φ2(t = 5), φ4(t = 5), φ1(t = 4), φ3(t = 3)]` -/
def timeOrderList (φs : List 𝓕.States) : List 𝓕.States :=
  List.insertionSort 𝓕.timeOrderRel φs

lemma timeOrderList_pair_ordered {φ ψ : 𝓕.States} (h : timeOrderRel φ ψ) :
    timeOrderList [φ, ψ] = [φ, ψ] := by
  simp only [timeOrderList, List.insertionSort, List.orderedInsert, ite_eq_left_iff,
    List.cons.injEq, and_true]
  exact fun h' => False.elim (h' h)

lemma timeOrderList_pair_not_ordered {φ ψ : 𝓕.States} (h : ¬ timeOrderRel φ ψ) :
    timeOrderList [φ, ψ] = [ψ, φ] := by
  simp only [timeOrderList, List.insertionSort, List.orderedInsert, ite_eq_right_iff,
    List.cons.injEq, and_true]
  exact fun h' => False.elim (h h')

@[simp]
lemma timeOrderList_nil : timeOrderList (𝓕 := 𝓕) [] = [] := by
  simp [timeOrderList]

lemma timeOrderList_eq_maxTimeField_timeOrderList (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrderList (φ :: φs) = maxTimeField φ φs :: timeOrderList (eraseMaxTimeField φ φs) := by
  exact insertionSort_eq_insertionSortMin_cons timeOrderRel φ φs

/-!

## Time ordering for CrAnStates

-/

/-!

## timeOrderRel

-/

/-- The time ordering relation on CrAnStates. -/
def crAnTimeOrderRel (a b : 𝓕.CrAnStates) : Prop := 𝓕.timeOrderRel a.1 b.1

/-- The relation `crAnTimeOrderRel` is decidable, but not computablly so due to
  `Real.decidableLE`. -/
noncomputable instance (φ φ' : 𝓕.CrAnStates) : Decidable (crAnTimeOrderRel φ φ') :=
  inferInstanceAs (Decidable (𝓕.timeOrderRel φ.1 φ'.1))

/-- Time ordering of `CrAnStates` is total. -/
instance : IsTotal 𝓕.CrAnStates 𝓕.crAnTimeOrderRel where
  total a b := IsTotal.total (r := 𝓕.timeOrderRel) a.1 b.1

/-- Time ordering of `CrAnStates` is transitive. -/
instance : IsTrans 𝓕.CrAnStates 𝓕.crAnTimeOrderRel where
  trans a b c := IsTrans.trans (r := 𝓕.timeOrderRel) a.1 b.1 c.1

/-- The sign associated with putting a list of `CrAnStates` into time order (with
  the state of greatest time to the left).
  We pick up a minus sign for every fermion paired crossed. -/
def crAnTimeOrderSign (φs : List 𝓕.CrAnStates) : ℂ :=
  Wick.koszulSign 𝓕.crAnStatistics 𝓕.crAnTimeOrderRel φs

@[simp]
lemma crAnTimeOrderSign_nil : crAnTimeOrderSign (𝓕 := 𝓕) [] = 1 := by
  simp only [crAnTimeOrderSign]
  rfl

/-- Sort a list of `CrAnStates` based on `crAnTimeOrderRel`. -/
def crAnTimeOrderList (φs : List 𝓕.CrAnStates) : List 𝓕.CrAnStates :=
  List.insertionSort 𝓕.crAnTimeOrderRel φs

@[simp]
lemma crAnTimeOrderList_nil : crAnTimeOrderList (𝓕 := 𝓕) [] = [] := by
  simp [crAnTimeOrderList]

/-!

## Relationship to sections
-/

lemma koszulSignInsert_crAnTimeOrderRel_crAnSection {φ : 𝓕.States} {ψ : 𝓕.CrAnStates}
    (h : ψ.1 = φ) : {φs : List 𝓕.States} → (ψs : CrAnSection φs) →
    Wick.koszulSignInsert 𝓕.crAnStatistics 𝓕.crAnTimeOrderRel ψ ψs.1 =
    Wick.koszulSignInsert 𝓕.statesStatistic 𝓕.timeOrderRel φ φs
  | [], ⟨[], h⟩ => by
    simp [Wick.koszulSignInsert]
  | φ' :: φs, ⟨ψ' :: ψs, h1⟩ => by
    simp only [Wick.koszulSignInsert, crAnTimeOrderRel, h]
    simp only [List.map_cons, List.cons.injEq] at h1
    have hi := koszulSignInsert_crAnTimeOrderRel_crAnSection h (φs := φs) ⟨ψs, h1.2⟩
    rw [hi]
    congr
    · exact h1.1
    · simp only [crAnStatistics, crAnStatesToStates, Function.comp_apply]
      congr
    · simp only [crAnStatistics, crAnStatesToStates, Function.comp_apply]
      congr
      exact h1.1

@[simp]
lemma crAnTimeOrderSign_crAnSection : {φs : List 𝓕.States} → (ψs : CrAnSection φs) →
    crAnTimeOrderSign ψs.1 = timeOrderSign φs
  | [], ⟨[], h⟩ => by
    simp
  | φ :: φs, ⟨ψ :: ψs, h⟩ => by
    simp only [crAnTimeOrderSign, Wick.koszulSign, timeOrderSign]
    simp only [List.map_cons, List.cons.injEq] at h
    congr 1
    · rw [koszulSignInsert_crAnTimeOrderRel_crAnSection h.1 ⟨ψs, h.2⟩]
    · exact crAnTimeOrderSign_crAnSection ⟨ψs, h.2⟩

lemma orderedInsert_crAnTimeOrderRel_crAnSection {φ : 𝓕.States} {ψ : 𝓕.CrAnStates}
    (h : ψ.1 = φ) : {φs : List 𝓕.States} → (ψs : CrAnSection φs) →
    (List.orderedInsert 𝓕.crAnTimeOrderRel ψ ψs.1).map 𝓕.crAnStatesToStates =
    List.orderedInsert 𝓕.timeOrderRel φ φs
  | [], ⟨[], _⟩ => by
    simp only [List.orderedInsert, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact h
  | φ' :: φs, ⟨ψ' :: ψs, h1⟩ => by
    simp only [List.orderedInsert, crAnTimeOrderRel, h]
    simp only [List.map_cons, List.cons.injEq] at h1
    by_cases hr : timeOrderRel φ φ'
    · simp only [hr, ↓reduceIte]
      rw [← h1.1] at hr
      simp only [crAnStatesToStates] at hr
      simp only [hr, ↓reduceIte, List.map_cons, List.cons.injEq]
      exact And.intro h (And.intro h1.1 h1.2)
    · simp only [hr, ↓reduceIte]
      rw [← h1.1] at hr
      simp only [crAnStatesToStates] at hr
      simp only [hr, ↓reduceIte, List.map_cons, List.cons.injEq]
      apply And.intro h1.1
      exact orderedInsert_crAnTimeOrderRel_crAnSection h ⟨ψs, h1.2⟩

lemma crAnTimeOrderList_crAnSection_is_crAnSection : {φs : List 𝓕.States} → (ψs : CrAnSection φs) →
    (crAnTimeOrderList ψs.1).map 𝓕.crAnStatesToStates = timeOrderList φs
  | [], ⟨[], h⟩ => by
    simp
  | φ :: φs, ⟨ψ :: ψs, h⟩ => by
    simp only [crAnTimeOrderList, List.insertionSort, timeOrderList]
    simp only [List.map_cons, List.cons.injEq] at h
    exact orderedInsert_crAnTimeOrderRel_crAnSection h.1 ⟨(List.insertionSort crAnTimeOrderRel ψs),
      crAnTimeOrderList_crAnSection_is_crAnSection ⟨ψs, h.2⟩⟩

/-- Time ordering of sections of a list of states. -/
def crAnSectionTimeOrder (φs : List 𝓕.States) (ψs : CrAnSection φs) :
    CrAnSection (timeOrderList φs) :=
  ⟨crAnTimeOrderList ψs.1, crAnTimeOrderList_crAnSection_is_crAnSection ψs⟩

lemma orderedInsert_crAnTimeOrderRel_injective {ψ ψ' : 𝓕.CrAnStates} (h : ψ.1 = ψ'.1) :
    {φs : List 𝓕.States} → (ψs ψs' : 𝓕.CrAnSection φs) →
    (ho : List.orderedInsert crAnTimeOrderRel ψ ψs.1 =
    List.orderedInsert crAnTimeOrderRel ψ' ψs'.1) → ψ = ψ' ∧ ψs = ψs'
  | [], ⟨[], _⟩, ⟨[], _⟩, h => by
    simp only [List.orderedInsert, List.cons.injEq, and_true] at h
    simpa using h
  | φ :: φs, ⟨ψ1 :: ψs, h1⟩, ⟨ψ1' :: ψs', h1'⟩, ho => by
    simp only [List.map_cons, List.cons.injEq] at h1 h1'
    have ih := orderedInsert_crAnTimeOrderRel_injective h ⟨ψs, h1.2⟩ ⟨ψs', h1'.2⟩
    simp only [List.orderedInsert] at ho
    by_cases hr : crAnTimeOrderRel ψ ψ1
    · simp_all only [ite_true]
      by_cases hr2 : crAnTimeOrderRel ψ' ψ1'
      · simp_all
      · simp only [crAnTimeOrderRel] at hr hr2
        simp_all only
        rw [crAnStatesToStates] at h1 h1'
        rw [h1.1] at hr
        rw [h1'.1] at hr2
        exact False.elim (hr2 hr)
    · simp_all only [ite_false]
      by_cases hr2 : crAnTimeOrderRel ψ' ψ1'
      · simp only [crAnTimeOrderRel] at hr hr2
        simp_all only
        rw [crAnStatesToStates] at h1 h1'
        rw [h1.1] at hr
        rw [h1'.1] at hr2
        exact False.elim (hr hr2)
      · simp only [hr2, ↓reduceIte, List.cons.injEq] at ho
        have ih' := ih ho.2
        simp_all only [and_self, implies_true, not_false_eq_true, true_and]
        apply Subtype.ext
        simp only [List.cons.injEq, true_and]
        rw [Subtype.eq_iff] at ih'
        exact ih'.2

lemma crAnSectionTimeOrder_injective : {φs : List 𝓕.States} →
    Function.Injective (𝓕.crAnSectionTimeOrder φs)
  | [], ⟨[], _⟩, ⟨[], _⟩ => by
    simp
  | φ :: φs, ⟨ψ :: ψs, h⟩, ⟨ψ' :: ψs', h'⟩ => by
    intro h1
    apply Subtype.ext
    simp only [List.cons.injEq]
    simp only [crAnSectionTimeOrder] at h1
    rw [Subtype.eq_iff] at h1
    simp only [crAnTimeOrderList, List.insertionSort] at h1
    simp only [List.map_cons, List.cons.injEq] at h h'
    rw [crAnStatesToStates] at h h'
    have hin := orderedInsert_crAnTimeOrderRel_injective (by rw [h.1, h'.1])
      (𝓕.crAnSectionTimeOrder φs ⟨ψs, h.2⟩)
      (𝓕.crAnSectionTimeOrder φs ⟨ψs', h'.2⟩) h1
    apply And.intro hin.1
    have hl := crAnSectionTimeOrder_injective hin.2
    rw [Subtype.ext_iff] at hl
    simpa using hl

lemma crAnSectionTimeOrder_bijective (φs : List 𝓕.States) :
    Function.Bijective (𝓕.crAnSectionTimeOrder φs) := by
  rw [Fintype.bijective_iff_injective_and_card]
  apply And.intro crAnSectionTimeOrder_injective
  apply CrAnSection.card_perm_eq
  simp only [timeOrderList]
  exact List.Perm.symm (List.perm_insertionSort timeOrderRel φs)

lemma sum_crAnSections_timeOrder {φs : List 𝓕.States} [AddCommMonoid M]
    (f : CrAnSection (timeOrderList φs) → M) : ∑ s, f s = ∑ s, f (𝓕.crAnSectionTimeOrder φs s) := by
  erw [(Equiv.ofBijective _ (𝓕.crAnSectionTimeOrder_bijective φs)).sum_comp]

/-!

## normTimeOrderRel

-/

/-- The time ordering relation on `CrAnStates` such that if two CrAnStates have the same
  time, we normal order them. -/
def normTimeOrderRel (a b : 𝓕.CrAnStates) : Prop :=
  crAnTimeOrderRel a b ∧ (crAnTimeOrderRel b a → normalOrderRel a b)

/-- The relation `normTimeOrderRel` is decidable, but not computablly so due to
  `Real.decidableLE`. -/
noncomputable instance (φ φ' : 𝓕.CrAnStates) : Decidable (normTimeOrderRel φ φ') :=
  instDecidableAnd

/-- Norm-Time ordering of `CrAnStates` is total. -/
instance : IsTotal 𝓕.CrAnStates 𝓕.normTimeOrderRel where
  total a b := by
    simp only [normTimeOrderRel]
    match IsTotal.total (r := 𝓕.crAnTimeOrderRel) a b,
      IsTotal.total (r := 𝓕.normalOrderRel) a b with
    | Or.inl h1, Or.inl h2 => simp [h1, h2]
    | Or.inr h1, Or.inl h2 =>
      simp only [h1, h2, imp_self, and_true, true_and]
      by_cases hn : crAnTimeOrderRel a b
      · simp [hn]
      · simp [hn]
    | Or.inl h1, Or.inr h2 =>
      simp only [h1, true_and, h2, imp_self, and_true]
      by_cases hn : crAnTimeOrderRel b a
      · simp [hn]
      · simp [hn]
    | Or.inr h1, Or.inr h2 => simp [h1, h2]

/-- Norm-Time ordering of `CrAnStates` is transitive. -/
instance : IsTrans 𝓕.CrAnStates 𝓕.normTimeOrderRel where
  trans a b c := by
    intro h1 h2
    simp_all only [normTimeOrderRel]
    apply And.intro
    · exact IsTrans.trans _ _ _ h1.1 h2.1
    · intro hc
      refine IsTrans.trans _ _ _ (h1.2 ?_) (h2.2 ?_)
      · exact IsTrans.trans _ _ _ h2.1 hc
      · exact IsTrans.trans _ _ _ hc h1.1

/-- The sign associated with putting a list of `CrAnStates` into normal-time order (with
  the state of greatest time to the left).
  We pick up a minus sign for every fermion paired crossed. -/
def normTimeOrderSign (φs : List 𝓕.CrAnStates) : ℂ :=
  Wick.koszulSign 𝓕.crAnStatistics 𝓕.normTimeOrderRel φs

/-- Sort a list of `CrAnStates` based on `normTimeOrderRel`. -/
def normTimeOrderList (φs : List 𝓕.CrAnStates) : List 𝓕.CrAnStates :=
  List.insertionSort 𝓕.normTimeOrderRel φs

end
end FieldSpecification
