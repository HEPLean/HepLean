/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
/-!

# Field statistics

Basic properties related to whether a field, or list of fields, is bosonic or fermionic.

-/

/-- A field can either be bosonic or fermionic in nature.
  That is to say, they can either have Bose-Einstein statistics or
  Fermi-Dirac statistics. -/
inductive FieldStatistic : Type where
  | bosonic : FieldStatistic
  | fermionic : FieldStatistic
deriving DecidableEq

namespace FieldStatistic

variable {𝓕 : Type}

@[simp]
instance : CommGroup FieldStatistic where
  one := bosonic
  mul a b :=
    match a, b with
    | bosonic, bosonic => bosonic
    | bosonic, fermionic => fermionic
    | fermionic, bosonic => fermionic
    | fermionic, fermionic => bosonic
  inv a := a
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;>
    dsimp [HMul.hMul]
  one_mul a := by
    cases a <;> dsimp [HMul.hMul]
  mul_one a := by
    cases a <;> dsimp [HMul.hMul]
  inv_mul_cancel a := by
    cases a <;> dsimp [HMul.hMul] <;> rfl
  mul_comm a b := by
    cases a <;> cases b <;> rfl

@[simp]
lemma bosonic_mul_bosonic : bosonic * bosonic = bosonic := rfl

@[simp]
lemma bosonic_mul_fermionic : bosonic * fermionic = fermionic := rfl

@[simp]
lemma fermionic_mul_bosonic : fermionic * bosonic = fermionic := rfl

@[simp]
lemma fermionic_mul_fermionic : fermionic * fermionic = bosonic := rfl

@[simp]
lemma mul_self (a : FieldStatistic) : a * a = 1 := by
  cases a <;> rfl

/-- Field statics form a finite type. -/
instance : Fintype FieldStatistic where
  elems := {bosonic, fermionic}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self bosonic {fermionic}
    · refine Finset.insert_eq_self.mp ?_
      exact rfl

@[simp]
lemma fermionic_not_eq_bonsic : ¬ fermionic = bosonic := by
  intro h
  exact FieldStatistic.noConfusion h

lemma bonsic_eq_fermionic_false : bosonic = fermionic ↔ false := by
  simp only [reduceCtorEq, Bool.false_eq_true]

@[simp]
lemma neq_fermionic_iff_eq_bosonic (a : FieldStatistic) : ¬ a = fermionic ↔ a = bosonic := by
  fin_cases a
  · simp
  · simp

@[simp]
lemma bosonic_neq_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a := by
  fin_cases a
  · simp
  · simp

@[simp]
lemma fermionic_neq_iff_bosonic_eq (a : FieldStatistic) : ¬ fermionic = a ↔ bosonic = a := by
  fin_cases a
  · simp
  · simp

lemma eq_self_if_eq_bosonic {a : FieldStatistic} :
    (if a = bosonic then bosonic else fermionic) = a := by
  fin_cases a <;> rfl

lemma eq_self_if_bosonic_eq {a : FieldStatistic} :
    (if bosonic = a then bosonic else fermionic) = a := by
  fin_cases a <;> rfl

lemma mul_eq_one_iff (a b : FieldStatistic) : a * b = 1 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp

lemma one_eq_mul_iff (a b : FieldStatistic) : 1 = a * b ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp

lemma mul_eq_iff_eq_mul (a b c : FieldStatistic) : a * b = c ↔ a = b * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp
  rfl
  rfl
  rfl

lemma mul_eq_iff_eq_mul' (a b c : FieldStatistic) : a * b = c ↔ b = a * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp
  rfl
  rfl
  rfl
/-- The field statistics of a list of fields is fermionic if ther is an odd number of fermions,
  otherwise it is bosonic. -/
def ofList (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) → FieldStatistic
  | [] => bosonic
  | φ :: φs => if s φ = ofList s φs then bosonic else fermionic

lemma ofList_cons_eq_mul (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    ofList s (φ :: φs) = s φ * ofList s φs := by
  have ha (a b  : FieldStatistic) : (if a = b then bosonic else fermionic) = a * b := by
    fin_cases a <;> fin_cases b <;> rfl
  exact ha (s φ) (ofList s φs)

lemma ofList_eq_prod (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) →
    ofList s φs = (List.map s φs).prod
  | [] => rfl
  | φ :: φs => by
    rw [ofList_cons_eq_mul, List.map_cons, List.prod_cons, ofList_eq_prod]

@[simp]
lemma ofList_singleton (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s [φ] = s φ := by
  simp only [ofList, Fin.isValue]
  rw [eq_self_if_eq_bosonic]

@[simp]
lemma ofList_freeMonoid (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s (FreeMonoid.of φ) = s φ :=
  ofList_singleton s φ

@[simp]
lemma ofList_empty (s : 𝓕 → FieldStatistic) : ofList s [] = bosonic := rfl

@[simp]
lemma ofList_append (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = if ofList s φs = ofList s φs' then bosonic else fermionic := by
  induction φs with
  | nil =>
    simp only [List.nil_append, ofList_empty, Fin.isValue, eq_self_if_bosonic_eq]
  | cons a l ih =>
    have hab (a b c : FieldStatistic) :
        (if a = (if b = c then bosonic else fermionic) then bosonic else fermionic) =
        if (if a = b then bosonic else fermionic) = c then bosonic else fermionic := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
    simp only [ofList, List.append_eq, Fin.isValue, ih, hab]

lemma ofList_append_eq_mul (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = ofList s φs * ofList s φs' := by
  rw [ofList_append]
  have ha (a b  : FieldStatistic) : (if a = b then bosonic else fermionic) = a * b := by
    fin_cases a <;> fin_cases b <;> rfl
  exact ha _ _

lemma ofList_perm (s : 𝓕 → FieldStatistic) {l l' : List 𝓕} (h : l.Perm l') :
    ofList s l = ofList s l' := by
  rw [ofList_eq_prod, ofList_eq_prod]
  exact List.Perm.prod_eq (List.Perm.map s h)

lemma ofList_orderedInsert (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) (φ : 𝓕) : ofList s (List.orderedInsert le1 φ φs) = ofList s (φ :: φs) :=
  ofList_perm s (List.perm_orderedInsert le1 φ φs)

@[simp]
lemma ofList_insertionSort (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) : ofList s (List.insertionSort le1 φs) = ofList s φs :=
  ofList_perm s (List.perm_insertionSort le1 φs)

lemma ofList_map_eq_finset_prod (s : 𝓕 → FieldStatistic) :
    (φs : List 𝓕) → (l : List (Fin φs.length)) → (hl : l.Nodup) →
    ofList s (l.map φs.get) = ∏ (i : Fin φs.length), if i ∈ l then s φs[i] else 1
  | [], [], _ => rfl
  | [], i :: l, hl => Fin.elim0 i
  | φ :: φs, [], hl => by
    simp
    rfl
  | φ :: φs, i :: l, hl => by
    simp
    rw [ofList_cons_eq_mul]
    rw [ofList_map_eq_finset_prod s (φ :: φs) l]
    have h1 : s (φ :: φs)[↑i] = ∏ (j : Fin ( φ :: φs).length),
      if j = i then s (φ :: φs)[↑i] else 1 := by
      rw [Fintype.prod_ite_eq']
    erw [h1]
    rw [← Finset.prod_mul_distrib]
    congr
    funext a
    simp
    by_cases ha : a = i
    · simp [ha]
      rw [if_neg]
      rfl
      simp at hl
      exact hl.1
    · simp [ha]
      rfl
    simp at hl
    exact hl.2

def pairedSign : FieldStatistic →* FieldStatistic →* ℂ where
  toFun a :=
    {
      toFun := fun b =>
        match a, b with
        | bosonic, _ => 1
        | _, bosonic => 1
        | fermionic, fermionic => -1
      map_one' := by
        fin_cases a
        <;> simp
      map_mul' := fun c b => by
        fin_cases a <;>
          fin_cases b <;>
          fin_cases c <;>
          simp
    }
  map_one' := by
    ext b
    fin_cases b
    <;> simp
  map_mul' c b := by
    ext a
    fin_cases a
    <;> fin_cases b <;> fin_cases c
    <;> simp

scoped[FieldStatistic] notation "𝓢(" a "," b ")" => pairedSign a b

@[simp]
lemma pairedSign_bosonic (a : FieldStatistic) : 𝓢(a, bosonic) = 1 := by
  fin_cases a <;> rfl

@[simp]
lemma bosonic_pairedSign (a : FieldStatistic) : 𝓢(bosonic, a) = 1 := by
  fin_cases a <;> rfl

lemma pairedSign_symm (a b : FieldStatistic) : 𝓢(a, b) = 𝓢(b, a) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma pairedSign_eq_if (a b : FieldStatistic) :
    𝓢(a, b) = if a = fermionic ∧ b = fermionic then - 1 else 1 := by
  fin_cases a <;> fin_cases b <;> rfl

@[simp]
lemma pairedSign_mul_self (a b : FieldStatistic) : 𝓢(a, b) * 𝓢(a, b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [pairedSign]

@[simp]
lemma pairedSign_mul_self_swap (a b : FieldStatistic) : 𝓢(a, b) * 𝓢(b, a) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [pairedSign]

lemma pairedSign_ofList_cons (a : FieldStatistic)
      (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    𝓢(a, ofList s (φ :: φs)) = 𝓢(a, s φ) * 𝓢(a, ofList s φs) := by
  rw [ofList_cons_eq_mul, map_mul]

end FieldStatistic
