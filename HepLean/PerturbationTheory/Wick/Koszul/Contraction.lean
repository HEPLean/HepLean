/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
import HepLean.Lorentz.RealVector.Basic
import HepLean.Mathematics.Fin
import HepLean.SpaceTime.Basic
import HepLean.Mathematics.SuperAlgebra.Basic
import HepLean.Mathematics.List
import HepLean.Meta.Notes.Basic
import Init.Data.List.Sort.Basic
import Mathlib.Data.Fin.Tuple.Take
import HepLean.PerturbationTheory.Wick.Koszul.OperatorMap
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section

def optionErase {I : Type} (l : List I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => l
  | some i => List.eraseIdx l i

inductive ContractionsAux {I : Type} : (l : List I) → (aux : List I) → Type
  | nil : ContractionsAux [] []
  | single {a : I} : ContractionsAux [a] [a]
  | cons {l : List I} {aux : List I} {a b: I} (i : Option (Fin (b :: aux).length)) :
    ContractionsAux (b :: l) aux → ContractionsAux (a :: b :: l) (optionErase (b :: aux) i)

def Contractions {I : Type} (l : List I) : Type := Σ aux, ContractionsAux l aux

namespace Contractions

variable {I : Type} {l : List I} (c : Contractions l)

def normalize : List I := c.1

lemma normalize_length_le : c.normalize.length ≤ l.length := by
  cases c
  rename_i aux c
  induction c with
  | nil =>
    simp [normalize]
  | single =>
    simp [normalize]
  | cons i c ih =>
    simp [normalize, optionErase]
    match i with
    | none =>
      simpa using ih
    | some i =>
      simp
      rw [List.length_eraseIdx]
      simp [normalize] at ih
      simp
      exact Nat.le_add_right_of_le ih

lemma contractions_nil (a : Contractions ([] : List I)) : a = ⟨[], ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

lemma contractions_single {i : I} (a : Contractions [i]) : a = ⟨[i], ContractionsAux.single⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

def consConsEquiv {a b : I} {l : List I} :
    Contractions (a :: b :: l) ≃ (c : Contractions (b :: l)) × Option (Fin (b :: c.normalize).length) where
  toFun c :=
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (aux := aux') i c => ⟨⟨aux', c⟩, i⟩
  invFun ci :=
    ⟨(optionErase (b :: ci.fst.normalize) ci.2), ContractionsAux.cons (a := a) ci.2 ci.1.2⟩
  left_inv c := by
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (aux := aux') i c => rfl
  right_inv ci := by rfl

instance decidable : (l : List I) → DecidableEq (Contractions l)
  | [] => fun a b =>
    match a, b with
    | ⟨_, a⟩, ⟨_, b⟩ =>
    match a, b with
    | ContractionsAux.nil , ContractionsAux.nil => isTrue rfl
  | _ :: [] => fun a b =>
    match a, b with
    | ⟨_, a⟩, ⟨_, b⟩ =>
    match a, b with
    | ContractionsAux.single , ContractionsAux.single => isTrue rfl
  | _ :: b :: l =>
    haveI : DecidableEq (Contractions (b :: l)) := decidable (b :: l)
    haveI : DecidableEq ((c : Contractions (b :: l)) × Option (Fin (b :: c.normalize).length)) :=
      Sigma.instDecidableEqSigma
    Equiv.decidableEq consConsEquiv

instance fintype  : (l : List I) → Fintype (Contractions l)
  | [] => {
    elems := {⟨[], ContractionsAux.nil⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_nil a}
  | a :: [] => {
    elems := {⟨[a], ContractionsAux.single⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_single a}
  | a :: b :: l =>
    haveI : Fintype (Contractions (b :: l)) := fintype (b :: l)
    haveI : Fintype ((c : Contractions (b :: l)) × Option (Fin (b :: c.normalize).length)) :=
      Sigma.instFintype
    Fintype.ofEquiv _ consConsEquiv.symm

-- This definition is not correct.
def superCommuteTermAux {l : List I} {aux : List I} : (c : ContractionsAux l aux)  → FreeAlgebra ℂ I
  | ContractionsAux.nil => 1
  | ContractionsAux.single => 1
  | ContractionsAux.cons i c => superCommuteTermAux c

def superCommuteTerm {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    {r : List I} (c : Contractions r) : FreeAlgebra ℂ (Σ i, f i) :=
    freeAlgebraMap f (superCommuteTermAux c.2)

lemma superCommuteTerm_center {f : I → Type} [∀ i, Fintype (f i)]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [SuperCommuteCenterMap F] :
    F (c.superCommuteTerm) ∈ Subalgebra.center ℂ A := by
  sorry

def toTerm {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) {r : List I}
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    (c : Contractions r) : FreeAlgebra ℂ (Σ i, f i) :=
  c.superCommuteTerm * koszulOrder le1 (fun i => q i.fst) (ofListM f c.normalize 1)

lemma toTerm_nil {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
     : toTerm q le1 (⟨[], ContractionsAux.nil⟩ : Contractions [])  = 1 := by
  simp [toTerm, normalize]
  rw [ofListM_empty]
  simp
  sorry

end Contractions

lemma wick_cons_cons {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    (tle : I → I → Prop) [DecidableRel tle]
    (i : (Σ i, f i)) (hi : ∀ j, le1 j i)
    {A : Type} [Semiring A] [Algebra ℂ A] (r : List I) (b a : I)
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [SuperCommuteCenterMap F]
    (bn bp : (Σ i, f i))
    (hb : ofListM f [b] 1 = ofList [bn] 1 + ofList [bp] 1)
    (ih : F (ofListM f (a :: r) 1) = ∑ c : Contractions (a :: r), F (c.toTerm q le1)) :
    F (ofListM f (b :: a :: r) 1) =  ∑ c : Contractions (b :: a :: r),  F (c.toTerm q le1)  := by
  rw [ofListM_cons_eq_ofListM, map_mul]
  rw [ih]
  rw [Finset.mul_sum]
  rw  [← Contractions.consConsEquiv.symm.sum_comp]
  simp
  erw [Finset.sum_sigma]
  congr
  funext c
  rw [Contractions.toTerm]
  rw [map_mul, ← mul_assoc]
  have hi := c.superCommuteTerm_center F
  rw [Subalgebra.mem_center_iff] at hi
  rw [hi]
  rw [mul_assoc]
  rw [← map_mul]
  rw [hb]
  rw [add_mul]
  rw [ofList_singleton, mul_koszulOrder_le, ← ofList_singleton]
  rw [map_add]
  conv_lhs =>
    rhs
    rhs
    rw [ofList_singleton]
  rw [le_all_mul_koszulOrder]
  rw [← add_assoc]
  rw [← map_add, ← map_add]
  conv_lhs =>
    rhs
    rw [← map_add]
    rw [← add_mul]
    rw [← ofList_singleton]
    rw [← hb]
    rw [map_add]
  rw [mul_add]
  conv_lhs =>
    rhs
    rw [superCommute_ofList_ofListM_sum]

  sorry



end
end Wick
