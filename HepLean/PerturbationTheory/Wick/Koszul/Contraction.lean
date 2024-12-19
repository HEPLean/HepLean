/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Koszul.OperatorMap
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section

open HepLean.List

inductive ContractionsAux {I : Type} : (l : List I) → (aux : List I) → Type
  | nil : ContractionsAux [] []
  | cons {l : List I} {aux : List I} {a : I} (i : Option (Fin aux.length)) :
    ContractionsAux l aux → ContractionsAux (a :: l) (optionEraseZ aux a i)

def Contractions {I : Type} (l : List I) : Type := Σ aux, ContractionsAux l aux

namespace Contractions

variable {I : Type} {l : List I} (c : Contractions l)

def normalize : List I := c.1


lemma contractions_nil (a : Contractions ([] : List I)) : a = ⟨[], ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

lemma contractions_single {i : I} (a : Contractions [i]) : a =
   ⟨[i], ContractionsAux.cons none  ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rename_i aux' c'
  cases c'
  cases aux'
  simp [optionEraseZ]
  rename_i x
  exact Fin.elim0 x

def nilEquiv : Contractions ([] : List I) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], ContractionsAux.nil⟩
  left_inv a := by
    exact Eq.symm (contractions_nil a)
  right_inv _ := by
    rfl

def consEquiv {a : I} {l : List I} :
    Contractions (a :: l) ≃ (c : Contractions l) × Option (Fin (c.normalize).length) where
  toFun c :=
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (aux := aux') i c => ⟨⟨aux', c⟩, i⟩
  invFun ci :=
    ⟨(optionEraseZ (ci.fst.normalize) a ci.2), ContractionsAux.cons (a := a) ci.2 ci.1.2⟩
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
  | _  :: l =>
    haveI : DecidableEq (Contractions l) := decidable l
    haveI : DecidableEq ((c : Contractions l) × Option (Fin (c.normalize).length)) :=
      Sigma.instDecidableEqSigma
    Equiv.decidableEq consEquiv

instance fintype  : (l : List I) → Fintype (Contractions l)
  | [] => {
    elems := {⟨[], ContractionsAux.nil⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_nil a}
  | a  :: l =>
    haveI : Fintype (Contractions l) := fintype l
    haveI : Fintype ((c : Contractions l) × Option (Fin (c.normalize).length)) :=
      Sigma.instFintype
    Fintype.ofEquiv _ consEquiv.symm


structure Splitting {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1] where
  𝓑n :  I → (Σ i, f i)
  𝓑p :  I → (Σ i, f i)
  𝓧n :  I → ℂ
  𝓧p :  I → ℂ
  h𝓑 : ∀ i, ofListM f [i] 1 = ofList [𝓑n i] (𝓧n i) + ofList [𝓑p i] (𝓧p i)
  h𝓑n : ∀ i j, le1 (𝓑n i) j
  h𝓑p : ∀ i j, le1 j (𝓑p i)

def toCenterTerm {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F]
     : {r : List I} → (c : Contractions r) →  (S : Splitting f le1) →  A
  | [], ⟨[], .nil⟩, _ => 1
  | _ :: _, ⟨_, .cons (aux := aux') none c⟩, S => toCenterTerm f q le1 F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons  (aux := aux') (some n) c⟩, S => toCenterTerm f q le1 F ⟨aux', c⟩ S *
    superCommuteCoef q [aux'.get n] (List.take (↑n) aux') •
      F (((superCommute fun i => q i.fst) (ofList [S.𝓑p a] (S.𝓧p a))) (ofListM f [aux'.get n] 1))

lemma toCenterTerm_none {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (q : I → Fin 2) {r : List I}
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1  F]
    (S : Splitting f le1)  (a  : I) (c : Contractions r) :
  toCenterTerm (r :=  a :: r) f q le1 F (Contractions.consEquiv.symm ⟨c, none⟩) S = toCenterTerm f q le1 F c S := by
  rw [consEquiv]
  simp [optionErase]
  dsimp [toCenterTerm]
  rfl

lemma toCenterTerm_center {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F]
     : {r : List I} → (c : Contractions r) →  (S : Splitting f le1) →
    (c.toCenterTerm f q le1 F S) ∈ Subalgebra.center ℂ A
  | [], ⟨[], .nil⟩, _ => by
    dsimp [toCenterTerm]
    exact Subalgebra.one_mem (Subalgebra.center ℂ A)
  | _ :: _, ⟨_, .cons (aux := aux') none c⟩, S => by
    dsimp [toCenterTerm]
    exact toCenterTerm_center f q le1 F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons  (aux := aux') (some n) c⟩, S => by
    dsimp [toCenterTerm]
    refine Subalgebra.mul_mem (Subalgebra.center ℂ A) ?hx ?hy
    exact toCenterTerm_center f q le1 F ⟨aux', c⟩ S
    apply Subalgebra.smul_mem
    rw [ofListM_expand]
    rw [map_sum, map_sum]
    refine Subalgebra.sum_mem (Subalgebra.center ℂ A) ?hy.hx.h
    intro x _
    simp [CreatAnnilateSect.toList]
    rw [ofList_singleton]
    exact OperatorMap.superCommute_ofList_singleton_ι_center (q := fun i => q i.1) (le1 := le1) F (S.𝓑p a) ⟨aux'[↑n], x.head⟩

end Contractions

lemma static_wick_nil {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F]
    (S : Contractions.Splitting f le1) :
    F (ofListM f [] 1) = ∑ c : Contractions [],
    c.toCenterTerm f q le1 F S * F (koszulOrder le1 (fun i => q i.fst) (ofListM f c.normalize 1))  := by
  rw [← Contractions.nilEquiv.symm.sum_comp]
  simp [Contractions.nilEquiv]
  dsimp [Contractions.normalize, Contractions.toCenterTerm]
  simp [ofListM_empty]

lemma static_wick_cons {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    [IsTrans ((i : I) × f i) le1] [IsTotal ((i : I) × f i) le1]
    {A : Type} [Semiring A] [Algebra ℂ A] (r : List I) (a : I)
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F]
    (S : Contractions.Splitting f le1)
    (ih : F (ofListM f r 1) =
    ∑ c : Contractions r, c.toCenterTerm f q le1 F S * F (koszulOrder le1 (fun i => q i.fst) (ofListM f c.normalize 1))) :
    F (ofListM f (a :: r) 1) =  ∑ c : Contractions ( a :: r),
      c.toCenterTerm f q le1 F S * F (koszulOrder le1 (fun i => q i.fst) (ofListM f c.normalize 1))  := by
  rw [ofListM_cons_eq_ofListM, map_mul, ih, Finset.mul_sum,
    ← Contractions.consEquiv.symm.sum_comp]
  erw [Finset.sum_sigma]
  congr
  funext c
  have hb := S.h𝓑 a
  rw [← mul_assoc]
  have hi := c.toCenterTerm_center f q le1 F S
  rw [Subalgebra.mem_center_iff] at hi
  rw [hi, mul_assoc, ← map_mul, hb, add_mul, map_add]
  conv_lhs =>
    rhs
    lhs
    rw [ofList_eq_smul_one]
    rw [Algebra.smul_mul_assoc]
    rw [ofList_singleton]
  rw [mul_koszulOrder_le]
  conv_lhs =>
    rhs
    lhs
    rw [← map_smul, ← Algebra.smul_mul_assoc]
    rw [← ofList_singleton, ← ofList_eq_smul_one]
  conv_lhs =>
    rhs
    rhs
    rw [ofList_eq_smul_one, Algebra.smul_mul_assoc, map_smul]
  rw [le_all_mul_koszulOrder_ofListM_expand]
  conv_lhs =>
    rhs
    rhs
    rw [smul_add, Finset.smul_sum]
    rw [← map_smul, ← map_smul, ← Algebra.smul_mul_assoc, ← ofList_eq_smul_one]
    rhs
    rhs
    intro n
    rw [← Algebra.smul_mul_assoc, smul_comm, ← map_smul, ← LinearMap.map_smul₂, ← ofList_eq_smul_one]
  rw [← add_assoc, ← map_add, ← map_add, ← add_mul, ← hb, ← ofListM_cons_eq_ofListM, mul_add]
  rw [Fintype.sum_option]
  congr 1
  rw [Finset.mul_sum]
  congr
  funext n
  rw [← mul_assoc]
  rfl
  exact S.h𝓑p a
  exact S.h𝓑n a

theorem static_wick_theorem {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1] [IsTrans ((i : I) × f i) le1] [IsTotal ((i : I) × f i) le1]
    {A : Type} [Semiring A] [Algebra ℂ A] (r : List I)
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F]
    (S : Contractions.Splitting f le1) :
    F (ofListM f r 1) = ∑ c : Contractions r, c.toCenterTerm f q le1 F S *
      F (koszulOrder le1 (fun i => q i.fst) (ofListM f c.normalize 1)) := by
  induction r with
  | nil => exact static_wick_nil q le1 F S
  | cons a r ih => exact static_wick_cons q le1 r a F S ih

end
end Wick
