/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.OperatorMap
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
    ⟨[i], ContractionsAux.cons none ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rename_i aux' c'
  cases c'
  cases aux'
  simp only [List.length_nil, optionEraseZ]
  rename_i x
  exact Fin.elim0 x

def nilEquiv : Contractions ([] : List I) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], ContractionsAux.nil⟩
  left_inv a := Eq.symm (contractions_nil a)
  right_inv _ := rfl

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
    | ContractionsAux.nil, ContractionsAux.nil => isTrue rfl
  | _ :: l =>
    haveI : DecidableEq (Contractions l) := decidable l
    haveI : DecidableEq ((c : Contractions l) × Option (Fin (c.normalize).length)) :=
      Sigma.instDecidableEqSigma
    Equiv.decidableEq consEquiv

instance fintype : (l : List I) → Fintype (Contractions l)
  | [] => {
    elems := {⟨[], ContractionsAux.nil⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_nil a}
  | a :: l =>
    haveI : Fintype (Contractions l) := fintype l
    haveI : Fintype ((c : Contractions l) × Option (Fin (c.normalize).length)) :=
      Sigma.instFintype
    Fintype.ofEquiv _ consEquiv.symm

structure Splitting {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1] where
  𝓑n : I → (Σ i, f i)
  𝓑p : I → (Σ i, f i)
  𝓧n : I → ℂ
  𝓧p : I → ℂ
  h𝓑 : ∀ i, ofListLift f [i] 1 = ofList [𝓑n i] (𝓧n i) + ofList [𝓑p i] (𝓧p i)
  h𝓑n : ∀ i j, le1 (𝓑n i) j
  h𝓑p : ∀ i j, le1 j (𝓑p i)

def toCenterTerm {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F] :
    {r : List I} → (c : Contractions r) → (S : Splitting f le1) → A
  | [], ⟨[], .nil⟩, _ => 1
  | _ :: _, ⟨_, .cons (aux := aux') none c⟩, S => toCenterTerm f q le1 F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (aux := aux') (some n) c⟩, S => toCenterTerm f q le1 F ⟨aux', c⟩ S *
    superCommuteCoef q [aux'.get n] (List.take (↑n) aux') •
      F (((superCommute fun i => q i.fst) (ofList [S.𝓑p a] (S.𝓧p a))) (ofListLift f [aux'.get n] 1))

lemma toCenterTerm_none {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (q : I → Fin 2) {r : List I}
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F]
    (S : Splitting f le1) (a : I) (c : Contractions r) :
    toCenterTerm (r := a :: r) f q le1 F (Contractions.consEquiv.symm ⟨c, none⟩) S =
    toCenterTerm f q le1 F c S := by
  rw [consEquiv]
  simp only [Equiv.coe_fn_symm_mk]
  dsimp [toCenterTerm]
  rfl

lemma toCenterTerm_center {I : Type} (f : I → Type) [∀ i, Fintype (f i)]
    (q : I → Fin 2)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F] :
    {r : List I} → (c : Contractions r) → (S : Splitting f le1) →
    (c.toCenterTerm f q le1 F S) ∈ Subalgebra.center ℂ A
  | [], ⟨[], .nil⟩, _ => by
    dsimp [toCenterTerm]
    exact Subalgebra.one_mem (Subalgebra.center ℂ A)
  | _ :: _, ⟨_, .cons (aux := aux') none c⟩, S => by
    dsimp [toCenterTerm]
    exact toCenterTerm_center f q le1 F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (aux := aux') (some n) c⟩, S => by
    dsimp [toCenterTerm]
    refine Subalgebra.mul_mem (Subalgebra.center ℂ A) ?hx ?hy
    exact toCenterTerm_center f q le1 F ⟨aux', c⟩ S
    apply Subalgebra.smul_mem
    rw [ofListLift_expand]
    rw [map_sum, map_sum]
    refine Subalgebra.sum_mem (Subalgebra.center ℂ A) ?hy.hx.h
    intro x _
    simp only [CreateAnnilateSect.toList]
    rw [ofList_singleton]
    exact OperatorMap.superCommute_ofList_singleton_ι_center (q := fun i => q i.1)
      (le1 := le1) F (S.𝓑p a) ⟨aux'[↑n], x.head⟩

end Contractions

end
end Wick
