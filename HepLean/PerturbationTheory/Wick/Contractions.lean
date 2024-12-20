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

open HepLean.List
open FieldStatistic

variable {𝓕 : Type}

/-- Given a list of fields `l`, the type of pairwise-contractions associated with `l`
  which have the list `aux` uncontracted. -/
inductive ContractionsAux : (l : List 𝓕) → (aux : List 𝓕) → Type
  | nil : ContractionsAux [] []
  | cons {l : List 𝓕} {aux : List 𝓕} {a : 𝓕} (i : Option (Fin aux.length)) :
    ContractionsAux l aux → ContractionsAux (a :: l) (optionEraseZ aux a i)

/-- Given a list of fields `l`, the type of pairwise-contractions associated with `l`. -/
def Contractions (l : List 𝓕) : Type := Σ aux, ContractionsAux l aux

namespace Contractions

variable {l : List 𝓕} (c : Contractions l)

/-- The list of uncontracted fields. -/
def normalize : List 𝓕 := c.1

lemma contractions_nil (a : Contractions ([] : List 𝓕)) : a = ⟨[], ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

lemma contractions_single {i : 𝓕} (a : Contractions [i]) : a =
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

/-- For the nil list of fields there is only one contraction. -/
def nilEquiv : Contractions ([] : List 𝓕) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], ContractionsAux.nil⟩
  left_inv a := Eq.symm (contractions_nil a)
  right_inv _ := rfl

/-- The equivalence between contractions of `a :: l` and contractions of
  `Contractions l` paired with an optional element of `Fin (c.normalize).length` specifying
  what `a` contracts with if any. -/
def consEquiv {a : 𝓕} {l : List 𝓕} :
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

/-- The type of contractions is decidable. -/
instance decidable : (l : List 𝓕) → DecidableEq (Contractions l)
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

/-- The type of contractions is finite. -/
instance fintype : (l : List 𝓕) → Fintype (Contractions l)
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

/-- A structure specifying when a type `I` and a map `f :I → Type` corresponds to
  the splitting of a fields `φ` into a creation `n` and annihlation part `p`. -/
structure Splitting (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1] where
  /-- The creation part of the fields. The label `n` corresponds to the fact that
    in normal ordering these feilds get pushed to the negative (left) direction. -/
  𝓑n : 𝓕 → (Σ i, f i)
  /-- The annhilation part of the fields. The label `p` corresponds to the fact that
    in normal ordering these feilds get pushed to the positive (right) direction. -/
  𝓑p : 𝓕 → (Σ i, f i)
  /-- The complex coefficent of creation part of a field `i`. This is usually `0` or `1`. -/
  𝓧n : 𝓕 → ℂ
  /-- The complex coefficent of annhilation part of a field `i`. This is usually `0` or `1`. -/
  𝓧p : 𝓕 → ℂ
  h𝓑 : ∀ i, ofListLift f [i] 1 = ofList [𝓑n i] (𝓧n i) + ofList [𝓑p i] (𝓧p i)
  h𝓑n : ∀ i j, le1 (𝓑n i) j
  h𝓑p : ∀ i j, le1 j (𝓑p i)

/-- In the static wick's theorem, the term associated with a contraction `c` containing
  the contractions. -/
noncomputable def toCenterTerm (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ[ℂ] A) :
    {r : List 𝓕} → (c : Contractions r) → (S : Splitting f le1) → A
  | [], ⟨[], .nil⟩, _ => 1
  | _ :: _, ⟨_, .cons (aux := aux') none c⟩, S => toCenterTerm f q le1 F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (aux := aux') (some n) c⟩, S => toCenterTerm f q le1 F ⟨aux', c⟩ S *
    superCommuteCoef q [aux'.get n] (List.take (↑n) aux') •
      F (((superCommute fun i => q i.fst) (ofList [S.𝓑p a] (S.𝓧p a))) (ofListLift f [aux'.get n] 1))

lemma toCenterTerm_none (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic) {r : List 𝓕}
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A)
    (S : Splitting f le1) (a : 𝓕) (c : Contractions r) :
    toCenterTerm (r := a :: r) f q le1 F (Contractions.consEquiv.symm ⟨c, none⟩) S =
    toCenterTerm f q le1 F c S := by
  rw [consEquiv]
  simp only [Equiv.coe_fn_symm_mk]
  dsimp [toCenterTerm]
  rfl

lemma toCenterTerm_center (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le1 F] :
    {r : List 𝓕} → (c : Contractions r) → (S : Splitting f le1) →
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
    simp only [CreateAnnihilateSect.toList]
    rw [ofList_singleton]
    exact OperatorMap.superCommute_ofList_singleton_ι_center (q := fun i => q i.1)
      (le1 := le1) F (S.𝓑p a) ⟨aux'[↑n], x.head⟩

end Contractions

end Wick
