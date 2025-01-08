/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.OperatorMap
import HepLean.Mathematics.Fin.Involutions
/-!

# Contractions of a list of fields

-/

namespace Wick

open HepLean.List
open HepLean.Fin
open FieldStatistic

variable {𝓕 : Type}

/-- Given a list of fields `φs`, the type of pairwise-contractions associated with `φs`
  which have the list `φsᵤₙ` uncontracted. -/
inductive ContractionsAux : (φs : List 𝓕) → (φsᵤₙ : List 𝓕) → Type
  | nil : ContractionsAux [] []
  | cons {φs : List 𝓕} {φsᵤₙ : List 𝓕} {φ : 𝓕} (i : Option (Fin φsᵤₙ.length)) :
    ContractionsAux φs φsᵤₙ → ContractionsAux (φ :: φs) (optionEraseZ φsᵤₙ φ i)

/-- Given a list of fields `l`, the type of pairwise-contractions associated with `l`. -/
def Contractions (φs : List 𝓕) : Type := Σ aux, ContractionsAux φs aux

namespace Contractions

variable {l : List 𝓕} (c : Contractions l)

/-- The equivalence between `ContractionsAux` based on the propositionally equivalent
  uncontracted lists. -/
def auxCongr : {φs : List 𝓕} → {φsᵤₙ φsᵤₙ' : List 𝓕} → (h : φsᵤₙ = φsᵤₙ') →
    ContractionsAux φs φsᵤₙ ≃ ContractionsAux φs φsᵤₙ'
  | _, _, _, Eq.refl _ => Equiv.refl _

lemma auxCongr_ext {φs : List 𝓕} {c c2 : Contractions φs} (h : c.1 = c2.1)
    (hx : c.2 = auxCongr h.symm c2.2) : c = c2 := by
  cases c
  cases c2
  simp only at h
  subst h
  simp only [auxCongr, Equiv.refl_apply] at hx
  subst hx
  rfl

/-- The list of uncontracted fields. -/
def uncontracted : List 𝓕 := c.1

lemma uncontracted_length_even_iff : {l : List 𝓕} → (c : Contractions l) →
    Even l.length ↔ Even c.uncontracted.length
  | [], ⟨[], ContractionsAux.nil⟩ => by
    simp [uncontracted]
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) none c⟩ => by
    simp only [List.length_cons, uncontracted, optionEraseZ]
    rw [Nat.even_add_one, Nat.even_add_one]
    rw [uncontracted_length_even_iff ⟨aux, c⟩]
    rfl
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩=> by
    simp only [List.length_cons, uncontracted, optionEraseZ_some_length]
    rw [Nat.even_sub, Nat.even_add_one]
    · simp only [Nat.not_even_iff_odd, Nat.not_even_one, iff_false]
      rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
      rw [uncontracted_length_even_iff ⟨aux, c⟩]
      rfl
    · refine Nat.one_le_iff_ne_zero.mpr (fun hn => ?_)
      rw [hn] at n
      exact Fin.elim0 n

lemma contractions_nil (a : Contractions ([] : List 𝓕)) : a = ⟨[], ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

/-- The embedding of the uncontracted fields into all fields. -/
def embedUncontracted {l : List 𝓕} (c : Contractions l) :
    Fin c.uncontracted.length → Fin l.length :=
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ => Fin.elim0
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    Fin.cons ⟨0, Nat.zero_lt_succ φs.length⟩ (Fin.succ ∘ (embedUncontracted ⟨aux, c⟩))
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ => by
    let lc := embedUncontracted ⟨aux, c⟩
    refine Fin.succ ∘ lc ∘ Fin.cast ?_ ∘ Fin.succAbove ⟨n, by
      rw [uncontracted, optionEraseZ_some_length]
      omega⟩
    simp only [uncontracted, optionEraseZ_some_length]
    have hq : aux.length ≠ 0 := by
      by_contra hn
      rw [hn] at n
      exact Fin.elim0 n
    omega

lemma embedUncontracted_injective {l : List 𝓕} (c : Contractions l) :
    Function.Injective c.embedUncontracted := by
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ =>
    dsimp only [List.length_nil, embedUncontracted]
    intro i
    exact Fin.elim0 i
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    dsimp only [List.length_cons, embedUncontracted, Fin.zero_eta]
    refine Fin.cons_injective_iff.mpr ?_
    apply And.intro
    · simp only [Set.mem_range, Function.comp_apply, not_exists]
      exact fun x => Fin.succ_ne_zero (embedUncontracted ⟨aux, c⟩ x)
    · exact Function.Injective.comp (Fin.succ_injective φs.length)
        (embedUncontracted_injective ⟨aux, c⟩)
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some i) c⟩ =>
    dsimp only [List.length_cons, embedUncontracted]
    refine Function.Injective.comp (Fin.succ_injective φs.length) ?hf
    refine Function.Injective.comp (embedUncontracted_injective ⟨aux, c⟩) ?hf.hf
    refine Function.Injective.comp (Fin.cast_injective (embedUncontracted.proof_5 φ φs aux i c))
      Fin.succAbove_right_injective

/-- Establishes uniqueness of contractions for a single field, showing that any contraction
  of a single field must be equivalent to the trivial contraction with no pairing. -/
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

/--
  This function provides an equivalence between the type of contractions for an empty list of fields
  and the unit type, indicating that there is only one possible contraction for an empty list.
-/
def nilEquiv : Contractions ([] : List 𝓕) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], ContractionsAux.nil⟩
  left_inv a := Eq.symm (contractions_nil a)
  right_inv _ := rfl

/-- The equivalence between contractions of `a :: l` and contractions of
  `Contractions l` paired with an optional element of `Fin (c.uncontracted).length` specifying
  what `a` contracts with if any. -/
def consEquiv {φ : 𝓕} {φs : List 𝓕} :
    Contractions (φ :: φs) ≃ (c : Contractions φs) × Option (Fin c.uncontracted.length) where
  toFun c :=
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (φsᵤₙ := aux') i c => ⟨⟨aux', c⟩, i⟩
  invFun ci :=
    ⟨(optionEraseZ (ci.fst.uncontracted) φ ci.2), ContractionsAux.cons (φ := φ) ci.2 ci.1.2⟩
  left_inv c := by
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (φsᵤₙ := aux') i c => rfl
  right_inv ci := by rfl

lemma consEquiv_ext {φs : List 𝓕} {c1 c2 : Contractions φs}
    {n1 : Option (Fin c1.uncontracted.length)} {n2 : Option (Fin c2.uncontracted.length)}
    (hc : c1 = c2) (hn : Option.map (finCongr (by rw [hc])) n1 = n2) :
    (⟨c1, n1⟩ : (c : Contractions φs) × Option (Fin c.uncontracted.length)) = ⟨c2, n2⟩ := by
  subst hc
  subst hn
  simp

/-- The type of contractions is decidable. -/
instance decidable : (φs : List 𝓕) → DecidableEq (Contractions φs)
  | [] => fun a b =>
    match a, b with
    | ⟨_, a⟩, ⟨_, b⟩ =>
    match a, b with
    | ContractionsAux.nil, ContractionsAux.nil => isTrue rfl
  | _ :: φs =>
    haveI : DecidableEq (Contractions φs) := decidable φs
    haveI : DecidableEq ((c : Contractions φs) × Option (Fin (c.uncontracted).length)) :=
      Sigma.instDecidableEqSigma
    Equiv.decidableEq consEquiv

/-- The type of contractions is finite. -/
instance fintype : (φs : List 𝓕) → Fintype (Contractions φs)
  | [] => {
    elems := {⟨[], ContractionsAux.nil⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_nil a}
  | φ :: φs =>
    haveI : Fintype (Contractions φs) := fintype φs
    haveI : Fintype ((c : Contractions φs) × Option (Fin (c.uncontracted).length)) :=
      Sigma.instFintype
    Fintype.ofEquiv _ consEquiv.symm

/-- A contraction is a full contraction if there normalizing list of fields is empty. -/
def IsFull : Prop := c.uncontracted = []

/-- Provides a decidable instance for determining if a contraction is full
  (i.e., all fields are paired). -/
instance isFull_decidable : Decidable c.IsFull := by
  have hn : c.IsFull ↔ c.uncontracted.length = 0 := by
    simp [IsFull]
  apply decidable_of_decidable_of_iff hn.symm

/-- A structure specifying when a type `I` and a map `f :I → Type` corresponds to
  the splitting of a fields `φ` into a creation `n` and annihlation part `p`. -/
structure Splitting (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le] where
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
  h𝓑n : ∀ i j, le (𝓑n i) j
  h𝓑p : ∀ i j, le j (𝓑p i)

/-- In the static wick's theorem, the term associated with a contraction `c` containing
  the contractions. -/
noncomputable def toCenterTerm (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic)
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ[ℂ] A) :
    {φs : List 𝓕} → (c : Contractions φs) → (S : Splitting f le) → A
  | [], ⟨[], .nil⟩, _ => 1
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux') none c⟩, S => toCenterTerm f q le F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (φsᵤₙ := aux') (some n) c⟩, S => toCenterTerm f q le F ⟨aux', c⟩ S *
    superCommuteCoef q [aux'.get n] (List.take (↑n) aux') •
      F (((superCommute fun i => q i.fst) (ofList [S.𝓑p a] (S.𝓧p a)))
        (ofListLift f [aux'.get n] 1))

/-- Shows that adding a field with no contractions (none) to an existing set of contractions
  results in the same center term as the original contractions.

  Physically, this represents that an uncontracted (free) field does not affect
  the contraction structure of other fields in Wick's theorem. -/
lemma toCenterTerm_none (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic) {φs : List 𝓕}
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A)
    (S : Splitting f le) (φ : 𝓕) (c : Contractions φs) :
    toCenterTerm (φs := φ :: φs) f q le F (Contractions.consEquiv.symm ⟨c, none⟩) S =
    toCenterTerm f q le F c S := by
  rw [consEquiv]
  simp only [Equiv.coe_fn_symm_mk]
  dsimp only [toCenterTerm]
  rfl

/-- Proves that the part of the term gained from Wick contractions is in
  the center of the algebra. -/
lemma toCenterTerm_center (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic)
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le F] :
    {φs : List 𝓕} → (c : Contractions φs) → (S : Splitting f le) →
    (c.toCenterTerm f q le F S) ∈ Subalgebra.center ℂ A
  | [], ⟨[], .nil⟩, _ => by
    dsimp only [toCenterTerm]
    exact Subalgebra.one_mem (Subalgebra.center ℂ A)
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux') none c⟩, S => by
    dsimp only [toCenterTerm]
    exact toCenterTerm_center f q le F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (φsᵤₙ := aux') (some n) c⟩, S => by
    dsimp only [toCenterTerm, List.get_eq_getElem]
    refine Subalgebra.mul_mem (Subalgebra.center ℂ A) ?hx ?hy
    exact toCenterTerm_center f q le F ⟨aux', c⟩ S
    apply Subalgebra.smul_mem
    rw [ofListLift_expand]
    rw [map_sum, map_sum]
    refine Subalgebra.sum_mem (Subalgebra.center ℂ A) ?hy.hx.h
    intro x _
    simp only [CreateAnnihilateSect.toList]
    rw [ofList_singleton]
    exact OperatorMap.superCommute_ofList_singleton_ι_center (q := fun i => q i.1)
      (le := le) F (S.𝓑p a) ⟨aux'[↑n], x.head⟩

/-!

## Inserting

-/
def eraseIdxFromUncontracted : {φs : List 𝓕} → Contractions φs → (n : ℕ) → List 𝓕
  | [], ⟨[], ContractionsAux.nil⟩, _ => []
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux) n _⟩, 0 => aux
  | φ :: _, ⟨_, .cons (φsᵤₙ := aux) none c⟩, n + 1 => φ :: eraseIdxFromUncontracted ⟨aux, c⟩ n
  | φ :: _, ⟨_, .cons (φsᵤₙ := aux) (some m) c⟩, n + 1 =>
    if m.val = n then
      φ :: eraseIdxFromUncontracted ⟨aux, c⟩ n
    else eraseIdxFromUncontracted ⟨aux, c⟩ n

def eraseIdx : {φs : List 𝓕} →  Contractions φs → (n : ℕ) → Contractions (List.eraseIdx φs n)
  | [], ⟨[], ContractionsAux.nil⟩, _ => ⟨[], ContractionsAux.nil⟩
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) x c⟩, 0 => ⟨aux, c⟩
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) none c⟩, n + 1 =>
    ⟨φ :: (eraseIdx ⟨aux, c⟩ n).1, ContractionsAux.cons none (eraseIdx ⟨aux, c⟩ n).2⟩
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some m) c⟩, n + 1 =>
    if m.val = n then
      ⟨φ :: (eraseIdx ⟨aux, c⟩ n).1 , ContractionsAux.cons none (eraseIdx ⟨aux, c⟩ n).2⟩
    else
     let m' : Fin (eraseIdx ⟨aux, c⟩ n).fst.length := ⟨
      if m.val < n then m.val else m.val - 1, by
      simp
      rw [ List.length_eraseIdx]
      ⟩
     ⟨(eraseIdx ⟨aux, c⟩ n).1, ContractionsAux.cons (some (by sorry)) (eraseIdx ⟨aux, c⟩ n).2⟩

def insertIdxEquiv (φ : 𝓕) (φs : List 𝓕) (n : ℕ) :
    Contractions (List.insertIdx n φ φs) ≃ (c : Contractions φs) × Option (Fin c.uncontracted.length) where
  toFun c := ⟨List.insertIdx n φ φs, c.1⟩
  invFun c := ⟨List.eraseIdx n c.uncontracted, c.1⟩

end Contractions

end Wick
