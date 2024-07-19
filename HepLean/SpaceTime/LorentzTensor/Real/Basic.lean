/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Function.CompTypeclasses
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fintype
/-!

# Real Lorentz Tensors

In this file we define real Lorentz tensors.

We implicitly follow the definition of a modular operad.
This will relation should be made explicit in the future.

## References

-- For modular operads see: [Raynor][raynor2021graphical]

-/
/-! TODO: Do complex tensors, with Van der Waerden notation for fermions. -/
/-! TODO: Generalize to maps into Lorentz tensors. -/

/-- The possible `colors` of an index for a RealLorentzTensor.
 There are two possibilities, `up` and `down`. -/
inductive RealLorentzTensor.Colors where
  | up : RealLorentzTensor.Colors
  | down : RealLorentzTensor.Colors

/-- The association of colors with indices. For up and down this is `Fin 1 ⊕ Fin d`. -/
def RealLorentzTensor.ColorsIndex (d : ℕ) (μ : RealLorentzTensor.Colors) : Type :=
  match μ with
  | RealLorentzTensor.Colors.up => Fin 1 ⊕ Fin d
  | RealLorentzTensor.Colors.down => Fin 1 ⊕ Fin d

instance (d : ℕ) (μ : RealLorentzTensor.Colors) : Fintype (RealLorentzTensor.ColorsIndex d μ) :=
  match μ with
  | RealLorentzTensor.Colors.up => instFintypeSum (Fin 1) (Fin d)
  | RealLorentzTensor.Colors.down => instFintypeSum (Fin 1) (Fin d)

instance (d : ℕ) (μ : RealLorentzTensor.Colors) : DecidableEq (RealLorentzTensor.ColorsIndex d μ) :=
  match μ with
  | RealLorentzTensor.Colors.up => instDecidableEqSum
  | RealLorentzTensor.Colors.down => instDecidableEqSum

/-- An `IndexValue` is a set of actual values an index can take. e.g. for a
  3-tensor (0, 1, 2). -/
def RealLorentzTensor.IndexValue {X : Type} (d : ℕ) (c : X → RealLorentzTensor.Colors) :
    Type 0 := (x : X) → RealLorentzTensor.ColorsIndex d (c x)

/-- A Lorentz Tensor defined by its coordinate map. -/
structure RealLorentzTensor (d : ℕ) (X : Type) where
  /-- The color associated to each index of the tensor. -/
  color : X → RealLorentzTensor.Colors
  /-- The coordinate map for the tensor. -/
  coord : RealLorentzTensor.IndexValue d color → ℝ

namespace RealLorentzTensor
open Matrix
universe u1
variable {d : ℕ} {X Y Z : Type} (c : X → Colors)

/-!

## Colors

-/

/-- The involution acting on colors. -/
def τ : Colors → Colors
  | Colors.up => Colors.down
  | Colors.down => Colors.up

/-- The map τ is an involution. -/
@[simp]
lemma τ_involutive : Function.Involutive τ := by
  intro x
  cases x <;> rfl

lemma color_eq_dual_symm {μ ν : Colors} (h : μ = τ ν) : ν = τ μ :=
  (Function.Involutive.eq_iff τ_involutive).mp h.symm

/-- The color associated with an element of `x ∈ X` for a tensor `T`. -/
def ch {X : Type} (x : X) (T : RealLorentzTensor d X) : Colors := T.color x

/-- An equivalence of `ColorsIndex` types given an equality of colors. -/
def colorsIndexCast {d : ℕ} {μ₁ μ₂ : RealLorentzTensor.Colors} (h : μ₁ = μ₂) :
    ColorsIndex d μ₁ ≃ ColorsIndex d μ₂ :=
  Equiv.cast (congrArg (ColorsIndex d) h)

/-- An equivalence of `ColorsIndex` between that of a color and that of its dual. -/
def colorsIndexDualCastSelf {d : ℕ} {μ : RealLorentzTensor.Colors}:
    ColorsIndex d μ ≃ ColorsIndex d (τ μ) where
  toFun x :=
    match μ with
    | RealLorentzTensor.Colors.up => x
    | RealLorentzTensor.Colors.down => x
  invFun x :=
    match μ with
    | RealLorentzTensor.Colors.up => x
    | RealLorentzTensor.Colors.down => x
  left_inv x := by cases μ <;> rfl
  right_inv x := by cases μ <;> rfl

/-- An equivalence of `ColorsIndex` types given an equality of a color and the dual of a color. -/
def colorsIndexDualCast {μ ν : Colors} (h : μ = τ ν) :
    ColorsIndex d μ ≃ ColorsIndex d ν :=
  (colorsIndexCast h).trans colorsIndexDualCastSelf.symm

lemma colorsIndexDualCast_symm {μ ν : Colors} (h : μ = τ ν) :
    (colorsIndexDualCast h).symm =
    @colorsIndexDualCast d _ _ ((Function.Involutive.eq_iff τ_involutive).mp h.symm) := by
  match μ, ν with
  | Colors.up, Colors.down => rfl
  | Colors.down, Colors.up => rfl

/-!

## Index values

-/

instance [Fintype X] [DecidableEq X] : Fintype (IndexValue d c) := Pi.fintype

instance [Fintype X] : DecidableEq (IndexValue d c) :=
  Fintype.decidablePiFintype

/-!

## Induced isomorphisms between IndexValue sets

-/

/-- An isomorphism of the type of index values given an isomorphism of sets. -/
@[simps!]
def indexValueIso (d : ℕ) (f : X ≃ Y) {i : X → Colors} {j : Y → Colors} (h : i = j ∘ f) :
    IndexValue d i ≃ IndexValue d j :=
  (Equiv.piCongrRight (fun μ => colorsIndexCast (congrFun h μ))).trans $
  Equiv.piCongrLeft (fun y => RealLorentzTensor.ColorsIndex d (j y)) f

lemma indexValueIso_symm_apply' (d : ℕ) (f : X ≃ Y) {i : X → Colors} {j : Y → Colors}
    (h : i = j ∘ f) (y : IndexValue d j) (x : X) :
    (indexValueIso d f h).symm y x = (colorsIndexCast (congrFun h x)).symm (y (f x)) := by
  rfl

@[simp]
lemma indexValueIso_trans (d : ℕ) (f : X ≃ Y) (g : Y ≃ Z) {i : X → Colors}
    {j : Y → Colors} {k : Z → Colors} (h : i = j ∘ f) (h' : j = k ∘ g) :
    (indexValueIso d f h).trans (indexValueIso d g h') =
    indexValueIso d (f.trans g) (by rw [h, h', Function.comp.assoc]; rfl) := by
  have h1 : ((indexValueIso d f h).trans (indexValueIso d g h')).symm =
      (indexValueIso d (f.trans g) (by rw [h, h', Function.comp.assoc]; rfl)).symm := by
    subst h' h
    exact Equiv.coe_inj.mp rfl
  simpa only [Equiv.symm_symm] using congrArg (fun e => e.symm) h1

lemma indexValueIso_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    (indexValueIso d f h).symm =
    indexValueIso d f.symm ((Equiv.eq_comp_symm f j i).mpr (id (Eq.symm h))) := by
  ext i : 1
  rw [← Equiv.symm_apply_eq]
  funext y
  rw [indexValueIso_symm_apply', indexValueIso_symm_apply']
  simp only [Function.comp_apply, colorsIndexCast, Equiv.cast_symm, Equiv.cast_apply, cast_cast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.apply_symm_apply]

lemma indexValueIso_eq_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    indexValueIso d f h =
    (indexValueIso d f.symm ((Equiv.eq_comp_symm f j i).mpr (id (Eq.symm h)))).symm := by
  rw [indexValueIso_symm]
  rfl

@[simp]
lemma indexValueIso_refl (d : ℕ) (i : X → Colors) :
    indexValueIso d (Equiv.refl X) (rfl : i = i) = Equiv.refl _ := by
  rfl

/-!

## Dual isomorphism for index values

-/

/-- The isomorphism between the index values of a color map and its dual. -/
@[simps!]
def indexValueDualIso (d : ℕ) {i j : X → Colors} (h : i = τ ∘ j) :
    IndexValue d i ≃ IndexValue d j :=
  (Equiv.piCongrRight (fun μ => colorsIndexDualCast (congrFun h μ)))

/-!

## Extensionality

-/

lemma ext {T₁ T₂ : RealLorentzTensor d X} (h : T₁.color = T₂.color)
    (h' : T₁.coord = fun i => T₂.coord (indexValueIso d (Equiv.refl X) h i)) :
      T₁ = T₂ := by
  cases T₁
  cases T₂
  simp_all only [IndexValue, mk.injEq]
  apply And.intro h
  simp only at h
  subst h
  simp only [Equiv.cast_refl, Equiv.coe_refl, CompTriple.comp_eq] at h'
  rfl

/-!

## Mapping isomorphisms.

-/

/-- An equivalence of Tensors given an equivalence of underlying sets. -/
@[simps!]
def mapIso (d : ℕ) (f : X ≃ Y) : RealLorentzTensor d X ≃ RealLorentzTensor d Y where
  toFun T := {
    color := T.color ∘ f.symm,
    coord := T.coord ∘ (indexValueIso d f (by simp : T.color = T.color ∘ f.symm ∘ f)).symm}
  invFun T := {
    color := T.color ∘ f,
    coord := T.coord ∘ (indexValueIso d f.symm (by simp : T.color = T.color ∘ f ∘ f.symm)).symm}
  left_inv T := by
    refine ext ?_ ?_
    · simp [Function.comp.assoc]
    · funext i
      simp only [IndexValue, Function.comp_apply, Function.comp_id]
      apply congrArg
      funext x
      erw [indexValueIso_symm_apply', indexValueIso_symm_apply', indexValueIso_eq_symm,
        indexValueIso_symm_apply']
      rw [← Equiv.apply_eq_iff_eq_symm_apply]
      simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq, colorsIndexCast,
        Equiv.cast_symm, Equiv.cast_apply, cast_cast, Equiv.refl_apply]
      apply cast_eq_iff_heq.mpr
      congr
      exact Equiv.symm_apply_apply f x
  right_inv T := by
    refine ext ?_ ?_
    · simp [Function.comp.assoc]
    · funext i
      simp only [IndexValue, Function.comp_apply, Function.comp_id]
      apply congrArg
      funext x
      erw [indexValueIso_symm_apply', indexValueIso_symm_apply', indexValueIso_eq_symm,
        indexValueIso_symm_apply']
      rw [← Equiv.apply_eq_iff_eq_symm_apply]
      simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq, colorsIndexCast,
        Equiv.cast_symm, Equiv.cast_apply, cast_cast, Equiv.refl_apply]
      apply cast_eq_iff_heq.mpr
      congr
      exact Equiv.apply_symm_apply f x

@[simp]
lemma mapIso_trans (f : X ≃ Y) (g : Y ≃ Z) :
    (mapIso d f).trans (mapIso d g) = mapIso d (f.trans g) := by
  refine Equiv.coe_inj.mp ?_
  funext T
  refine ext rfl ?_
  simp only [Equiv.trans_apply, IndexValue, mapIso_apply_color, Equiv.symm_trans_apply,
    indexValueIso_refl, Equiv.refl_apply, mapIso_apply_coord]
  funext i
  rw [mapIso_apply_coord, mapIso_apply_coord]
  apply congrArg
  rw [← indexValueIso_trans]
  rfl
  exact (Equiv.comp_symm_eq f (T.color ∘ ⇑f.symm) T.color).mp rfl

lemma mapIso_symm (f : X ≃ Y) : (mapIso d f).symm = mapIso d f.symm := rfl

lemma mapIso_refl : mapIso d (Equiv.refl X) = Equiv.refl _ := rfl

/-!

## Sums

-/

/-- An equivalence that splits elements of `IndexValue d (Sum.elim TX TY)` into two components. -/
def indexValueSumEquiv {X Y : Type} {TX : X → Colors} {TY : Y → Colors} :
    IndexValue d (Sum.elim TX TY) ≃ IndexValue d TX × IndexValue d TY where
  toFun i := (fun x => i (Sum.inl x), fun x => i (Sum.inr x))
  invFun p := fun c => match c with
    | Sum.inl x => (p.1 x)
    | Sum.inr x => (p.2 x)
  left_inv i := by
    simp only [IndexValue]
    ext1 x
    cases x with
    | inl val => rfl
    | inr val_1 => rfl
  right_inv p := rfl

/-- An equivalence between index values formed by commuting sums. -/
def indexValueSumComm {X Y : Type} (Tc : X → Colors) (Sc : Y → Colors) :
    IndexValue d (Sum.elim Tc Sc) ≃ IndexValue d (Sum.elim Sc Tc) :=
  indexValueIso d (Equiv.sumComm X Y) (by aesop)

/-!

## Marked Lorentz tensors

To define contraction and multiplication of Lorentz tensors we need to mark indices.

-/

/-- A `RealLorentzTensor` with `n` marked indices. -/
def Marked (d : ℕ) (X : Type) (n : ℕ) : Type :=
  RealLorentzTensor d (X ⊕ Fin n)

namespace Marked

variable {n m : ℕ}

/-- The marked point. -/
def markedPoint (X : Type) (i : Fin n) : (X ⊕ Fin n) :=
  Sum.inr i

/-- The colors of unmarked indices. -/
def unmarkedColor (T : Marked d X n) : X → Colors :=
  T.color ∘ Sum.inl

/-- The colors of marked indices. -/
def markedColor (T : Marked d X n) : Fin n → Colors :=
  T.color ∘ Sum.inr

/-- The index values restricted to unmarked indices. -/
def UnmarkedIndexValue (T : Marked d X n) : Type :=
  IndexValue d T.unmarkedColor

instance [Fintype X] [DecidableEq X] (T : Marked d X n) : Fintype T.UnmarkedIndexValue :=
  Pi.fintype

instance [Fintype X] (T : Marked d X n) : DecidableEq T.UnmarkedIndexValue :=
  Fintype.decidablePiFintype

/-- The index values restricted to marked indices. -/
def MarkedIndexValue (T : Marked d X n) : Type :=
  IndexValue d T.markedColor

instance (T : Marked d X n) : Fintype T.MarkedIndexValue :=
  Pi.fintype

instance (T : Marked d X n) : DecidableEq T.MarkedIndexValue :=
  Fintype.decidablePiFintype

lemma color_eq_elim (T : Marked d X n) :
    T.color = Sum.elim T.unmarkedColor T.markedColor := by
  ext1 x
  cases' x <;> rfl

/-- An equivalence splitting elements of `IndexValue d T.color` into their two components. -/
def splitIndexValue {T : Marked d X n} :
    IndexValue d T.color ≃ T.UnmarkedIndexValue × T.MarkedIndexValue :=
  (indexValueIso d (Equiv.refl _) T.color_eq_elim).trans
  indexValueSumEquiv

 @[simp]
lemma splitIndexValue_sum {T : Marked d X n} [Fintype X] [DecidableEq X]
    (P : T.UnmarkedIndexValue × T.MarkedIndexValue → ℝ) :
    ∑ i, P (splitIndexValue i) = ∑ j, ∑ k, P (j, k) := by
  rw [Equiv.sum_comp splitIndexValue, Fintype.sum_prod_type]

/-- Construction of marked index values for the case of 1 marked index. -/
def oneMarkedIndexValue {T : Marked d X 1} :
    ColorsIndex d (T.color (markedPoint X 0)) ≃ T.MarkedIndexValue where
  toFun x := fun i => match i with
    | 0 => x
  invFun i := i 0
  left_inv x := rfl
  right_inv i := by
    funext x
    fin_cases x
    rfl

/-- Construction of marked index values for the case of 2 marked index. -/
def twoMarkedIndexValue (T : Marked d X 2) (x : ColorsIndex d (T.color (markedPoint X 0)))
    (y : ColorsIndex d <| T.color <| markedPoint X 1) :
    T.MarkedIndexValue := fun i =>
  match i with
  | 0 => x
  | 1 => y

/-- An equivalence of types used to turn the first marked index into an unmarked index. -/
def unmarkFirstSet (X : Type) (n : ℕ) : (X ⊕ Fin n.succ) ≃ (X ⊕ Fin 1) ⊕ Fin n :=
  trans (Equiv.sumCongr (Equiv.refl _)
    (((Fin.castOrderIso (Nat.succ_eq_one_add n)).toEquiv.trans finSumFinEquiv.symm)))
  (Equiv.sumAssoc _ _ _).symm

/-- Unmark the first marked index of a marked tensor. -/
def unmarkFirst {X : Type} : Marked d X n.succ ≃ Marked d (X ⊕ Fin 1) n :=
  mapIso d (unmarkFirstSet X n)

/-!

## Marking elements.

-/
section markingElements

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Splits a type based on an embedding from `Fin n` into elements not in the image of the
  embedding, and elements in the image. -/
def markEmbeddingSet {n : ℕ} (f : Fin n ↪ X) :
    X ≃ {x // x ∈ (Finset.image f Finset.univ)ᶜ} ⊕ Fin n :=
  (Equiv.Set.sumCompl (Set.range ⇑f)).symm.trans <|
  (Equiv.sumComm _ _).trans <|
  Equiv.sumCongr ((Equiv.subtypeEquivRight (by simp))) <|
  (Function.Embedding.toEquivRange f).symm

lemma markEmbeddingSet_on_mem {n : ℕ} (f : Fin n ↪ X) (x : X)
    (hx : x ∈ Finset.image f Finset.univ) : markEmbeddingSet f x =
    Sum.inr (f.toEquivRange.symm ⟨x, by simpa using hx⟩) := by
  rw [markEmbeddingSet]
  simp only [Equiv.trans_apply, Equiv.sumComm_apply, Equiv.sumCongr_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_mem]
  rfl

lemma markEmbeddingSet_on_not_mem {n : ℕ} (f : Fin n ↪ X) (x : X)
    (hx : ¬ x ∈ (Finset.image f Finset.univ)) : markEmbeddingSet f x =
    Sum.inl ⟨x, by simpa using hx⟩ := by
  rw [markEmbeddingSet]
  simp only [Equiv.trans_apply, Equiv.sumComm_apply, Equiv.sumCongr_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_not_mem]
  rfl
  simpa using hx

/-- Marks the indices of tensor in the image of an embedding. -/
@[simps!]
def markEmbedding {n : ℕ} (f : Fin n ↪ X) :
    RealLorentzTensor d X ≃ Marked d {x // x ∈ (Finset.image f Finset.univ)ᶜ} n :=
  mapIso d (markEmbeddingSet f)

lemma markEmbeddingSet_on_mem_indexValue_apply {n : ℕ} (f : Fin n ↪ X) (T : RealLorentzTensor d X)
    (i : IndexValue d (markEmbedding f T).color) (x : X) (hx : x ∈ (Finset.image f Finset.univ)) :
    i (markEmbeddingSet f x) = colorsIndexCast (congrArg ((markEmbedding f) T).color
    (markEmbeddingSet_on_mem f x hx).symm)
    (i (Sum.inr (f.toEquivRange.symm ⟨x, by simpa using hx⟩))) := by
  simp [colorsIndexCast]
  symm
  apply cast_eq_iff_heq.mpr
  rw [markEmbeddingSet_on_mem f x hx]

lemma markEmbeddingSet_on_not_mem_indexValue_apply {n : ℕ}
    (f : Fin n ↪ X) (T : RealLorentzTensor d X) (i : IndexValue d (markEmbedding f T).color)
    (x : X) (hx : ¬ x ∈ (Finset.image f Finset.univ)) :
    i (markEmbeddingSet f x) = colorsIndexCast (congrArg ((markEmbedding f) T).color
    (markEmbeddingSet_on_not_mem f x hx).symm) (i (Sum.inl ⟨x, by simpa using hx⟩)) := by
  simp [colorsIndexCast]
  symm
  apply cast_eq_iff_heq.mpr
  rw [markEmbeddingSet_on_not_mem f x hx]

/-- An equivalence between the IndexValues for a tensor `T` and the corresponding
  tensor with indices maked by an embedding. -/
@[simps!]
def markEmbeddingIndexValue {n : ℕ} (f : Fin n ↪ X) (T : RealLorentzTensor d X) :
    IndexValue d T.color ≃ IndexValue d (markEmbedding f T).color :=
  indexValueIso d (markEmbeddingSet f) (
    (Equiv.comp_symm_eq (markEmbeddingSet f) ((markEmbedding f) T).color T.color).mp rfl)

lemma markEmbeddingIndexValue_apply_symm_on_mem {n : ℕ}
    (f : Fin n.succ ↪ X) (T : RealLorentzTensor d X) (i : IndexValue d (markEmbedding f T).color)
    (x : X) (hx : x ∈ (Finset.image f Finset.univ)) :
    (markEmbeddingIndexValue f T).symm i x = (colorsIndexCast ((congrFun ((Equiv.comp_symm_eq
    (markEmbeddingSet f) ((markEmbedding f) T).color T.color).mp rfl) x).trans
    (congrArg ((markEmbedding f) T).color (markEmbeddingSet_on_mem f x hx)))).symm
    (i (Sum.inr (f.toEquivRange.symm ⟨x, by simpa using hx⟩))) := by
  rw [markEmbeddingIndexValue, indexValueIso_symm_apply']
  rw [markEmbeddingSet_on_mem_indexValue_apply f T i x hx]
  simp [colorsIndexCast]

lemma markEmbeddingIndexValue_apply_symm_on_not_mem {n : ℕ} (f : Fin n.succ ↪ X)
    (T : RealLorentzTensor d X) (i : IndexValue d (markEmbedding f T).color) (x : X)
    (hx : ¬ x ∈ (Finset.image f Finset.univ)) : (markEmbeddingIndexValue f T).symm i x =
    (colorsIndexCast ((congrFun ((Equiv.comp_symm_eq
      (markEmbeddingSet f) ((markEmbedding f) T).color T.color).mp rfl) x).trans
      ((congrArg ((markEmbedding f) T).color (markEmbeddingSet_on_not_mem f x hx))))).symm
     (i (Sum.inl ⟨x, by simpa using hx⟩)) := by
  rw [markEmbeddingIndexValue, indexValueIso_symm_apply']
  rw [markEmbeddingSet_on_not_mem_indexValue_apply f T i x hx]
  simp only [Nat.succ_eq_add_one, Function.comp_apply, markEmbedding_apply_color, colorsIndexCast,
    Equiv.cast_symm, id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, Equiv.cast_apply, cast_cast, cast_eq,
    Equiv.cast_refl, Equiv.refl_symm]
  rfl

/-- Given an equivalence of types, an embedding `f` to an embedding `g`, the equivalence
  taking the complement of the image of `f` to the complement of the image of `g`. -/
@[simps!]
def equivEmbedCompl (e : X ≃ Y) {f : Fin n ↪ X} {g : Fin n ↪ Y} (he : f.trans e = g) :
    {x // x ∈ (Finset.image f Finset.univ)ᶜ} ≃ {y // y ∈ (Finset.image g Finset.univ)ᶜ} :=
  (Equiv.subtypeEquivOfSubtype' e).trans <|
  (Equiv.subtypeEquivRight (fun x => by simp [← he, Equiv.eq_symm_apply]))

lemma markEmbedding_mapIso_right (e : X ≃ Y) (f : Fin n ↪ X) (g : Fin n ↪ Y) (he : f.trans e = g)
    (T : RealLorentzTensor d X) : markEmbedding g (mapIso d e T) =
    mapIso d (Equiv.sumCongr (equivEmbedCompl e he) (Equiv.refl (Fin n))) (markEmbedding f T) := by
  rw [markEmbedding, markEmbedding]
  erw [← Equiv.trans_apply, ← Equiv.trans_apply]
  rw [mapIso_trans, mapIso_trans]
  apply congrFun
  repeat apply congrArg
  refine Equiv.ext (fun x => ?_)
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl]
  by_cases hx : x ∈ Finset.image f Finset.univ
  · rw [markEmbeddingSet_on_mem f x hx, markEmbeddingSet_on_mem g (e x) (by simpa [← he] using hx)]
    subst he
    simp only [Sum.map_inr, id_eq, Sum.inr.injEq, Equiv.symm_apply_eq,
      Function.Embedding.toEquivRange_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
    change x = f.toEquivRange _
    rw [Equiv.apply_symm_apply]
  · rw [markEmbeddingSet_on_not_mem f x hx,
      markEmbeddingSet_on_not_mem g (e x) (by simpa [← he] using hx)]
    subst he
    rfl

lemma markEmbedding_mapIso_left {n m : ℕ} (e : Fin n ≃ Fin m) (f : Fin n ↪ X) (g : Fin m ↪ X)
    (he : e.symm.toEmbedding.trans f = g) (T : RealLorentzTensor d X) :
    markEmbedding g T = mapIso d (Equiv.sumCongr (Equiv.subtypeEquivRight (fun x => by
     simpa [← he] using Equiv.forall_congr_left e)) e) (markEmbedding f T) := by
  rw [markEmbedding, markEmbedding]
  erw [← Equiv.trans_apply]
  rw [mapIso_trans]
  apply congrFun
  repeat apply congrArg
  refine Equiv.ext (fun x => ?_)
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply]
  by_cases hx : x ∈ Finset.image f Finset.univ
  · rw [markEmbeddingSet_on_mem f x hx, markEmbeddingSet_on_mem g x (by
      simp [← he, hx]
      obtain ⟨y, _, hy2⟩ := Finset.mem_image.mp hx
      use e y
      simpa using hy2)]
    subst he
    simp [Equiv.symm_apply_eq]
    change x = f.toEquivRange _
    rw [Equiv.apply_symm_apply]
  · rw [markEmbeddingSet_on_not_mem f x hx, markEmbeddingSet_on_not_mem g x (by
      simpa [← he, hx] using fun x => not_exists.mp (Finset.mem_image.mpr.mt hx) (e.symm x))]
    subst he
    rfl

/-!

## Marking a single element

-/

/-- An embedding from `Fin 1` into `X` given an element `x ∈ X`. -/
@[simps!]
def embedSingleton (x : X) : Fin 1 ↪ X :=
  ⟨![x], fun x y => by fin_cases x; fin_cases y; simp⟩

lemma embedSingleton_toEquivRange_symm (x : X) :
    (embedSingleton x).toEquivRange.symm ⟨x, by simp⟩ = 0 := by
  exact Fin.fin_one_eq_zero _

/-- Equivalence, taking a tensor to a tensor with a single marked index. -/
@[simps!]
def markSingle (x : X) : RealLorentzTensor d X ≃ Marked d {x' // x' ≠ x} 1 :=
  (markEmbedding (embedSingleton x)).trans
  (mapIso d (Equiv.sumCongr (Equiv.subtypeEquivRight (fun x => by simp)) (Equiv.refl _)))

/-- Equivalence between index values of a tensor and the corresponding tensor with a single
  marked index. -/
@[simps!]
def markSingleIndexValue (T : RealLorentzTensor d X) (x : X) :
    IndexValue d T.color ≃ IndexValue d (markSingle x T).color :=
  (markEmbeddingIndexValue (embedSingleton x) T).trans <|
  indexValueIso d (Equiv.sumCongr (Equiv.subtypeEquivRight (fun x => by simp)) (Equiv.refl _))
   (by funext x_1; simp)

/-- Given an equivalence of types, taking `x` to `y` the corresponding equivalence of
  subtypes of elements not equal to `x` and not equal to `y` respectively. -/
@[simps!]
def equivSingleCompl (e : X ≃ Y) {x : X} {y : Y} (he : e x = y) :
    {x' // x' ≠ x} ≃ {y' // y' ≠ y} :=
  (Equiv.subtypeEquivOfSubtype' e).trans <|
  Equiv.subtypeEquivRight (fun a => by simp [Equiv.symm_apply_eq, he])

lemma markSingle_mapIso (e : X ≃ Y) (x : X) (y : Y) (he : e x = y)
    (T : RealLorentzTensor d X) : markSingle y (mapIso d e T) =
    mapIso d (Equiv.sumCongr (equivSingleCompl e he) (Equiv.refl _)) (markSingle x T) := by
  rw [markSingle, Equiv.trans_apply]
  rw [markEmbedding_mapIso_right e (embedSingleton x) (embedSingleton y)
    (Function.Embedding.ext_iff.mp (fun a => by simpa using he)), markSingle, markEmbedding]
  erw [← Equiv.trans_apply, ← Equiv.trans_apply, ← Equiv.trans_apply]
  rw [mapIso_trans, mapIso_trans, mapIso_trans, mapIso_trans]
  apply congrFun
  repeat apply congrArg
  refine Equiv.ext fun x => ?_
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.sumCongr_trans,
    Equiv.trans_refl, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_trans, Equiv.coe_refl,
    Sum.map_map, CompTriple.comp_eq]
  subst he
  rfl

/-!

## Marking two elements

-/

/-- An embedding from `Fin 2` given two inequivalent elements. -/
@[simps!]
def embedDoubleton (x y : X) (h : x ≠ y) : Fin 2 ↪ X :=
  ⟨![x, y], fun a b => by
    fin_cases a <;> fin_cases b <;> simp [h]
    exact h.symm⟩

end markingElements

end Marked

/-!

## Contraction of indices

-/

open Marked

/-- The contraction of the marked indices in a tensor with two marked indices. -/
def contr {X : Type} (T : Marked d X 2) (h : T.markedColor 0 = τ (T.markedColor 1)) :
    RealLorentzTensor d X where
  color := T.unmarkedColor
  coord := fun i =>
    ∑ x, T.coord (splitIndexValue.symm (i, T.twoMarkedIndexValue x $ colorsIndexDualCast h x))

/-! TODO: Following the ethos of modular operads, prove properties of contraction. -/

/-! TODO: Use `contr` to generalize to any pair of marked index. -/

/-!

## Rising and lowering indices

Rising or lowering an index corresponds to changing the color of that index.

-/

/-! TODO: Define the rising and lowering of indices using contraction with the metric. -/

/-!

## Graphical species and Lorentz tensors

-/

/-! TODO: From Lorentz tensors graphical species. -/
/-! TODO: Show that the action of the Lorentz group defines an action on the graphical species. -/

end RealLorentzTensor
