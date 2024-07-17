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
 There are two possiblities, `up` and `down`. -/
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
@[simp]
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

/-- An equivalence of `ColorsIndex` types given an equality of a colors. -/
def colorsIndexCast {d : ℕ} {μ₁ μ₂ : RealLorentzTensor.Colors} (h : μ₁ = μ₂) :
    ColorsIndex d μ₁ ≃ ColorsIndex d μ₂ :=
  Equiv.cast (by rw [h])

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

instance [Fintype X] [DecidableEq X] : DecidableEq (IndexValue d c) :=
  Fintype.decidablePiFintype

/-!

## Induced isomorphisms between IndexValue sets

-/

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
    ext x : 2
    rfl
  simpa only [Equiv.symm_symm] using congrArg (fun e => e.symm) h1

lemma indexValueIso_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    (indexValueIso d f h).symm = indexValueIso d f.symm (by rw [h, Function.comp.assoc]; simp) := by
  ext i : 1
  rw [← Equiv.symm_apply_eq]
  funext y
  rw [indexValueIso_symm_apply', indexValueIso_symm_apply']
  simp [colorsIndexCast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.apply_symm_apply]

lemma indexValueIso_eq_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    indexValueIso d f h = (indexValueIso d f.symm (by rw [h, Function.comp.assoc]; simp)).symm := by
  rw [indexValueIso_symm]
  congr

@[simp]
lemma indexValueIso_refl (d : ℕ) (i : X → Colors) :
    indexValueIso d (Equiv.refl X) (rfl : i = i) = Equiv.refl _ := by
  rfl

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
  simp only [Function.comp.assoc, Equiv.symm_comp_self, CompTriple.comp_eq]

lemma mapIso_symm (f : X ≃ Y) : (mapIso d f).symm = mapIso d f.symm := by
  rfl

lemma mapIso_refl : mapIso d (Equiv.refl X) = Equiv.refl _ := rfl

/-!

## Sums

-/

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

instance [Fintype X] [DecidableEq X] (T : Marked d X n) : Fintype T.MarkedIndexValue :=
  Pi.fintype

instance [Fintype X] (T : Marked d X n) : DecidableEq T.MarkedIndexValue :=
  Fintype.decidablePiFintype

lemma color_eq_elim (T : Marked d X n) :
    T.color = Sum.elim T.unmarkedColor T.markedColor := by
  ext1 x
  cases' x <;> rfl

def splitIndexValue {T : Marked d X n} :
    IndexValue d T.color ≃ T.UnmarkedIndexValue × T.MarkedIndexValue :=
  (indexValueIso d (Equiv.refl _) T.color_eq_elim).trans
  indexValueSumEquiv

 @[simp]
lemma splitIndexValue_sum {T : Marked d X n} [Fintype X] [DecidableEq X]
    (P : T.UnmarkedIndexValue × T.MarkedIndexValue → ℝ) :
    ∑ i, P (splitIndexValue i) = ∑ j, ∑ k, P (j, k) := by
  rw [Equiv.sum_comp splitIndexValue, Fintype.sum_prod_type]

/-- Contruction of marked index values for the case of 1 marked index. -/
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

/-- Contruction of marked index values for the case of 2 marked index. -/
def twoMarkedIndexValue (T : Marked d X 2) (x : ColorsIndex d (T.color (markedPoint X 0)))
    (y : ColorsIndex d <| T.color <| markedPoint X 1) :
    T.MarkedIndexValue := fun i =>
  match i with
  | 0 => x
  | 1 => y

/-- An equivalence of types used to turn the first marked index into an unmarked index. -/
def unmarkFirstSet (X : Type) (n : ℕ) : (X ⊕ Fin n.succ) ≃
    (X ⊕ Fin 1) ⊕ Fin n :=
  trans (Equiv.sumCongr (Equiv.refl _) $
    (((Fin.castOrderIso (Nat.succ_eq_one_add n)).toEquiv.trans finSumFinEquiv.symm)))
  (Equiv.sumAssoc _ _ _).symm

/-- Unmark the first marked index of a marked thensor. -/
def unmarkFirst {X : Type} : Marked d X n.succ ≃ Marked d (X ⊕ Fin 1) n :=
  mapIso d (unmarkFirstSet X n)

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
