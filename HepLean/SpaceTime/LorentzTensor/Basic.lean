/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Function.CompTypeclasses
import Mathlib.Data.Real.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
/-!

# Lorentz Tensors

In this file we define real Lorentz tensors.

We implicitly follow the definition of a modular operad.
This will relation should be made explicit in the future.

## References

-- For modular operads see: [Raynor][raynor2021graphical]

-/
/-! TODO: Replace `FintypeCat` throughout with `Type` and `Fintype`. -/
/-! TODO: Do complex tensors, with Van der Waerden notation for fermions. -/
/-! TODO: Generalize to maps into Lorentz tensors. -/
/-!

## Real Lorentz tensors

-/

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

/-- An `IndexValue` is a set of actual values an index can take. e.g. for a
  3-tensor (0, 1, 2). -/
@[simp]
def RealLorentzTensor.IndexValue {X : FintypeCat} (d : ℕ) (c : X → RealLorentzTensor.Colors) :
    Type 0 := (x : X) → RealLorentzTensor.ColorsIndex d (c x)

/-- A Lorentz Tensor defined by its coordinate map. -/
structure RealLorentzTensor (d : ℕ) (X : FintypeCat) where
  /-- The color associated to each index of the tensor. -/
  color : X → RealLorentzTensor.Colors
  /-- The coordinate map for the tensor. -/
  coord : RealLorentzTensor.IndexValue d color → ℝ

namespace RealLorentzTensor
open CategoryTheory
open Matrix
universe u1
variable {d : ℕ} {X Y Z : FintypeCat.{0}}

/-!

## Some equivalences in FintypeCat

These come in use casting Lorentz tensors.
There is likely a better way to deal with these castings.

-/

/-- An equivalence between an `X` which is empty and `FintypeCat.of Empty`. -/
def equivToEmpty (X : FintypeCat) [IsEmpty X] : X ≃ FintypeCat.of Empty :=
  Equiv.equivEmpty _

/-- An equivalence between an `X ⊕ Empty` and `X`. -/
def equivToSumEmpty (X : FintypeCat) : FintypeCat.of (X ⊕ Empty) ≃ X :=
  Equiv.sumEmpty (↑X) Empty

/-- An equivalence from `Empty ⊕ PUnit.{1}` to `Empty ⊕ Σ _ : Fin 1, PUnit`. -/
def equivPUnitToSigma :
    FintypeCat.of (Empty ⊕ PUnit.{1}) ≃ FintypeCat.of (Empty ⊕ Σ _ : Fin 1, PUnit) where
  toFun x := match x with
    | Sum.inr x => Sum.inr ⟨0, x⟩
  invFun x := match x with
    | Sum.inr ⟨0, x⟩ => Sum.inr x
  left_inv x := match x with
    | Sum.inr _ => rfl
  right_inv x := match x with
    | Sum.inr ⟨0, _⟩ => rfl

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

/-- The color associated with an element of `x ∈ X` for a tensor `T`. -/
def ch {X : FintypeCat} (x : X) (T : RealLorentzTensor d X) : Colors := T.color x

/-- An equivalence of `ColorsIndex` between that of a color and that of its dual. -/
def dualColorsIndex {d : ℕ} {μ : RealLorentzTensor.Colors}:
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

/-- An equivalence of `ColorsIndex` types given an equality of a colors. -/
def castColorsIndex {d : ℕ} {μ₁ μ₂ : RealLorentzTensor.Colors} (h : μ₁ = μ₂) :
    ColorsIndex d μ₁ ≃ ColorsIndex d μ₂ :=
  Equiv.cast (by rw [h])

/-- An equivalence of `ColorsIndex` types given an equality of a color and the dual of a color. -/
def congrColorsDual {μ ν : Colors} (h : μ = τ ν) :
    ColorsIndex d μ ≃ ColorsIndex d ν :=
  (castColorsIndex h).trans dualColorsIndex.symm

lemma congrColorsDual_symm {μ ν : Colors} (h : μ = τ ν) :
    (congrColorsDual h).symm =
    @congrColorsDual d _ _ ((Function.Involutive.eq_iff τ_involutive).mp h.symm) := by
  match μ, ν with
  | Colors.up, Colors.down => rfl
  | Colors.down, Colors.up => rfl

lemma color_eq_dual_symm {μ ν : Colors} (h : μ = τ ν) : ν = τ μ :=
  (Function.Involutive.eq_iff τ_involutive).mp h.symm

/-!

## Index values

-/

/-- An equivalence of Index values from an equality of color maps. -/
def castIndexValue {X : FintypeCat} {T S : X → Colors} (h : T = S) :
    IndexValue d T ≃ IndexValue d S where
  toFun i := (fun μ => castColorsIndex (congrFun h μ) (i μ))
  invFun i := (fun μ => (castColorsIndex (congrFun h μ)).symm (i μ))
  left_inv i := by
    simp
  right_inv i := by
    simp

lemma indexValue_eq {T₁ T₂ : X → RealLorentzTensor.Colors} (d : ℕ) (h : T₁ = T₂) :
    IndexValue d T₁ = IndexValue d T₂ :=
  pi_congr fun a => congrArg (ColorsIndex d) (congrFun h a)

/-!

## Extensionality

-/

lemma ext {T₁ T₂ : RealLorentzTensor d X} (h : T₁.color = T₂.color)
    (h' : T₁.coord = T₂.coord ∘ Equiv.cast (indexValue_eq d h)) : T₁ = T₂ := by
  cases T₁
  cases T₂
  simp_all only [IndexValue, mk.injEq]
  apply And.intro h
  simp only at h
  subst h
  simp only [Equiv.cast_refl, Equiv.coe_refl, CompTriple.comp_eq] at h'
  subst h'
  rfl

lemma ext' {T₁ T₂ : RealLorentzTensor d X} (h : T₁.color = T₂.color)
    (h' : T₁.coord = fun i => T₂.coord (castIndexValue h i)) :
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

## Congruence

-/

/-- An equivalence between `X → Fin 1 ⊕ Fin d` and `Y → Fin 1 ⊕ Fin d` given an isomorphism
  between `X` and `Y`. -/
def congrSetIndexValue (d : ℕ) (f : X ≃ Y) (i : X → Colors) :
    IndexValue d i ≃ IndexValue d (i ∘ f.symm) :=
  Equiv.piCongrLeft' _ f

/-- Given an equivalence of indexing sets, a map on Lorentz tensors. -/
@[simps!]
def congrSetMap (f : X ≃ Y) (T : RealLorentzTensor d X) : RealLorentzTensor d Y where
  color := T.color ∘ f.symm
  coord := T.coord ∘ (congrSetIndexValue d f T.color).symm

lemma congrSetMap_trans (f : X ≃ Y) (g : Y ≃ Z) (T : RealLorentzTensor d X) :
    congrSetMap g (congrSetMap f T) = congrSetMap (f.trans g) T := by
  apply ext (by rfl)
  have h1 : (congrSetIndexValue d (f.trans g) T.color) = (congrSetIndexValue d f T.color).trans
    (congrSetIndexValue d g ((Equiv.piCongrLeft' (fun _ => Colors) f) T.color)) := by
    exact Equiv.coe_inj.mp rfl
  simp only [congrSetMap, Equiv.piCongrLeft'_apply, IndexValue, Equiv.symm_trans_apply, h1,
    Equiv.cast_refl, Equiv.coe_refl, CompTriple.comp_eq]
  rfl

/-- An equivalence of Tensors given an equivalence of underlying sets. -/
@[simps!]
def congrSet (f : X ≃ Y) : RealLorentzTensor d X ≃ RealLorentzTensor d Y where
  toFun := congrSetMap f
  invFun := congrSetMap f.symm
  left_inv T := by
    rw [congrSetMap_trans, Equiv.self_trans_symm]
    rfl
  right_inv T := by
    rw [congrSetMap_trans, Equiv.symm_trans_self]
    rfl

lemma congrSet_trans (f : X ≃ Y) (g : Y ≃ Z) :
    (@congrSet d _ _ f).trans (congrSet g) = congrSet (f.trans g) := by
  refine Equiv.coe_inj.mp ?_
  funext T
  exact congrSetMap_trans f g T

lemma congrSet_refl : @congrSet d _ _ (Equiv.refl X) = Equiv.refl _ := rfl

/-!

## Sums

-/

/-- An equivalence through commuting sums between types casted from `FintypeCat.of`. -/
def sumCommFintypeCat (X Y : FintypeCat) : FintypeCat.of (X ⊕ Y) ≃ FintypeCat.of (Y ⊕ X) :=
  Equiv.sumComm X Y

/-- The sum of two color maps. -/
def sumElimIndexColor (Tc : X → Colors) (Sc : Y → Colors) :
    FintypeCat.of (X ⊕ Y) → Colors :=
  Sum.elim Tc Sc

/-- The symmetry property on `sumElimIndexColor`. -/
lemma sumElimIndexColor_symm (Tc : X → Colors) (Sc : Y → Colors) : sumElimIndexColor Tc Sc =
    Equiv.piCongrLeft' _ (Equiv.sumComm X Y).symm (sumElimIndexColor Sc Tc) := by
  ext1 x
  simp_all only [Equiv.piCongrLeft'_apply, Equiv.sumComm_symm, Equiv.sumComm_apply]
  cases x <;> rfl

/-- The sum of two index values for different color maps. -/
@[simp]
def sumElimIndexValue {X Y : FintypeCat} {TX : X → Colors} {TY : Y → Colors}
    (i : IndexValue d TX) (j : IndexValue d TY) :
    IndexValue d (sumElimIndexColor TX TY) :=
  fun c => match c with
  | Sum.inl x => i x
  | Sum.inr x => j x

/-- The projection of an index value on a sum of color maps to its left component. -/
def inlIndexValue {Tc : X → Colors} {Sc : Y → Colors} (i : IndexValue d (sumElimIndexColor Tc Sc)) :
    IndexValue d Tc := fun x => i (Sum.inl x)

/-- The projection of an index value on a sum of color maps to its right component. -/
def inrIndexValue {Tc : X → Colors} {Sc : Y → Colors}
    (i : IndexValue d (sumElimIndexColor Tc Sc)) :
  IndexValue d Sc := fun y => i (Sum.inr y)

/-- An equivalence between index values formed by commuting sums. -/
def sumCommIndexValue {X Y : FintypeCat} (Tc : X → Colors) (Sc : Y → Colors) :
    IndexValue d (sumElimIndexColor Tc Sc) ≃ IndexValue d (sumElimIndexColor Sc Tc) :=
  (congrSetIndexValue d (sumCommFintypeCat X Y) (sumElimIndexColor Tc Sc)).trans
  (castIndexValue (sumElimIndexColor_symm Sc Tc).symm)

lemma sumCommIndexValue_inlIndexValue {X Y : FintypeCat} {Tc : X → Colors} {Sc : Y → Colors}
    (i : IndexValue d <| sumElimIndexColor Tc Sc) :
    inlIndexValue (sumCommIndexValue Tc Sc i) = inrIndexValue i := rfl

lemma sumCommIndexValue_inrIndexValue {X Y : FintypeCat} {Tc : X → Colors} {Sc : Y → Colors}
    (i : IndexValue d <| sumElimIndexColor Tc Sc) :
    inrIndexValue (sumCommIndexValue Tc Sc i) = inlIndexValue i := rfl

/-- Equivalence between sets of `RealLorentzTensor` formed by commuting sums. -/
@[simps!]
def sumComm : RealLorentzTensor d (FintypeCat.of (X ⊕ Y))
    ≃ RealLorentzTensor d (FintypeCat.of (Y ⊕ X)) := congrSet (Equiv.sumComm X Y)

/-!

## Marked Lorentz tensors

To define contraction and multiplication of Lorentz tensors we need to mark indices.

-/

/-- A `RealLorentzTensor` with `n` marked indices. -/
def Marked (d : ℕ) (X : FintypeCat) (n : ℕ) : Type :=
  RealLorentzTensor d (FintypeCat.of (X ⊕ Σ _ : Fin n, PUnit))

namespace Marked

variable {n m : ℕ}

/-- The marked point. -/
def markedPoint (X : FintypeCat) (i : Fin n) : FintypeCat.of (X ⊕ Σ _ : Fin n, PUnit) :=
  Sum.inr ⟨i, PUnit.unit⟩

/-- The colors of unmarked indices. -/
def unmarkedColor (T : Marked d X n) : X → Colors :=
  T.color ∘ Sum.inl

/-- The colors of marked indices. -/
def markedColor (T : Marked d X n) : FintypeCat.of (Σ _ : Fin n, PUnit) → Colors :=
  T.color ∘ Sum.inr

/-- The index values restricted to unmarked indices. -/
def UnmarkedIndexValue (T : Marked d X n) : Type :=
  IndexValue d T.unmarkedColor

/-- The index values restricted to marked indices. -/
def MarkedIndexValue (T : Marked d X n) : Type :=
  IndexValue d T.markedColor

lemma sumElimIndexColor_of_marked (T : Marked d X n) :
    sumElimIndexColor T.unmarkedColor T.markedColor = T.color := by
  ext1 x
  cases' x <;> rfl

/-- Contruction of marked index values for the case of 1 marked index. -/
def oneMarkedIndexValue (T : Marked d X 1) (x : ColorsIndex d (T.color (markedPoint X 0))) :
    T.MarkedIndexValue := fun i => match i with
  | ⟨0, PUnit.unit⟩ => x

/-- Contruction of marked index values for the case of 2 marked index. -/
def twoMarkedIndexValue (T : Marked d X 2) (x : ColorsIndex d (T.color (markedPoint X 0)))
    (y : ColorsIndex d (T.color (markedPoint X 1))) :
    T.MarkedIndexValue := fun i =>
  match i with
  | ⟨0, PUnit.unit⟩ => x
  | ⟨1, PUnit.unit⟩ => y

/-- An equivalence of types used to turn the first marked index into an unmarked index. -/
def unmarkFirstSet (X : FintypeCat) (n : ℕ) : FintypeCat.of (X ⊕ Σ _ : Fin n.succ, PUnit) ≃
    FintypeCat.of ((X ⊕ PUnit) ⊕ Σ _ : Fin n, PUnit) where
  toFun x := match x with
    | Sum.inl x => Sum.inl (Sum.inl x)
    | Sum.inr ⟨0, PUnit.unit⟩ => Sum.inl (Sum.inr PUnit.unit)
    | Sum.inr ⟨⟨Nat.succ i, h⟩, PUnit.unit⟩ => Sum.inr ⟨⟨i, Nat.succ_lt_succ_iff.mp h⟩, PUnit.unit⟩
  invFun x := match x with
    | Sum.inl (Sum.inl x) => Sum.inl x
    | Sum.inl (Sum.inr PUnit.unit) => Sum.inr ⟨0, PUnit.unit⟩
    | Sum.inr ⟨⟨i, h⟩, PUnit.unit⟩ => Sum.inr ⟨⟨Nat.succ i, Nat.succ_lt_succ h⟩, PUnit.unit⟩
  left_inv x := by match x with
    | Sum.inl x => rfl
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
    | Sum.inr ⟨⟨Nat.succ i, h⟩, PUnit.unit⟩ => rfl
  right_inv x := by match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr PUnit.unit) => rfl
    | Sum.inr ⟨⟨i, h⟩, PUnit.unit⟩ => rfl

/-- Unmark the first marked index of a marked thensor. -/
def unmarkFirst {X : FintypeCat} : Marked d X n.succ ≃ Marked d (FintypeCat.of (X ⊕ PUnit)) n :=
  congrSet (unmarkFirstSet X n)

end Marked

/-!

## Multiplication

-/
open Marked

/-- The contraction of the marked indices of two tensors each with one marked index, which
is dual to the others. The contraction is done via
`φ^μ ψ_μ = φ^0 ψ_0 + φ^1 ψ_1 + ...`. -/
@[simps!]
def mul {X Y : FintypeCat} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor ⟨0, PUnit.unit⟩ = τ (S.markedColor ⟨0, PUnit.unit⟩)) :
    RealLorentzTensor d (FintypeCat.of (X ⊕ Y)) where
  color := sumElimIndexColor T.unmarkedColor S.unmarkedColor
  coord := fun i => ∑ x,
    T.coord (castIndexValue T.sumElimIndexColor_of_marked $
      sumElimIndexValue (inlIndexValue i) (T.oneMarkedIndexValue x)) *
    S.coord (castIndexValue S.sumElimIndexColor_of_marked $
      sumElimIndexValue (inrIndexValue i) (S.oneMarkedIndexValue $ congrColorsDual h x))

/-- Multiplication is well behaved with regard to swapping tensors. -/
lemma sumComm_mul {X Y : FintypeCat} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor ⟨0, PUnit.unit⟩ = τ (S.markedColor ⟨0, PUnit.unit⟩)) :
    sumComm (mul T S h) = mul S T (color_eq_dual_symm h) := by
  refine ext' (sumElimIndexColor_symm S.unmarkedColor T.unmarkedColor).symm ?_
  change (mul T S h).coord ∘
    (congrSetIndexValue d (sumCommFintypeCat X Y) (mul T S h).color).symm = _
  rw [Equiv.comp_symm_eq]
  funext i
  simp only [mul_coord, IndexValue, mul_color, Function.comp_apply, sumComm_apply_color]
  erw [sumCommIndexValue_inlIndexValue, sumCommIndexValue_inrIndexValue,
    ← Equiv.sum_comp (congrColorsDual h)]
  refine Fintype.sum_congr _ _ (fun a => ?_)
  rw [mul_comm]
  repeat apply congrArg
  rw [← congrColorsDual_symm h]
  exact (Equiv.apply_eq_iff_eq_symm_apply <| congrColorsDual h).mp rfl

/-! TODO: Following the ethos of modular operads, prove properties of multiplication. -/

/-! TODO: Use `mul` to generalize to any pair of marked index. -/
/-!

## Contraction of indices

-/

/-- The contraction of the marked indices in a tensor with two marked indices. -/
def contr {X : FintypeCat} (T : Marked d X 2)
    (h : T.markedColor ⟨0, PUnit.unit⟩ = τ (T.markedColor ⟨1, PUnit.unit⟩)) :
    RealLorentzTensor d X where
  color := T.unmarkedColor
  coord := fun i =>
    ∑ x, T.coord (castIndexValue T.sumElimIndexColor_of_marked $
      sumElimIndexValue i $ T.twoMarkedIndexValue x $ congrColorsDual h x)

/-! TODO: Following the ethos of modular operads, prove properties of contraction. -/

/-! TODO: Use `contr` to generalize to any pair of marked index. -/

/-!

# Tensors from reals, vectors and matrices

Note that that these definitions are not equivariant with respect to an
action of the Lorentz group. They are provided for constructive purposes.

-/

/-- A 0-tensor from a real number. -/
def ofReal (d : ℕ) (r : ℝ) : RealLorentzTensor d (FintypeCat.of Empty) where
  color := fun _ => Colors.up
  coord := fun _ => r

/-- A marked 1-tensor with a single up index constructed from a vector.

  Note: This is not the same as rising indices on `ofVecDown`. -/
def ofVecUp {d : ℕ} (v : Fin 1 ⊕ Fin d → ℝ) :
    Marked d (FintypeCat.of Empty) 1 where
  color := fun _ => Colors.up
  coord := fun i => v (i (Sum.inr ⟨0, PUnit.unit⟩))

/-- A marked 1-tensor with a single down index constructed from a vector.

  Note: This is not the same as lowering indices on `ofVecUp`. -/
def ofVecDown {d : ℕ} (v : Fin 1 ⊕ Fin d → ℝ) :
    Marked d (FintypeCat.of Empty) 1 where
  color := fun _ => Colors.down
  coord := fun i => v (i (Sum.inr ⟨0, PUnit.unit⟩))

/-- A tensor with two up indices constructed from a matrix.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
def ofMatUpUp {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d (FintypeCat.of Empty) 2 where
  color := fun _ => Colors.up
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- A tensor with two down indices constructed from a matrix.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
def ofMatDownDown {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d (FintypeCat.of Empty) 2 where
  color := fun _ => Colors.down
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- A marked 2-tensor with the first index up and the second index down.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
@[simps!]
def ofMatUpDown {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d (FintypeCat.of Empty) 2 where
  color := fun i => match i with
  | Sum.inr ⟨0, PUnit.unit⟩ => Colors.up
  | Sum.inr ⟨1, PUnit.unit⟩ => Colors.down
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- A marked 2-tensor with the first index down and the second index up.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
def ofMatDownUp {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d (FintypeCat.of Empty) 2 where
  color := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => Colors.down
    | Sum.inr ⟨1, PUnit.unit⟩ => Colors.up
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- Contracting the indices of `ofMatUpDown` returns the trace of the matrix. -/
lemma contr_ofMatUpDown_eq_trace {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contr (ofMatUpDown M) (by rfl) = ofReal d M.trace := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    simp only [Fin.isValue, contr, IndexValue, Equiv.cast_apply, trace, diag_apply, ofReal,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    apply Finset.sum_congr rfl
    intro x _
    rfl

/-- Contracting the indices of `ofMatDownUp` returns the trace of the matrix. -/
lemma contr_ofMatDownUp_eq_trace {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contr (ofMatDownUp M) (by rfl) = ofReal d M.trace := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    rfl

/-- Multiplying `ofVecUp` with `ofVecDown` gives the dot product. -/
@[simp]
lemma mul_ofVecUp_ofVecDown_eq_dot_prod {d : ℕ} (v₁ v₂ : Fin 1 ⊕ Fin d → ℝ) :
    congrSet (@equivToEmpty (FintypeCat.of (Empty ⊕ Empty)) instIsEmptySum)
    (mul (ofVecUp v₁) (ofVecDown v₂) (by rfl)) = ofReal d (v₁ ⬝ᵥ v₂) := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    rfl

/-- Multiplying `ofVecDown` with `ofVecUp` gives the dot product. -/
@[simp]
lemma mul_ofVecDown_ofVecUp_eq_dot_prod {d : ℕ} (v₁ v₂ : Fin 1 ⊕ Fin d → ℝ) :
    congrSet (@equivToEmpty (FintypeCat.of (Empty ⊕ Empty)) instIsEmptySum)
    (mul (ofVecDown v₁) (ofVecUp v₂) (by rfl)) = ofReal d (v₁ ⬝ᵥ v₂) := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    rfl

lemma mul_ofMatUpDown_ofVecUp_eq_mulVec {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (v : Fin 1 ⊕ Fin d → ℝ) :
    congrSet ((equivToSumEmpty (FintypeCat.of (Empty ⊕ PUnit.{1}))).trans equivPUnitToSigma)
    (mul (unmarkFirst (ofMatUpDown M)) (ofVecUp v) (by rfl)) = ofVecUp (M *ᵥ v) := by
  refine ext' ?_ ?_
  · funext i
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, congrSet_apply_color, mul_color, Equiv.symm_symm]
    fin_cases i
    rfl
  · funext i
    rfl

lemma mul_ofMatDownUp_ofVecDown_eq_mulVec {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (v : Fin 1 ⊕ Fin d → ℝ) :
    congrSet ((equivToSumEmpty (FintypeCat.of (Empty ⊕ PUnit.{1}))).trans equivPUnitToSigma)
    (mul (unmarkFirst (ofMatDownUp M)) (ofVecDown v) (by rfl)) = ofVecDown (M *ᵥ v) := by
  refine ext' ?_ ?_
  · funext i
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, congrSet_apply_color, mul_color, Equiv.symm_symm]
    fin_cases i
    rfl
  · funext i
    rfl

/-!

## Rising and lowering indices

Rising or lowering an index corresponds to changing the color of that index.

-/

/-! TODO: Define the rising and lowering of indices using contraction with the metric. -/

/-!

## Action of the Lorentz group

-/

/-! TODO: Define the action of the Lorentz group on the sets of Tensors. -/

/-!

## Graphical species and Lorentz tensors

-/

/-! TODO: From Lorentz tensors graphical species. -/
/-! TODO: Show that the action of the Lorentz group defines an action on the graphical species. -/

end RealLorentzTensor
