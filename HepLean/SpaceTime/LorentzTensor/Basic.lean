/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Function.CompTypeclasses
import Mathlib.Data.Real.Basic
import Mathlib.CategoryTheory.FintypeCat
/-!

# Lorentz Tensors

In this file we define real Lorentz tensors.

We implicitly follow the definition of a modular operad.
This will relation should be made explicit in the future.

## References

-- For modular operads see: [Raynor][raynor2021graphical]

-/
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

/-- The association of colors with indices. For up and down this is `Fin 1 ⊕ Fin d`.-/
def RealLorentzTensor.ColorsIndex (d : ℕ) (μ : RealLorentzTensor.Colors) : Type :=
  match μ with
  | RealLorentzTensor.Colors.up => Fin 1 ⊕ Fin d
  | RealLorentzTensor.Colors.down => Fin 1 ⊕ Fin d

/-- A Lorentz Tensor defined by its coordinate map. -/
structure RealLorentzTensor (d : ℕ) (X : FintypeCat) where
  /-- The color associated to each index of the tensor. -/
  color : X → RealLorentzTensor.Colors
  /-- The coordinate map for the tensor. -/
  coord : ((x : X) → RealLorentzTensor.ColorsIndex d (color x)) → ℝ

namespace RealLorentzTensor
open CategoryTheory
universe u1
variable {d : ℕ} {X Y Z : FintypeCat.{u1}}

/-- An `IndexType` for a tensor is an element of
`(x : X) → RealLorentzTensor.ColorsIndex d (T.color x)`. -/
@[simp]
def IndexType (T : RealLorentzTensor d X) : Type u1 :=
  (x : X) → RealLorentzTensor.ColorsIndex d (T.color x)

lemma indexType_eq {T₁ T₂ : RealLorentzTensor d X} (h : T₁.color = T₂.color) :
    T₁.IndexType = T₂.IndexType := by
  simp only [IndexType]
  rw [h]

lemma ext {T₁ T₂ : RealLorentzTensor d X} (h : T₁.color = T₂.color)
    (h' :  T₁.coord  = T₂.coord ∘ Equiv.cast (indexType_eq h)) : T₁ = T₂ := by
  cases T₁
  cases T₂
  simp_all only [IndexType, mk.injEq]
  apply And.intro h
  simp only at h
  subst h
  simp only [Equiv.cast_refl, Equiv.coe_refl, CompTriple.comp_eq] at h'
  subst h'
  rfl

/-- The involution acting on colors. -/
def τ : Colors → Colors
  | Colors.up => Colors.down
  | Colors.down => Colors.up

/-- The map τ is an involution. -/
lemma τ_involutive : Function.Involutive τ := by
  intro x
  cases x <;> rfl

/-- The color associated with an element of `x ∈ X` for a tensor `T`. -/
def ch {X : FintypeCat} (x : X) (T : RealLorentzTensor d X) : Colors := T.color x

/-!

## Congruence

-/

/-- An equivalence between `X → Fin 1 ⊕ Fin d` and `Y → Fin 1 ⊕ Fin d` given an isomorphism
  between `X` and `Y`. -/
def congrSetIndexType (d : ℕ) (f : X ≃ Y) (i : X → Colors) :
    ((x : X) → ColorsIndex d (i x)) ≃ ((y : Y) → ColorsIndex d ((Equiv.piCongrLeft' _ f) i y))  :=
  Equiv.piCongrLeft' _ (f)

/-- Given an equivalence of indexing sets, a map on Lorentz tensors. -/
@[simps!]
def congrSetMap (f : X ≃ Y) (T : RealLorentzTensor d X) : RealLorentzTensor d Y where
  color := (Equiv.piCongrLeft' _ f) T.color
  coord := (Equiv.piCongrLeft' _ (congrSetIndexType d f T.color)) T.coord

lemma congrSetMap_trans (f : X ≃ Y) (g : Y ≃ Z) (T : RealLorentzTensor d X)  :
    congrSetMap g  (congrSetMap f T) = congrSetMap (f.trans g) T := by
  apply ext (by rfl)
  have h1 : (congrSetIndexType d (f.trans g) T.color) = (congrSetIndexType d f T.color).trans
    (congrSetIndexType d g ((Equiv.piCongrLeft' (fun _ => Colors) f) T.color)) := by
    simp only [Equiv.piCongrLeft'_apply, Equiv.symm_trans_apply, congrSetIndexType]
    exact Equiv.coe_inj.mp rfl
  simp only [congrSetMap, Equiv.piCongrLeft'_apply, IndexType, Equiv.symm_trans_apply, h1,
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

lemma congrSet_refl : @congrSet d _ _ (Equiv.refl X) = Equiv.refl _ := by
  rfl

/-!

## Multiplication

-/

/-! TODO: Following the ethos of modular operads, define multiplication of Lorentz tensors. -/

/-!

## Contraction of indices

-/

/-! TODO: Following the ethos of modular operads, define contraction of Lorentz tensors. -/

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
