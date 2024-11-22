/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.DualRepIso
/-!

# Pure tensors

A pure tensor is one of the form `ψ1 ⊗ ψ2 ⊗ ... ⊗ ψn`.
We say a tensor is pure if it is of this form.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

noncomputable section

namespace TensorSpecies
open TensorTree
variable (S : TensorSpecies)

/-- The type of tensors specified by a map to colors `c : OverColor S.C`. -/
def Pure (c : OverColor S.C) : Type := (i : c.left) → S.FD.obj (Discrete.mk (c.hom i))

namespace Pure

variable {S : TensorSpecies} {c : OverColor S.C}

/-- The group action on a pure tensor. -/
def ρ (g : S.G) (p : Pure S c) : Pure S c := fun i ↦ (S.FD.obj (Discrete.mk (c.hom i))).ρ g (p i)

/-- The underlying tensor of a pure tensor. -/
def tprod (p : Pure S c) : S.F.obj c := PiTensorProduct.tprod S.k p

/-- The map `tprod` is equivariant with respect to the group action. -/
lemma tprod_equivariant (g : S.G) (p : Pure S c) : (ρ g p).tprod = (S.F.obj c).ρ g p.tprod := by
  simp only [F_def, OverColor.lift, OverColor.lift.obj', OverColor.lift.objObj',
    OverColor.instMonoidalCategoryStruct_tensorUnit_left, Functor.id_obj,
    OverColor.instMonoidalCategoryStruct_tensorUnit_hom,
    OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Rep.coe_of, tprod, Rep.of_ρ,
    MonoidHom.coe_mk, OneHom.coe_mk, PiTensorProduct.map_tprod]
  rfl

end Pure

/-- A tensor is pure if it is `⨂[S.k] i, p i` for some `p : Pure c`. -/
def IsPure {c : OverColor S.C} (t : S.F.obj c) : Prop := ∃ p : Pure S c, t = p.tprod

/-- As long as we are dealing with tensors with at least one index, then the zero
  tensor is pure. -/
lemma zero_isPure {c : OverColor S.C} [h : Nonempty c.left] : @IsPure S c 0 := by
  refine ⟨fun i => 0, ?_⟩
  simp only [Pure.tprod, Functor.id_obj]
  change 0 = PiTensorProduct.tprodCoeff S.k 1 fun i => 0
  symm
  apply PiTensorProduct.zero_tprodCoeff' (1 : S.k)
  rfl
  exact (Classical.inhabited_of_nonempty h).default

@[simp]
lemma Pure.tprod_isPure {c : OverColor S.C} (p : Pure S c) : S.IsPure p.tprod := ⟨p, rfl⟩

@[simp]
lemma action_isPure_iff_isPure {c : OverColor S.C} {ψ : S.F.obj c} (g : S.G) :
    S.IsPure ((S.F.obj c).ρ g ψ) ↔ S.IsPure ψ := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨p, hp⟩ := h
    have hp' := congrArg ((S.F.obj c).ρ g⁻¹) hp
    simp only [Rep.ρ_inv_self_apply] at hp'
    rw [← Pure.tprod_equivariant] at hp'
    subst hp'
    exact Pure.tprod_isPure S (Pure.ρ g⁻¹ p)
  · obtain ⟨p, hp⟩ := h
    subst hp
    rw [← Pure.tprod_equivariant]
    exact Pure.tprod_isPure S (Pure.ρ g p)

end TensorSpecies

end
