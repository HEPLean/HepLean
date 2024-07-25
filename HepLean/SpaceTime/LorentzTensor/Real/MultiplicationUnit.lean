/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Constructors
/-!

# Unit of multiplication of Real Lorentz Tensors

The definition of the unit is akin to the definition given in

[Raynor][raynor2021graphical]

for modular operads.

The main results of this file are:

- `mulUnit_right`: The multiplicative unit acts as a right unit for the multiplication of Lorentz
  tensors.
- `mulUnit_left`: The multiplicative unit acts as a left unit for the multiplication of Lorentz
  tensors.
- `mulUnit_lorentzAction`: The multiplicative unit is invariant under Lorentz transformations.

-/

namespace RealLorentzTensor

variable {d : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  (T : RealLorentzTensor d X) (c : X → Color) (Λ Λ' : LorentzGroup d) {μ : Color}

open Marked

/-!

## Unit of multiplication

-/

/-- The unit for the multiplication of Lorentz tensors. -/
def mulUnit (d : ℕ) (μ : Color) : Marked d (Fin 1) 1 :=
  match μ with
  | .up => mapIso d ((Equiv.emptySum Empty (Fin (1 + 1))).trans finSumFinEquiv.symm)
    (ofMatUpDown 1)
  | .down => mapIso d ((Equiv.emptySum Empty (Fin (1 + 1))).trans finSumFinEquiv.symm)
    (ofMatDownUp 1)

lemma mulUnit_up_coord : (mulUnit d Colors.up).coord = fun i =>
    (1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i (Sum.inl 0)) (i (Sum.inr 0)) := by
  rfl

lemma mulUnit_down_coord : (mulUnit d Colors.down).coord = fun i =>
    (1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i (Sum.inl 0)) (i (Sum.inr 0)) := by
  rfl

@[simp]
lemma mulUnit_markedColor (μ : Color) : (mulUnit d μ).markedColor 0 = τ μ := by
  cases μ
  case up => rfl
  case down => rfl

lemma mulUnit_dual_markedColor (μ : Color) : τ ((mulUnit d μ).markedColor 0) = μ := by
  cases μ
  case up => rfl
  case down => rfl

@[simp]
lemma mulUnit_unmarkedColor (μ : Color) : (mulUnit d μ).unmarkedColor 0 = μ := by
  cases μ
  case up => rfl
  case down => rfl

lemma mulUnit_unmarkedColor_eq_dual_marked (μ : Color) :
    (mulUnit d μ).unmarkedColor = τ ∘ (mulUnit d μ).markedColor := by
  funext x
  fin_cases x
  simp only [Fin.zero_eta, Fin.isValue, mulUnit_unmarkedColor, Function.comp_apply,
    mulUnit_markedColor]
  exact color_eq_dual_symm rfl

lemma mulUnit_coord_diag (μ : Color) (i : (mulUnit d μ).UnmarkedIndexValue) :
    (mulUnit d μ).coord (splitIndexValue.symm (i,
    indexValueDualIso d (mulUnit_unmarkedColor_eq_dual_marked μ) i)) = 1 := by
  cases μ
  case' up => rw [mulUnit_up_coord]
  case' down => rw [mulUnit_down_coord]
  all_goals
    simp only [mulUnit]
    symm
    simp_all only [Fin.isValue, Matrix.one_apply]
    split
    rfl
    next h => exact False.elim (h rfl)

lemma mulUnit_coord_off_diag (μ : Color) (i: (mulUnit d μ).UnmarkedIndexValue)
    (b : (mulUnit d μ).MarkedIndexValue)
    (hb : b ≠ indexValueDualIso d (mulUnit_unmarkedColor_eq_dual_marked μ) i) :
    (mulUnit d μ).coord (splitIndexValue.symm (i, b)) = 0 := by
  match μ with
  | Colors.up =>
    rw [mulUnit_up_coord]
    simp only [mulUnit, Matrix.one_apply, Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false,
      ne_eq]
    by_contra h
    have h1 : (indexValueDualIso d (mulUnit_unmarkedColor_eq_dual_marked (Colors.up)) i) = b := by
      funext a
      fin_cases a
      exact h
    exact hb (id (Eq.symm h1))
  | Colors.down =>
    rw [mulUnit_down_coord]
    simp only [mulUnit, Matrix.one_apply, Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false,
      ne_eq]
    by_contra h
    have h1 : (indexValueDualIso d (mulUnit_unmarkedColor_eq_dual_marked (Colors.down)) i) = b := by
      funext a
      fin_cases a
      exact h
    exact hb (id (Eq.symm h1))

lemma mulUnit_right (μ : Color) (T : Marked d X 1) (h : T.markedColor 0 = μ) :
    multMarked T (mulUnit d μ) (h.trans (mulUnit_dual_markedColor μ).symm) = T := by
  refine ext ?_ ?_
  · funext a
    match a with
    | .inl _ => rfl
    | .inr 0 =>
      simp only [Fin.isValue, mul_color, Sum.elim_inr, mulUnit_unmarkedColor]
      exact h.symm
  funext i
  rw [mulMarked_indexValue_right]
  change ∑ j,
    T.coord (splitIndexValue.symm ((indexValueTensorator i).1, _)) *
    (mulUnit d μ).coord (splitIndexValue.symm ((indexValueTensorator i).2, j)) = _
  let y := indexValueDualIso d (mulUnit_unmarkedColor_eq_dual_marked μ) (indexValueTensorator i).2
  erw [Finset.sum_eq_single_of_mem y]
  rw [mulUnit_coord_diag]
  simp only [Fin.isValue, mul_one]
  apply congrArg
  funext a
  match a with
  | .inl a =>
    change (indexValueTensorator i).1 a = _
    rfl
  | .inr 0 =>
    change oneMarkedIndexValue
      ((colorIndexDualCast (Eq.trans h (Eq.symm (mulUnit_dual_markedColor μ)))).symm
      (oneMarkedIndexValue.symm y)) 0 = _
    rw [indexValueIso_eq_symm, indexValueIso_symm_apply']
    simp only [Fin.isValue, oneMarkedIndexValue, colorIndexDualCast, colorIndexCast,
      Equiv.coe_fn_symm_mk, indexValueDualIso_apply, Equiv.trans_apply, Equiv.cast_apply,
      Equiv.symm_trans_apply, Equiv.cast_symm, Equiv.symm_symm, Equiv.apply_symm_apply, cast_cast,
      Equiv.coe_fn_mk, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq, mul_color,
      Sum.elim_inr, Equiv.refl_apply, cast_inj, y]
    rfl
  exact Finset.mem_univ y
  intro b _ hab
  rw [mul_eq_zero]
  apply Or.inr
  exact mulUnit_coord_off_diag μ (indexValueTensorator i).2 b hab

lemma mulUnit_left (μ : Color) (T : Marked d X 1) (h : T.markedColor 0 = μ) :
    multMarked (mulUnit d μ) T ((mulUnit_markedColor μ).trans (congrArg τ h.symm)) =
    mapIso d (Equiv.sumComm X (Fin 1)) T := by
  rw [← mult_symmd_symm, mulUnit_right]
  exact h

lemma mulUnit_lorentzAction (μ : Color) (Λ : LorentzGroup d) :
    Λ • mulUnit d μ = mulUnit d μ := by
  match μ with
  | Colors.up =>
    rw [mulUnit]
    simp only [Nat.reduceAdd]
    rw [← lorentzAction_mapIso]
    rw [lorentzAction_ofMatUpDown]
    repeat apply congrArg
    rw [mul_one]
    change (Λ * Λ⁻¹).1 = 1
    rw [mul_inv_self Λ]
    rfl
  | Colors.down =>
    rw [mulUnit]
    simp only [Nat.reduceAdd]
    rw [← lorentzAction_mapIso]
    rw [lorentzAction_ofMatDownUp]
    repeat apply congrArg
    rw [mul_one]
    change ((LorentzGroup.transpose Λ⁻¹) * LorentzGroup.transpose Λ).1 = 1
    have inv_transpose : (LorentzGroup.transpose Λ⁻¹) = (LorentzGroup.transpose Λ)⁻¹ := by
      simp [LorentzGroup.transpose]
    rw [inv_transpose]
    rw [inv_mul_self]
    rfl

end RealLorentzTensor
