/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

## Swapping indices in a contraction

Swapping the indices in a single contraction.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies}

namespace ContrPair
variable {n : ℕ} {c : Fin n.succ.succ → S.C} (q : ContrPair c)

/-- On swapping the indices of a contraction (notionally `(i, j)` vs `(j, i)`), this
  is the new `i` index. -/
def swapI : Fin n.succ.succ := q.i.succAbove q.j

/-- On swapping the indices of a contraction (notionally `(i, j)` vs `(j, i)`), this
  is the new `j` index. -/
def swapJ : Fin n.succ := predAboveI (q.i.succAbove q.j) q.i

lemma swap_map_eq (x : Fin n) : (q.swapI.succAbove (q.swapJ.succAbove x)) =
    (q.i.succAbove (q.j.succAbove x)) := by
  rw [succAbove_succAbove_predAboveI q.i q.j]
  rfl

@[simp]
lemma swapJ_swapI_succAbove : q.swapI.succAbove q.swapJ = q.i := by
  rw [swapJ, swapI, succsAbove_predAboveI]
  exact Fin.succAbove_ne q.i q.j

/-- The `ContrPair` corresponding to swapping the indices, notionally `(i, j)` vs `(j, i)`. -/
def swap : ContrPair c where
  i := q.swapI
  j := q.swapJ
  h := by
    rw [swapJ_swapI_succAbove]
    simpa only [swapI, q.h] using (S.τ_involution _).symm

lemma swapI_color : c q.swapI = S.τ (c (q.i)) := by
  rw [swapI]
  exact q.h

@[simp]
lemma predAboveI_i_swapI : predAboveI q.i q.swapI = q.j := by
  rw [swapI]
  simp only [Nat.succ_eq_add_one, predAboveI_succAbove]

lemma swap_swap : q.swap.swap = q := by
  apply ext
  · simp only [Nat.succ_eq_add_one, swap]
    rw [swapI]
    simp only [swapJ_swapI_succAbove]
  · simp only [Nat.succ_eq_add_one, swap]
    rw [swapJ]
    simp only [swapJ_swapI_succAbove, predAboveI_i_swapI]

/-- The homomorphism one must apply on swapping indices in a contraction. -/
def contrSwapHom : (OverColor.mk (c ∘ q.swap.i.succAbove ∘ q.swap.j.succAbove)) ⟶
    (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)) :=
  (mkIso (funext fun x => congrArg c (swap_map_eq q x))).hom

lemma contrMap_swap : q.contrMap = q.swap.contrMap ≫ S.F.map q.contrSwapHom := by
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy]
  simp only [Nat.succ_eq_add_one, Functor.id_obj, mk_hom, PiTensorProduct.tprodCoeff_eq_smul_tprod,
    map_smul, Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply]
  apply congrArg
  rw [contrMap, contrMap]
  erw [TensorSpecies.contrMap_tprod, TensorSpecies.contrMap_tprod]
  simp only [Nat.succ_eq_add_one, Functor.id_obj, mk_hom, Function.comp_apply,
    Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, map_smul]
  have h1n' {a b d: Fin n.succ.succ} (hbd : b = d) (h : c d = S.τ (c a))
          (h' : c b = S.τ (c a)) :
          (S.FDiscrete.map (Discrete.eqToHom (h))).hom (x d) =
          (S.FDiscrete.map (Discrete.eqToHom h')).hom (x b) := by
        subst hbd
        rfl
  congr 1
  /- The contractions. -/
  · apply congrArg
    erw [S.contr_tmul_symm]
    have h1' : ∀ {a a' b c b' c'} (haa' : a = a')
        (_ : b = (S.FDiscrete.map (Discrete.eqToHom (by rw [haa']))).hom b')
        (_ : c = (S.FDiscrete.map (Discrete.eqToHom (by rw [haa']))).hom c'),
        (S.contr.app a).hom (b ⊗ₜ[S.k] c) = (S.contr.app a').hom (b' ⊗ₜ[S.k] c') := by
      intro a a' b c b' c'  haa' hbc hcc
      subst haa'
      simp_all
    refine h1' ?_ ?_ ?_
    · simp
      exact Eq.symm (swapI_color q)
    · refine h1n' ?_ ?_ ?_
      rfl
    · change _ = ((S.FDiscrete.map (Discrete.eqToHom _)) ≫ S.FDiscrete.map (Discrete.eqToHom _)).hom
        ( (x (q.swap.i.succAbove q.swap.j)))
      rw [← S.FDiscrete.map_comp]
      simp
      have h1nn' {a b d: Fin n.succ.succ} (hbd : b = d) (h : c d = S.τ (S.τ (c a))):
          (S.FDiscrete.map (Discrete.eqToHom (h))).hom (x d) =
          (S.FDiscrete.map (eqToHom (by
          subst hbd
          simp_all only [Nat.succ_eq_add_one, forall_true_left, Discrete.functor_obj_eq_as,
            Function.comp_apply, Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
            Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
            Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj, mk_hom]))).hom
            (x b) := by
        subst hbd
        rfl
      refine h1nn' ?_ ?_
      · simp only [Nat.succ_eq_add_one, swap, swapJ_swapI_succAbove]
  /- The tensor. -/
  · simp only [S.F_def]
    erw [lift.map_tprod]
    apply congrArg
    funext k
    have h1' {a b : Fin n.succ.succ} (h : a = b) :
      x b = (S.FDiscrete.map (Discrete.eqToIso (by rw [h])).hom).hom (x a) := by
      subst h
      simp only [Nat.succ_eq_add_one, mk_hom, eqToIso_refl, Iso.refl_hom, Discrete.functor_map_id,
        Action.id_hom, ModuleCat.id_apply]
    refine h1' ?_
    simp only [Nat.succ_eq_add_one, swap, Function.comp_apply]
    rw [swap_map_eq]
    rfl

lemma contr_swap (t : TensorTree S c) :
    (contr q.i q.j q.h t).tensor = (perm q.contrSwapHom
    (contr q.swapI q.swapJ q.swap.h t)).tensor := by
  simp only [contr_tensor, perm_tensor]
  change (q.contrMap).hom t.tensor = _
  rw [contrMap_swap]
  simp only [Nat.succ_eq_add_one, Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply]
  apply congrArg
  apply congrArg
  rfl

end ContrPair

/-- Swapping the nodes of a contraction. -/
theorem contr_swap {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ}
    {j : Fin n.succ} (hij : c (i.succAbove j) = S.τ (c i))
    (t : TensorTree S c) :
    (contr i j hij t).tensor = (perm (ContrPair.mk i j hij).contrSwapHom
    (contr (ContrPair.mk i j hij).swapI (ContrPair.mk i j hij).swapJ
    (ContrPair.mk i j hij).swap.h t)).tensor :=
  (ContrPair.mk i j hij).contr_swap t

end TensorTree
