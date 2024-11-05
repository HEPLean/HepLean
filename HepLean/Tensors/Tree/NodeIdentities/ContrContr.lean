/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

## Commutativity of two contractions

The order of two contractions can be swapped, once the indices have been
accordingly adjusted.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies}

/-- A structure containing two pairs of indices (i, j) and (k, l) to be sequentially
  contracted in a tensor. -/
structure ContrQuartet {n : ℕ} (c : Fin n.succ.succ.succ.succ → S.C) where
  /-- The first index of the first pair to be contracted. -/
  i : Fin n.succ.succ.succ.succ
  /-- The second index of the first pair to be contracted. -/
  j : Fin n.succ.succ.succ
  /-- The first index of the second pair to be contracted. -/
  k : Fin n.succ.succ
  /-- The second index of the second pair to be contracted. -/
  l : Fin n.succ
  /-- The condition on the first pair of indices permitting their contraction. -/
  hij : c (i.succAbove j) = S.τ (c i)
  /-- The condition on the second pair of indices permitting their contraction. -/
  hkl : (c ∘ i.succAbove ∘ j.succAbove) (k.succAbove l) = S.τ ((c ∘ i.succAbove ∘ j.succAbove) k)

namespace ContrQuartet
variable {n : ℕ} {c : Fin n.succ.succ.succ.succ → S.C} (q : ContrQuartet c)

/-- On swapping the order of contraction (notionally `(i, j) - (k, l)` vs `(k, l) - (i, j)`), this
  is the new `i` index. -/
def swapI : Fin n.succ.succ.succ.succ := q.i.succAbove (q.j.succAbove q.k)

/-- On swapping the order of contraction (notionally `(i, j) - (k, l)` vs `(k, l) - (i, j)`), this
  is the new `j` index. -/
def swapJ : Fin n.succ.succ.succ := (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i).succAbove
  ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l)

/-- On swapping the order of contraction (notionally `(i, j) - (k, l)` vs `(k, l) - (i, j)`), this
  is the new `k` index. -/
def swapK : Fin n.succ.succ := predAboveI
    ((predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i).succAbove
      ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l))
    (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i)

/-- On swapping the order of contraction (notionally `(i, j) - (k, l)` vs `(k, l) - (i, j)`), this
  is the new `l` index. -/
def swapL : Fin n.succ := predAboveI ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l)
  (predAboveI (q.j.succAbove q.k) q.j)

lemma swap_map_eq (x : Fin n) : (q.swapI.succAbove (q.swapJ.succAbove
    (q.swapK.succAbove (q.swapL.succAbove x)))) =
    (q.i.succAbove (q.j.succAbove (q.k.succAbove (q.l.succAbove x)))) := by
  rw [succAbove_succAbove_predAboveI q.j q.k]
  rw [succAbove_succAbove_predAboveI q.i]
  apply congrArg
  rw [succAbove_succAbove_predAboveI (predAboveI (q.j.succAbove q.k) q.j)]
  rw [succAbove_succAbove_predAboveI (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i)]
  rfl

@[simp]
lemma swapI_neq_i : ¬ q.swapI = q.i := by
  simp only [Nat.succ_eq_add_one, swapI]
  exact Fin.succAbove_ne q.i (q.j.succAbove q.k)

@[simp]
lemma swapI_neq_succAbove : ¬ q.swapI = q.i.succAbove q.j := by
  simp only [Nat.succ_eq_add_one, swapI]
  apply Function.Injective.ne Fin.succAbove_right_injective
  exact Fin.succAbove_ne q.j q.k

@[simp]
lemma swapI_neq_i_j_k_l_succAbove :
    ¬ q.swapI = q.i.succAbove (q.j.succAbove (q.k.succAbove q.l)) := by
  simp only [Nat.succ_eq_add_one, swapI]
  apply Function.Injective.ne Fin.succAbove_right_injective
  apply Function.Injective.ne Fin.succAbove_right_injective
  exact Fin.ne_succAbove q.k q.l

lemma swapJ_swapI_succAbove : q.swapI.succAbove q.swapJ = q.i.succAbove
    (q.j.succAbove (q.k.succAbove q.l)) := by
  simp only [swapI, swapJ]
  rw [← succAbove_succAbove_predAboveI]
  rw [← succAbove_succAbove_predAboveI]

lemma swapJ_eq_swapI_predAbove : q.swapJ = predAboveI q.swapI (q.i.succAbove
    (q.j.succAbove (q.k.succAbove q.l))) := by
  rw [predAboveI_eq_iff]
  exact swapJ_swapI_succAbove q
  exact swapI_neq_i_j_k_l_succAbove q

@[simp]
lemma swapK_swapJ_succAbove : (q.swapJ.succAbove q.swapK) = predAboveI q.swapI q.i := by
  rw [swapJ, swapK]
  rw [succsAbove_predAboveI]
  rfl
  exact Fin.succAbove_ne (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i)
      ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l)

@[simp]
lemma swapK_swapJ_swapI_succAbove : (q.swapI).succAbove (predAboveI q.swapI q.i) = q.i := by
  rw [succsAbove_predAboveI]
  simp

@[simp]
lemma swapL_swapK_swapJ_swapI_succAbove :
    q.swapI.succAbove (q.swapJ.succAbove (q.swapK.succAbove q.swapL)) = q.i.succAbove q.j := by
  rw [swapJ, swapK]
  rw [← succAbove_succAbove_predAboveI]
  rw [swapI]
  rw [← succAbove_succAbove_predAboveI]
  apply congrArg
  rw [swapL]
  rw [succsAbove_predAboveI, succsAbove_predAboveI]
  exact Fin.succAbove_ne q.j q.k
  exact Fin.succAbove_ne (predAboveI (q.j.succAbove q.k) q.j) q.l

/-- The `ContrQuartet` corresponding to swapping the order of contraction
  (notionally `(i, j) - (k, l)` vs `(k, l) - (i, j)`). -/
def swap : ContrQuartet c where
  i := q.swapI
  j := q.swapJ
  k := q.swapK
  l := q.swapL
  hij := by
    rw [swapJ_swapI_succAbove, swapI]
    simpa using q.hkl
  hkl := by
    simpa using q.hij

noncomputable section

/-- The contraction map for the first pair of indices. -/
def contrMapFst := S.contrMap c q.i q.j q.hij

/-- The contractoin map for the second pair of indices. -/
def contrMapSnd := S.contrMap (c ∘ q.i.succAbove ∘ q.j.succAbove) q.k q.l q.hkl

/-- The homomorphism one must apply on swapping the order of contractions. -/
def contrSwapHom : (OverColor.mk ((c ∘ q.swap.i.succAbove ∘ q.swap.j.succAbove) ∘
    q.swap.k.succAbove ∘ q.swap.l.succAbove)) ⟶
    (OverColor.mk fun x => c (q.i.succAbove (q.j.succAbove (q.k.succAbove (q.l.succAbove x))))) :=
  (mkIso (funext fun x => congrArg c (swap_map_eq q x))).hom

lemma contrSwapHom_contrMapSnd_tprod (x : (i : (𝟭 Type).obj (OverColor.mk c).left) →
    CoeSort.coe (S.FD.obj { as := (OverColor.mk c).hom i })) :
    ((lift.obj S.FD).map q.contrSwapHom).hom
    (q.swap.contrMapSnd.hom ((PiTensorProduct.tprod S.k) fun k =>
    x (q.swap.i.succAbove (q.swap.j.succAbove k)))) = ((S.castToField
    ((S.contr.app { as := (c ∘ q.swap.i.succAbove ∘ q.swap.j.succAbove) q.swap.k }).hom
    (x (q.swap.i.succAbove (q.swap.j.succAbove q.swap.k)) ⊗ₜ[S.k]
    (S.FD.map (Discrete.eqToHom q.swap.hkl)).hom
    (x (q.swap.i.succAbove (q.swap.j.succAbove (q.swap.k.succAbove q.swap.l))))))) •
    ((lift.obj S.FD).map q.contrSwapHom).hom ((PiTensorProduct.tprod S.k) fun k =>
    x (q.swap.i.succAbove (q.swap.j.succAbove (q.swap.k.succAbove (q.swap.l.succAbove k)))))) := by
  rw [contrMapSnd,TensorSpecies.contrMap_tprod]
  change ((lift.obj S.FD).map q.contrSwapHom).hom
    (_ • ((PiTensorProduct.tprod S.k) fun k =>
        x (q.swap.i.succAbove (q.swap.j.succAbove
        (q.swap.k.succAbove (q.swap.l.succAbove k)))) :
        S.F.obj (OverColor.mk ((c ∘ q.swap.i.succAbove ∘ q.swap.j.succAbove) ∘
        q.swap.k.succAbove ∘ q.swap.l.succAbove)))) = _
  rw [map_smul]
  rfl

lemma contrSwapHom_tprod (x : (i : (𝟭 Type).obj (OverColor.mk c).left) →
    CoeSort.coe (S.FD.obj { as := (OverColor.mk c).hom i })) :
    ((PiTensorProduct.tprod S.k)
    fun k => x (q.i.succAbove (q.j.succAbove (q.k.succAbove (q.l.succAbove k))))) =
    ((lift.obj S.FD).map q.contrSwapHom).hom
    ((PiTensorProduct.tprod S.k) fun k =>
      x (q.swap.i.succAbove (q.swap.j.succAbove (q.swap.k.succAbove (q.swap.l.succAbove k))))) := by
  rw [lift.map_tprod]
  apply congrArg
  funext i
  simp only [Nat.succ_eq_add_one, mk_hom, Function.comp_apply]
  rw [lift.discreteFunctorMapEqIso]
  change _ = (S.FD.map (Discrete.eqToIso _).hom).hom _
  have h1' {a b : Fin n.succ.succ.succ.succ} (h : a = b) :
      x b = (S.FD.map (Discrete.eqToIso (by rw [h])).hom).hom (x a) := by
      subst h
      simp
  exact h1' (q.swap_map_eq i)

lemma contrMapFst_contrMapSnd_swap :
    q.contrMapFst ≫ q.contrMapSnd = q.swap.contrMapFst ≫ q.swap.contrMapSnd ≫
    S.F.map q.contrSwapHom := by
  ext x
  change q.contrMapSnd.hom (q.contrMapFst.hom x) = (S.F.map q.contrSwapHom).hom
    (q.swap.contrMapSnd.hom (q.swap.contrMapFst.hom x))
  refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy]
  simp only [Nat.succ_eq_add_one, Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
    map_smul]
  apply congrArg
  rw [contrMapFst, contrMapFst]
  change q.contrMapSnd.hom ((S.contrMap c q.i q.j _).hom ((PiTensorProduct.tprod S.k) x)) =
    (S.F.map q.contrSwapHom).hom
    (q.swap.contrMapSnd.hom ((S.contrMap c q.swap.i q.swap.j _).hom
    ((PiTensorProduct.tprod S.k) x)))
  rw [TensorSpecies.contrMap_tprod, TensorSpecies.contrMap_tprod]
  simp only [Nat.succ_eq_add_one, Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, map_smul]
  change _ •
    q.contrMapSnd.hom ((PiTensorProduct.tprod S.k) fun k => x (q.i.succAbove (q.j.succAbove k))) =
    S.castToField
    _ •
    ((lift.obj S.FD).map q.contrSwapHom).hom
      (q.swap.contrMapSnd.hom ((PiTensorProduct.tprod S.k)
      fun k => x (q.swap.i.succAbove (q.swap.j.succAbove k))))
  rw [contrMapSnd, TensorSpecies.contrMap_tprod, q.contrSwapHom_contrMapSnd_tprod]
  rw [smul_smul, smul_smul]
  congr 1
  /- The contractions. -/
  · nth_rewrite 1 [mul_comm]
    congr 1
    · congr 3
      have h1' {a b d: Fin n.succ.succ.succ.succ} (hbd : b = d) (h : c d = S.τ (c a))
          (h' : c b = S.τ (c a)) :
          (S.FD.map (Discrete.eqToHom (h))).hom (x d) =
          (S.FD.map (Discrete.eqToHom h')).hom (x b) := by
        subst hbd
        rfl
      refine h1' ?_ ?_ ?_
      erw [swapJ_swapI_succAbove]
      rfl
    · congr 1
      simp only [Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
        Nat.succ_eq_add_one, Function.comp_apply, Equivalence.symm_inverse,
        Action.functorCategoryEquivalence_functor,
        Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj,
        Discrete.functor_obj_eq_as]
      have h' {a a' b b' : Fin n.succ.succ.succ.succ} (hab : c b = S.τ (c a))
          (hab' : c b' = S.τ (c a')) (ha : a = a') (hb : b= b') :
          (S.contr.app { as := c a }).hom
          (x a ⊗ₜ[S.k] (S.FD.map (Discrete.eqToHom hab)).hom (x b)) =
          (S.contr.app { as := c a' }).hom (x a' ⊗ₜ[S.k]
          (S.FD.map (Discrete.eqToHom hab')).hom (x b')) := by
        subst ha hb
        rfl
      apply h'
      · simp only [Nat.succ_eq_add_one, swap, swapK_swapJ_succAbove, swapK_swapJ_swapI_succAbove]
      · simp only [Nat.succ_eq_add_one, swap, Function.comp_apply,
        swapL_swapK_swapJ_swapI_succAbove]
  /- The tensor-/
  · exact q.contrSwapHom_tprod _

lemma contr_contr (t : TensorTree S c) :
    (contr q.k q.l q.hkl (contr q.i q.j q.hij t)).tensor = (perm q.contrSwapHom
    (contr q.swapK q.swapL q.swap.hkl (contr q.swapI q.swapJ q.swap.hij t))).tensor := by
  simp only [contr_tensor, perm_tensor]
  trans (q.contrMapFst ≫ q.contrMapSnd).hom t.tensor
  simp only [Nat.succ_eq_add_one, contrMapFst, contrMapSnd, Action.comp_hom, ModuleCat.coe_comp,
    Function.comp_apply]
  rw [contrMapFst_contrMapSnd_swap]
  simp only [Nat.succ_eq_add_one, contrMapFst, contrMapSnd, Action.comp_hom, ModuleCat.coe_comp,
    Function.comp_apply, swap]
  apply congrArg
  apply congrArg
  apply congrArg
  rfl

end
end ContrQuartet

/-- The homomorphism one must apply on swapping the order of contractions.
  This is identical to `ContrQuartet.contrSwapHom` except manifestly between the correct
  types. -/
def contrContrPerm {n : ℕ} {c : Fin n.succ.succ.succ.succ → S.C} {i : Fin n.succ.succ.succ.succ}
    {j : Fin n.succ.succ.succ} {k : Fin n.succ.succ} {l : Fin n.succ}
    (hij : c (i.succAbove j) = S.τ (c i)) (hkl : (c ∘ i.succAbove ∘ j.succAbove) (k.succAbove l) =
    S.τ ((c ∘ i.succAbove ∘ j.succAbove) k)) :
    OverColor.mk ((c ∘ (ContrQuartet.mk i j k l hij hkl).swapI.succAbove ∘
      (ContrQuartet.mk i j k l hij hkl).swapJ.succAbove) ∘
      (ContrQuartet.mk i j k l hij hkl).swapK.succAbove ∘
      (ContrQuartet.mk i j k l hij hkl).swapL.succAbove) ⟶
    OverColor.mk
      ((c ∘ i.succAbove ∘ j.succAbove) ∘ k.succAbove ∘ l.succAbove) :=
  (ContrQuartet.mk i j k l hij hkl).contrSwapHom

/-- Contraction nodes commute on adjusting indices. -/
theorem contr_contr {n : ℕ} {c : Fin n.succ.succ.succ.succ → S.C} {i : Fin n.succ.succ.succ.succ}
    {j : Fin n.succ.succ.succ} {k : Fin n.succ.succ} {l : Fin n.succ}
    (hij : c (i.succAbove j) = S.τ (c i)) (hkl : (c ∘ i.succAbove ∘ j.succAbove) (k.succAbove l) =
    S.τ ((c ∘ i.succAbove ∘ j.succAbove) k))
    (t : TensorTree S c) :
    (contr k l hkl (contr i j hij t)).tensor =
    (perm (contrContrPerm hij hkl)
    (contr (ContrQuartet.mk i j k l hij hkl).swapK (ContrQuartet.mk i j k l hij hkl).swapL
    (ContrQuartet.mk i j k l hij hkl).swap.hkl (contr (ContrQuartet.mk i j k l hij hkl).swapI
    (ContrQuartet.mk i j k l hij hkl).swapJ
    (ContrQuartet.mk i j k l hij hkl).swap.hij t))).tensor :=
  (ContrQuartet.mk i j k l hij hkl).contr_contr t

end TensorTree
