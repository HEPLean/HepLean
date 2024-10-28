/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

## Products and contractions


-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies}

namespace ContrPair
variable {n n1 : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n1 → S.C} (q : ContrPair c)

/-!

## Left contractions.

-/

/-- An equivalence needed to perform contraction. For specified `n` and `n1`
  this reduces to an identity. -/
def leftContrEquivSuccSucc : Fin (n.succ.succ + n1) ≃ Fin ((n + n1).succ.succ) :=
  (Fin.castOrderIso (by omega)).toEquiv

/-- An equivalence needed to perform contraction. For specified `n` and `n1`
  this reduces to an identity. -/
def leftContrEquivSucc : Fin (n.succ + n1) ≃ Fin ((n + n1).succ) :=
  (Fin.castOrderIso (by omega)).toEquiv

def leftContrI (n1 : ℕ): Fin ((n + n1).succ.succ) := leftContrEquivSuccSucc <| Fin.castAdd n1 q.i

def leftContrJ (n1 : ℕ) : Fin ((n + n1).succ) := leftContrEquivSucc <| Fin.castAdd n1 q.j

@[simp]
lemma leftContrJ_succAbove_leftContrI : (q.leftContrI n1).succAbove (q.leftContrJ n1)
      = leftContrEquivSuccSucc (Fin.castAdd n1  (q.i.succAbove q.j)) := by
  rw [leftContrI, leftContrJ]
  rw [Fin.ext_iff]
  simp only [Fin.succAbove, Nat.succ_eq_add_one, leftContrEquivSucc, RelIso.coe_fn_toEquiv,
    Fin.castOrderIso_apply, leftContrEquivSuccSucc, Fin.coe_cast, Fin.coe_castAdd]
  split_ifs
    <;> rename_i h1 h2
    <;> rw [Fin.lt_def] at h1 h2
  · simp only [Fin.coe_castSucc, Fin.coe_cast, Fin.coe_castAdd]
  · simp_all only [Fin.coe_castSucc, Fin.coe_cast, Fin.coe_castAdd, not_true_eq_false]
  · simp_all only [Fin.coe_castSucc, Fin.coe_cast, Fin.coe_castAdd, not_lt, Fin.val_succ,
    add_right_eq_self, one_ne_zero]
    omega
  · simp only [Fin.val_succ, Fin.coe_cast, Fin.coe_castAdd]

lemma succAbove_leftContrJ_leftContrI_castAdd (x : Fin n) :
    (q.leftContrI n1).succAbove ((q.leftContrJ n1).succAbove (Fin.castAdd n1 x)) =
    leftContrEquivSuccSucc (Fin.castAdd n1 (q.i.succAbove (q.j.succAbove x))) := by
  rw [Fin.ext_iff]
  simp [leftContrI, leftContrJ, leftContrEquivSuccSucc, Fin.succAbove]
  split_ifs <;> rename_i h1 h2 h3 h4
    <;> rw [Fin.lt_def] at h1 h2 h3 h4
    <;> simp_all [leftContrEquivSucc]
    <;> omega

lemma succAbove_leftContrJ_leftContrI_natAdd (x : Fin n1) :
    (q.leftContrI n1).succAbove ((q.leftContrJ n1).succAbove (Fin.natAdd n x)) =
    leftContrEquivSuccSucc (Fin.natAdd n.succ.succ x) := by
  rw [Fin.ext_iff]
  simp [leftContrI, leftContrJ, leftContrEquivSuccSucc, Fin.succAbove]
  split_ifs <;> rename_i h1 h2
    <;> rw [Fin.lt_def] at h1 h2
    <;> simp_all [leftContrEquivSucc]
    <;> omega


def leftContr : ContrPair ((Sum.elim c c1 ∘ (@finSumFinEquiv n.succ.succ n1).symm.toFun) ∘
    leftContrEquivSuccSucc.symm) where
  i := q.leftContrI n1
  j := q.leftContrJ n1
  h := by
    simp only [Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrJ_succAbove_leftContrI,
      Function.comp_apply, Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    simpa only [leftContrI, Nat.succ_eq_add_one, Equiv.symm_apply_apply,
      finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl] using q.h

lemma leftContr_map_eq : ((Sum.elim c (OverColor.mk c1).hom ∘ finSumFinEquiv.symm.toFun) ∘ ⇑leftContrEquivSuccSucc.symm) ∘
    (q.leftContr (c1 := c1)).i.succAbove ∘ (q.leftContr (c1 := c1)).j.succAbove =
    Sum.elim (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)).hom (OverColor.mk c1).hom ∘
    ⇑finSumFinEquiv.symm := by
  funext x
  simp only [Nat.succ_eq_add_one, Functor.id_obj, mk_hom, Equiv.toFun_as_coe, Function.comp_apply,
    Functor.const_obj_obj]
  obtain ⟨k, hk⟩ := finSumFinEquiv.surjective x
  subst hk
  match k with
  | Sum.inl k =>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl,
      Function.comp_apply]
    erw [succAbove_leftContrJ_leftContrI_castAdd]
    simp only [Nat.succ_eq_add_one, Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl]
  | Sum.inr k =>
    simp only [finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    erw [succAbove_leftContrJ_leftContrI_natAdd]
    simp only [Nat.succ_eq_add_one, Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inr]

lemma sum_inl_succAbove_leftContrI_leftContrJ (k : Fin n) : finSumFinEquiv.symm
  (leftContrEquivSuccSucc.symm
      ((q.leftContr (c1 := c1)).i.succAbove
        ((q.leftContr (c1 := c1)).j.succAbove
          (
            (finSumFinEquiv (Sum.inl k)))))) =
  Sum.map (q.i.succAbove ∘ q.j.succAbove) id (Sum.inl k) := by
  simp only [leftContr, Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrI,
    Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  erw [succAbove_leftContrJ_leftContrI_castAdd]
  simp

lemma sum_inr_succAbove_leftContrI_leftContrJ (k : Fin n1) :  finSumFinEquiv.symm
    (leftContrEquivSuccSucc.symm
      ((q.leftContr (c1 := c1)).i.succAbove
        ((q.leftContr (c1 := c1)).j.succAbove
          (
            (finSumFinEquiv (Sum.inr k)))))) =
  Sum.map (q.i.succAbove ∘ q.j.succAbove) id (Sum.inr k) := by
  simp only [leftContr, Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrI,
    Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  erw [succAbove_leftContrJ_leftContrI_natAdd]
  simp
lemma contrMap_prod_tprod (p : (i : (𝟭 Type).obj (OverColor.mk c).left) → CoeSort.coe (S.FDiscrete.obj { as := (OverColor.mk c).hom i }))
  (q' : (i : (𝟭 Type).obj (OverColor.mk c1).left) → CoeSort.coe (S.FDiscrete.obj { as := (OverColor.mk c1).hom i })):
  (S.F.map (equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)) (OverColor.mk c1)).hom
    ((q.contrMap.hom (PiTensorProduct.tprod S.k p)) ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) q'))
     = (S.F.map (mkIso (by exact leftContr_map_eq q)).hom).hom
    (q.leftContr.contrMap.hom
      ((S.F.map (equivToIso (@leftContrEquivSuccSucc n n1)).hom).hom
        ((S.F.map (equivToIso finSumFinEquiv).hom).hom
          ((S.F.μ (OverColor.mk c) (OverColor.mk c1)).hom
            ((PiTensorProduct.tprod S.k) p ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) q'))))) := by
  conv_lhs => rw [contrMap, TensorSpecies.contrMap_tprod]
  simp only [TensorSpecies.F_def]
  conv_rhs => rw [lift.obj_μ_tprod_tmul]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
  conv_lhs => rw [lift.obj_μ_tprod_tmul]
  change _ = ((lift.obj S.FDiscrete).map (mkIso _).hom).hom
    (q.leftContr.contrMap.hom
      (((lift.obj S.FDiscrete).map (equivToIso leftContrEquivSuccSucc).hom).hom
        (((lift.obj S.FDiscrete).map (equivToIso finSumFinEquiv).hom).hom
          ((PiTensorProduct.tprod S.k) _))))
  conv_rhs => rw [lift.map_tprod]
  change _ = ((lift.obj S.FDiscrete).map (mkIso _).hom).hom
    (q.leftContr.contrMap.hom
      (((lift.obj S.FDiscrete).map (equivToIso leftContrEquivSuccSucc).hom).hom
        (
          ((PiTensorProduct.tprod S.k) _))))
  conv_rhs => rw [lift.map_tprod]
  change _ = ((lift.obj S.FDiscrete).map (mkIso _).hom).hom
    (q.leftContr.contrMap.hom
      ((PiTensorProduct.tprod S.k) _))
  conv_rhs => rw [contrMap, TensorSpecies.contrMap_tprod]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
  have hL (a : Fin n.succ.succ) {b :  Fin (n + 1 + 1) ⊕ Fin n1}
          (h : b = Sum.inl a) :  p a = (S.FDiscrete.map (Discrete.eqToHom (by rw [h]; simp ))).hom
          ((lift.discreteSumEquiv S.FDiscrete b)
          (HepLean.PiTensorProduct.elimPureTensor p q' b)) := by
        subst h
        simp only [Nat.succ_eq_add_one, mk_hom, instMonoidalCategoryStruct_tensorObj_hom,
          Sum.elim_inl, eqToHom_refl, Discrete.functor_map_id, Action.id_hom, Functor.id_obj,
          ModuleCat.id_apply]
        rfl
  congr 1
  /- The contraction. -/
  · apply congrArg
    simp only [Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj,
      Discrete.functor_obj_eq_as, Function.comp_apply, Nat.succ_eq_add_one, mk_hom,
      Equiv.toFun_as_coe, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, Functor.id_obj,
      instMonoidalCategoryStruct_tensorObj_hom, LinearEquiv.ofLinear_apply]
    have h1' : ∀ {a a' b c b' c'} (haa' : a = a')
        (_ : b = (S.FDiscrete.map (Discrete.eqToHom (by rw [haa']))).hom b')
        (_ : c = (S.FDiscrete.map (Discrete.eqToHom (by rw [haa']))).hom c'),
        (S.contr.app a).hom (b ⊗ₜ[S.k] c) = (S.contr.app a').hom (b' ⊗ₜ[S.k] c') := by
      intro a a' b c b' c' haa' hbc hcc
      subst haa'
      simp_all
    refine h1' ?_ ?_ ?_
    · simp only [leftContr, Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrI,
      Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    · erw [ModuleCat.id_apply, ModuleCat.id_apply, ModuleCat.id_apply, ModuleCat.id_apply]
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, equivToIso_homToEquiv,
        LinearEquiv.coe_coe]
      apply hL
      exact Eq.symm ((fun f => (Equiv.apply_eq_iff_eq_symm_apply f).mp) finSumFinEquiv rfl)
    · simp only [Discrete.functor_obj_eq_as, Function.comp_apply, AddHom.toFun_eq_coe,
        LinearMap.coe_toAddHom, equivToIso_homToEquiv]
      change _ = (S.FDiscrete.map (Discrete.eqToHom _) ≫ S.FDiscrete.map (Discrete.eqToHom _)).hom _
      rw [← S.FDiscrete.map_comp]
      simp only [eqToHom_trans]
      /- a = q.i.succAbove q.j, d = q.i, b = (finSumFinEquiv.symm (leftContrEquivSuccSucc.symm (q.leftContr.i.succAbove q.leftContr.j))
        h : c (q.i.succAbove q.j) = S.τ (c q.i)  -/
      have h1 {a d : Fin n.succ.succ} {b :  Fin (n + 1 + 1) ⊕ Fin n1}
          (h1' : b = Sum.inl a) (h2' : c a = S.τ (c d)) :
          (S.FDiscrete.map (Discrete.eqToHom h2')).hom (p a) =
          (S.FDiscrete.map (eqToHom (by subst h1'; simpa using h2'))).hom
          ((lift.discreteSumEquiv S.FDiscrete b)
          (HepLean.PiTensorProduct.elimPureTensor p q' b)) := by
        subst h1'
        rfl
      apply h1
      erw [leftContrJ_succAbove_leftContrI]
      simp only [Nat.succ_eq_add_one, Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd]
  /- The tensor. -/
  · rw [lift.map_tprod]
    conv_lhs => erw [lift.map_tprod]
    apply congrArg
    funext k
    simp only [ Functor.id_obj, mk_hom, Function.comp_apply,
      equivToIso_homToEquiv, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, instMonoidalCategoryStruct_tensorObj_hom,
      LinearEquiv.ofLinear_apply, Equiv.toFun_as_coe, equivToIso_mkIso_hom, Equiv.refl_symm,
      Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv, eqToIso.inv]
    have h1 (l : (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)).left ⊕ (OverColor.mk c1).left)
      (l' : Fin n.succ.succ ⊕ Fin n1)
      (h : Sum.elim c c1 l' = Sum.elim (c ∘ q.i.succAbove ∘ q.j.succAbove) c1 l)
      (h' : l' = (Sum.map (q.i.succAbove ∘ q.j.succAbove) id l))
      : (lift.discreteSumEquiv S.FDiscrete l)
        (HepLean.PiTensorProduct.elimPureTensor (fun k => p (q.i.succAbove (q.j.succAbove k))) q' l) =
        (S.FDiscrete.map (eqToHom (by simp [h] ))).hom
        ((lift.discreteSumEquiv S.FDiscrete l')
        (HepLean.PiTensorProduct.elimPureTensor p q' l')) := by
      subst h'
      match l with
      | Sum.inl l =>
        simp only [ instMonoidalCategoryStruct_tensorObj_hom, mk_hom,
          Sum.elim_inl, Function.comp_apply, Functor.id_obj, Sum.map_inl, eqToHom_refl,
          Discrete.functor_map_id, Action.id_hom, ModuleCat.id_apply]
        rfl
      | Sum.inr l =>
        simp only [instMonoidalCategoryStruct_tensorObj_hom, mk_hom, Sum.elim_inr, Functor.id_obj,
          Function.comp_apply, Sum.map_inr, Discrete.functor_map_id, Action.id_hom]
        rfl
    refine h1 _ _ ?_ ?_
    · simpa using Discrete.eqToIso.proof_1
        (Hom.toEquiv_comp_inv_apply (mkIso (leftContr_map_eq q)).hom k)
    · obtain ⟨k, hk⟩ := finSumFinEquiv.surjective k
      subst hk
      erw [Equiv.symm_apply_apply]
      match k with
      | Sum.inl k => exact q.sum_inl_succAbove_leftContrI_leftContrJ _
      | Sum.inr k => exact q.sum_inr_succAbove_leftContrI_leftContrJ _

lemma contrMap_prod :
    (q.contrMap ▷ S.F.obj (OverColor.mk c1)) ≫ (S.F.μ _ ((OverColor.mk c1))) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom =
    (S.F.μ ((OverColor.mk c)) ((OverColor.mk c1))) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom ≫
    S.F.map (OverColor.equivToIso leftContrEquivSuccSucc).hom ≫ q.leftContr.contrMap
    ≫ S.F.map (OverColor.mkIso (q.leftContr_map_eq)).hom  := by
  ext1
  exact HepLean.PiTensorProduct.induction_tmul (fun p q' => q.contrMap_prod_tprod p q')

lemma contr_prod
    (t : TensorTree S c) (t1 : TensorTree S c1) :
    (prod (contr q.i q.j q.h t) t1).tensor =  ((perm (OverColor.mkIso q.leftContr_map_eq).hom
    (contr (q.leftContrI n1) (q.leftContrJ n1)
    q.leftContr.h (
      perm (OverColor.equivToIso ContrPair.leftContrEquivSuccSucc).hom (prod t t1)
    ))).tensor) := by
  simp only [contr_tensor, perm_tensor, prod_tensor]
  change  ((q.contrMap ▷ S.F.obj (OverColor.mk c1)) ≫ (S.F.μ _ ((OverColor.mk c1))) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom (t.tensor ⊗ₜ[S.k] t1.tensor) = _
  rw [contrMap_prod]
  simp only [Nat.succ_eq_add_one, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Functor.const_obj_obj, Equiv.toFun_as_coe, Action.comp_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.coe_comp, Function.comp_apply]
  apply congrArg
  apply congrArg
  rfl

/-!

## Right contractions.

-/

def rightContrI (n1 : ℕ): Fin ((n1 + n).succ.succ) := Fin.natAdd n1 q.i

def rightContrJ (n1 : ℕ) : Fin ((n1 + n).succ) := Fin.natAdd n1 q.j

@[simp]
lemma rightContrJ_succAbove_rightContrI : (q.rightContrI n1).succAbove (q.rightContrJ n1)
      = (Fin.natAdd n1  (q.i.succAbove q.j)) := by
  rw [rightContrI, rightContrJ]
  rw [Fin.ext_iff]
  simp only [Fin.succAbove, Nat.succ_eq_add_one, Fin.coe_natAdd]
  split_ifs
    <;> rename_i h1 h2
    <;> rw [Fin.lt_def] at h1 h2
  · simp only [Fin.coe_castSucc, Fin.coe_natAdd]
  · simp_all only [Fin.coe_castSucc, Fin.coe_natAdd, add_lt_add_iff_left, not_true_eq_false]
  · simp_all only [Fin.coe_castSucc, Fin.coe_natAdd, add_lt_add_iff_left, not_lt, Fin.val_succ,
    add_right_eq_self, one_ne_zero]
    omega
  · simp only [Fin.val_succ, Fin.coe_natAdd]
    omega

lemma succAbove_rightContrJ_rightContrI_castAdd (x : Fin n1) :
    (q.rightContrI n1).succAbove ((q.rightContrJ n1).succAbove (Fin.castAdd n x)) =
    (Fin.castAdd n.succ.succ x) := by
  rw [Fin.ext_iff]
  simp [rightContrI, rightContrJ, Fin.succAbove]
  split_ifs <;> rename_i h1 h2
    <;> rw [Fin.lt_def] at h1 h2
    <;> simp_all
    <;> omega

lemma succAbove_rightContrJ_rightContrI_natAdd (x : Fin n) :
    (q.rightContrI n1).succAbove ((q.rightContrJ n1).succAbove (Fin.natAdd n1 x)) =
    (Fin.natAdd n1 ((q.i.succAbove) (q.j.succAbove x))) := by
  rw [Fin.ext_iff]
  simp [rightContrI, rightContrJ, Fin.succAbove]
  split_ifs <;> rename_i h1 h2 h3 h4
    <;> rw [Fin.lt_def] at h1 h2 h3 h4
    <;> simp_all
    <;> omega

def rightContr : ContrPair ((Sum.elim c1 c ∘ (@finSumFinEquiv n1 n.succ.succ).symm.toFun)) where
  i := q.rightContrI n1
  j := q.rightContrJ n1
  h := by
    simp only [Nat.add_eq, Nat.succ_eq_add_one, Equiv.toFun_as_coe,
      rightContrJ_succAbove_rightContrI, Function.comp_apply, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inr]
    simpa [rightContrI] using q.h

lemma rightContr_map_eq : ((Sum.elim c1 (OverColor.mk c).hom ∘ finSumFinEquiv.symm.toFun)) ∘
    (q.rightContr (c1 := c1)).i.succAbove ∘ (q.rightContr (c1 := c1)).j.succAbove =
    Sum.elim (OverColor.mk c1).hom (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)).hom ∘
    ⇑finSumFinEquiv.symm := by
  funext x
  simp only [Nat.succ_eq_add_one, Functor.id_obj, mk_hom, Equiv.toFun_as_coe, Function.comp_apply,
    Functor.const_obj_obj]
  obtain ⟨k, hk⟩ := finSumFinEquiv.surjective x
  subst hk
  match k with
  | Sum.inl k =>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    erw [succAbove_rightContrJ_rightContrI_castAdd]
    simp only [Nat.succ_eq_add_one, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  | Sum.inr k =>
    simp only [finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    erw [succAbove_rightContrJ_rightContrI_natAdd]
    simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Function.comp_apply]


lemma sum_inl_succAbove_rightContrI_rightContrJ (k : Fin n1): (@finSumFinEquiv n1 n.succ.succ).symm
    ((q.rightContr (c1 := c1)).i.succAbove
      ((q.rightContr (c1 := c1)).j.succAbove
        (((@finSumFinEquiv n1 n) (Sum.inl k))))) =
    Sum.map id (q.i.succAbove ∘ q.j.succAbove) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl k))) := by
  simp only [leftContr, Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrI,
    Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  erw [succAbove_rightContrJ_rightContrI_castAdd]
  simp

lemma sum_inr_succAbove_rightContrI_rightContrJ (k : Fin n): (@finSumFinEquiv n1 n.succ.succ).symm
    ((q.rightContr (c1 := c1)).i.succAbove
      ((q.rightContr (c1 := c1)).j.succAbove
        (
          (finSumFinEquiv (Sum.inr k))))) =
  Sum.map id (q.i.succAbove ∘ q.j.succAbove) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr k))):= by
  simp only [leftContr, Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrI,
    Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  erw [succAbove_rightContrJ_rightContrI_natAdd]
  simp


lemma prod_contrMap_tprod (p : (i : (𝟭 Type).obj (OverColor.mk c1).left) → CoeSort.coe (S.FDiscrete.obj { as := (OverColor.mk c1).hom i }))
  (q' : (i : (𝟭 Type).obj (OverColor.mk c).left) → CoeSort.coe (S.FDiscrete.obj { as := (OverColor.mk c).hom i })):
     (S.F.map (equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ (OverColor.mk c1) (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove))).hom
    ((PiTensorProduct.tprod S.k) p ⊗ₜ[S.k] (q.contrMap.hom (PiTensorProduct.tprod S.k q')))) =
    (S.F.map (mkIso (by exact (rightContr_map_eq q))).hom).hom
    (q.rightContr.contrMap.hom
    (((S.F.map (equivToIso finSumFinEquiv).hom ).hom
    ((S.F.μ (OverColor.mk c1) (OverColor.mk c)).hom ((PiTensorProduct.tprod S.k) p ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) q'))))) := by
  conv_lhs => rw [contrMap, TensorSpecies.contrMap_tprod]
  simp only [TensorSpecies.F_def]
  conv_rhs => rw [lift.obj_μ_tprod_tmul]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
  conv_lhs => rw [lift.obj_μ_tprod_tmul]
  conv_rhs => erw [lift.map_tprod]
  conv_rhs => erw [contrMap, TensorSpecies.contrMap_tprod]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
  congr 1
  /- The contraction. -/
  · apply congrArg
    simp only [Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj,
      Discrete.functor_obj_eq_as, Function.comp_apply, Nat.succ_eq_add_one, mk_hom,
      Equiv.toFun_as_coe, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, Functor.id_obj,
      instMonoidalCategoryStruct_tensorObj_hom, LinearEquiv.ofLinear_apply]
    have h1' : ∀ {a a' b c b' c'} (haa' : a = a')
        (_ : b = (S.FDiscrete.map (Discrete.eqToHom (by rw [haa']))).hom b')
        (_ : c = (S.FDiscrete.map (Discrete.eqToHom (by rw [haa']))).hom c'),
        (S.contr.app a).hom (b ⊗ₜ[S.k] c) = (S.contr.app a').hom (b' ⊗ₜ[S.k] c') := by
      intro a a' b c b' c' haa' hbc hcc
      subst haa'
      simp_all
    refine h1' ?_ ?_ ?_
    · simp only [Nat.add_eq, rightContr, Nat.succ_eq_add_one, Equiv.toFun_as_coe, rightContrI,
      finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    · erw [ModuleCat.id_apply, ModuleCat.id_apply, ModuleCat.id_apply]
      simp
      have hL (a : Fin n.succ.succ) {b :  Fin n1 ⊕ Fin n.succ.succ}
          (h : b = Sum.inr a) :  q' a = (S.FDiscrete.map (Discrete.eqToHom (by rw [h]; simp ))).hom
          ((lift.discreteSumEquiv S.FDiscrete b)
          (HepLean.PiTensorProduct.elimPureTensor p q' b)) := by
        subst h
        simp only [Nat.succ_eq_add_one, mk_hom, instMonoidalCategoryStruct_tensorObj_hom,
          Sum.elim_inl, eqToHom_refl, Discrete.functor_map_id, Action.id_hom, Functor.id_obj,
          ModuleCat.id_apply]
        rfl
      apply hL
      simp [rightContr, rightContrI]
    · erw [ModuleCat.id_apply, ModuleCat.id_apply, ModuleCat.id_apply, ModuleCat.id_apply, ModuleCat.id_apply]
      simp only [Discrete.functor_obj_eq_as, Function.comp_apply, AddHom.toFun_eq_coe,
        LinearMap.coe_toAddHom, equivToIso_homToEquiv]
      change _ = (S.FDiscrete.map (Discrete.eqToHom _) ≫ S.FDiscrete.map (Discrete.eqToHom _)).hom _
      rw [← S.FDiscrete.map_comp]
      simp
      have h1 {a d : Fin n.succ.succ} {b :  Fin n1 ⊕ Fin (n + 1 + 1) }
          (h1' : b = Sum.inr a) (h2' : c a = S.τ (c d)) :
          (S.FDiscrete.map (Discrete.eqToHom h2')).hom (q' a) =
          (S.FDiscrete.map (eqToHom (by subst h1'; simpa using h2'))).hom
          ((lift.discreteSumEquiv S.FDiscrete b)
          (HepLean.PiTensorProduct.elimPureTensor p q' b)) := by
        subst h1'
        rfl
      apply h1
      erw [rightContrJ_succAbove_rightContrI]
      simp only [finSumFinEquiv_symm_apply_natAdd, Nat.succ_eq_add_one]
  /- The tensor. -/
  · rw [lift.map_tprod]
    conv_lhs => erw [lift.map_tprod]
    apply congrArg
    funext k
    simp only [ Functor.id_obj, mk_hom, Function.comp_apply,
      equivToIso_homToEquiv, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, instMonoidalCategoryStruct_tensorObj_hom,
      LinearEquiv.ofLinear_apply, Equiv.toFun_as_coe, equivToIso_mkIso_hom, Equiv.refl_symm,
      Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv, eqToIso.inv]
    conv_rhs => repeat erw [ModuleCat.id_apply]
    simp  [Nat.succ_eq_add_one, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearEquiv.coe_coe]
    have h1 (l : (OverColor.mk c1).left ⊕  (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)).left)
      (l' :Fin n1 ⊕ Fin n.succ.succ )
      (h : Sum.elim c1 c l' = Sum.elim c1 (c ∘ q.i.succAbove ∘ q.j.succAbove) l)
      (h' : l' = (Sum.map id (q.i.succAbove ∘ q.j.succAbove) l))
      : (lift.discreteSumEquiv S.FDiscrete l)
        (HepLean.PiTensorProduct.elimPureTensor p (fun k => q' (q.i.succAbove (q.j.succAbove k)))  l) =
        (S.FDiscrete.map (eqToHom (by simp [h] ))).hom
        ((lift.discreteSumEquiv S.FDiscrete l')
        (HepLean.PiTensorProduct.elimPureTensor p q' l')) := by
      subst h'
      match l with
      | Sum.inl l =>
        simp only [Nat.succ_eq_add_one, instMonoidalCategoryStruct_tensorObj_hom, mk_hom,
          Sum.elim_inl, Function.comp_apply, Functor.id_obj, Sum.map_inl, eqToHom_refl,
          Discrete.functor_map_id, Action.id_hom, ModuleCat.id_apply]
        rfl
      | Sum.inr l =>
        simp only [Nat.succ_eq_add_one, instMonoidalCategoryStruct_tensorObj_hom, mk_hom,
          Sum.elim_inr, Functor.id_obj, Function.comp_apply, Sum.map_inr, id_eq, eqToHom_refl,
          Discrete.functor_map_id, Action.id_hom, ModuleCat.id_apply]
        rfl
    refine h1 _ _ ?_ ?_
    · simpa using Discrete.eqToIso.proof_1
        (Hom.toEquiv_comp_inv_apply (mkIso (rightContr_map_eq q)).hom k)
    · obtain ⟨k, hk⟩ := finSumFinEquiv.surjective k
      subst hk
      match k with
      | Sum.inl k => exact sum_inl_succAbove_rightContrI_rightContrJ _ _
      | Sum.inr k => exact sum_inr_succAbove_rightContrI_rightContrJ _ _

lemma prod_contrMap :
    (S.F.obj (OverColor.mk c1) ◁ q.contrMap) ≫ (S.F.μ ((OverColor.mk c1)) _) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom =
    (S.F.μ ((OverColor.mk c1)) ((OverColor.mk c))) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom ≫
     q.rightContr.contrMap ≫  S.F.map (OverColor.mkIso (q.rightContr_map_eq)).hom := by
  ext1
  exact HepLean.PiTensorProduct.induction_tmul (fun p q' => q.prod_contrMap_tprod p q')

lemma prod_contr (t1 : TensorTree S c1) (t : TensorTree S c) :
   (prod t1 (contr q.i q.j q.h t)).tensor =  ((perm (OverColor.mkIso q.rightContr_map_eq).hom
    (contr (q.rightContrI n1) (q.rightContrJ n1)
    q.rightContr.h (
       (prod t1 t)
    ))).tensor) := by
  simp only [contr_tensor, perm_tensor, prod_tensor]
  change  ( (S.F.obj (OverColor.mk c1) ◁ q.contrMap) ≫ (S.F.μ ((OverColor.mk c1)) _) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom (t1.tensor ⊗ₜ[S.k] t.tensor) = _
  rw [prod_contrMap]
  simp only [Nat.succ_eq_add_one, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Functor.const_obj_obj, Equiv.toFun_as_coe, Action.comp_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.coe_comp, Function.comp_apply]
  apply congrArg
  apply congrArg
  rfl

end ContrPair

theorem contr_prod {n n1 : ℕ} {c : Fin n.succ.succ → S.C} {c1  : Fin n1 → S.C} {i : Fin n.succ.succ}
    {j : Fin n.succ} (hij : c (i.succAbove j) = S.τ (c i))
    (t : TensorTree S c) (t1 : TensorTree S c1) :
    (prod (contr i j hij t) t1).tensor =  ((perm (OverColor.mkIso (ContrPair.mk i j hij).leftContr_map_eq).hom
    (contr ((ContrPair.mk i j hij).leftContrI n1) ((ContrPair.mk i j hij).leftContrJ n1)
    (ContrPair.mk i j hij).leftContr.h (
      perm (OverColor.equivToIso ContrPair.leftContrEquivSuccSucc).hom (prod t t1)
    ))).tensor) :=
  (ContrPair.mk i j hij).contr_prod t t1

theorem prod_contr {n n1 : ℕ} {c : Fin n.succ.succ → S.C} {c1  : Fin n1 → S.C} {i : Fin n.succ.succ}
    {j : Fin n.succ} (hij : c (i.succAbove j) = S.τ (c i))
    (t1 : TensorTree S c1) (t : TensorTree S c) :
   (prod t1 (contr i j hij t)).tensor =  ((perm (OverColor.mkIso (ContrPair.mk i j hij).rightContr_map_eq).hom
    (contr ((ContrPair.mk i j hij).rightContrI n1) ((ContrPair.mk i j hij).rightContrJ n1)
    (ContrPair.mk i j hij).rightContr.h (
       (prod t1 t)
    ))).tensor) :=
  (ContrPair.mk i j hij).prod_contr t1 t

end TensorTree
