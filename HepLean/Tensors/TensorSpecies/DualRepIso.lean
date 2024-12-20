/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.MetricTensor
import HepLean.Tensors.Tree.NodeIdentities.Assoc
/-!

# Isomorphism between rep of color `c` and rep of dual color.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

noncomputable section

namespace TensorSpecies
open TensorTree
variable (S : TensorSpecies)

/-- The morphism from `S.FD.obj (Discrete.mk c)` to `S.FD.obj (Discrete.mk (S.τ c))`
  defined by contracting with the metric. -/
def toDualRep (c : S.C) : S.FD.obj (Discrete.mk c) ⟶ S.FD.obj (Discrete.mk (S.τ c)) :=
  (ρ_ (S.FD.obj (Discrete.mk c))).inv
  ≫ (S.FD.obj { as := c } ◁ (S.metric.app (Discrete.mk (S.τ c))))
  ≫ (α_ (S.FD.obj (Discrete.mk c)) (S.FD.obj (Discrete.mk (S.τ c)))
    (S.FD.obj (Discrete.mk (S.τ c)))).inv
  ≫ (S.contr.app (Discrete.mk c) ▷ S.FD.obj { as := S.τ c })
  ≫ (λ_ (S.FD.obj (Discrete.mk (S.τ c)))).hom

/-- The `toDualRep` for equal colors is the same, up-to conjugation by a trivial equivalence. -/
lemma toDualRep_congr {c c' : S.C} (h : c = c') : S.toDualRep c = S.FD.map (Discrete.eqToHom h) ≫
    S.toDualRep c' ≫ S.FD.map (Discrete.eqToHom (congrArg S.τ h.symm)) := by
  subst h
  simp only [eqToHom_refl, Discrete.functor_map_id, Category.comp_id, Category.id_comp]

/-- The morphism from `S.FD.obj (Discrete.mk (S.τ c))` to `S.FD.obj (Discrete.mk c)`
  defined by contracting with the metric. -/
def fromDualRep (c : S.C) : S.FD.obj (Discrete.mk (S.τ c)) ⟶ S.FD.obj (Discrete.mk c) :=
  S.toDualRep (S.τ c) ≫ S.FD.map (Discrete.eqToHom (S.τ_involution c))

/-- The rewriting of `toDualRep` in terms of `contrOneTwoLeft`. -/
lemma toDualRep_apply_eq_contrOneTwoLeft (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    (S.toDualRep c).hom x = (S.tensorToVec (S.τ c)).hom.hom
    (contrOneTwoLeft (((S.tensorToVec c).inv.hom x))
    (S.metricTensor (S.τ c))) := by
  simp only [toDualRep, Monoidal.tensorUnit_obj, Action.comp_hom,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_rightUnitor_inv_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    Action.instMonoidalCategory_associator_inv_hom, Action.instMonoidalCategory_whiskerRight_hom,
    Action.instMonoidalCategory_leftUnitor_hom_hom, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    Nat.succ_eq_add_one, Nat.reduceAdd, contrOneTwoLeft, Functor.comp_obj,
    Discrete.functor_obj_eq_as, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, OverColor.Discrete.rep_iso_hom_inv_apply]
  repeat apply congrArg
  erw [pairIsoSep_inv_metricTensor]
  rfl

/-- Expansion of `toDualRep` is
  `(S.tensorToVec c).inv.hom x | μ ⊗ S.metricTensor (S.τ c) | μ ν`. -/
lemma toDualRep_tensorTree (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    let y : S.F.obj (OverColor.mk ![c]) := (S.tensorToVec c).inv.hom x
    (S.toDualRep c).hom x = (S.tensorToVec (S.τ c)).hom.hom
    ({y | μ ⊗ S.metricTensor (S.τ c) | μ ν}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl _) (fun x => by fin_cases x; rfl))).tensor := by
  simp only
  rw [toDualRep_apply_eq_contrOneTwoLeft]
  apply congrArg
  exact contrOneTwoLeft_tensorTree ((S.tensorToVec c).inv.hom x) (S.metricTensor (S.τ c))

lemma fromDualRep_tensorTree (c : S.C) (x : S.FD.obj (Discrete.mk (S.τ c))) :
    let y : S.F.obj (OverColor.mk ![S.τ c]) := (S.tensorToVec (S.τ c)).inv.hom x
    (S.fromDualRep c).hom x = (S.tensorToVec c).hom.hom
    ({y | μ ⊗ S.metricTensor (S.τ (S.τ c))| μ ν}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl _)
      (fun x => by fin_cases x; exact (S.τ_involution c).symm))).tensor := by
  simp only
  rw [fromDualRep]
  simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero]
  rw [toDualRep_tensorTree]
  rw [tensorToVec_naturality_eqToHom_apply]
  apply congrArg
  conv_lhs =>
    rw [← perm_tensor]
    rw [perm_perm]
  exact perm_congr rfl rfl

/-- Applying `toDualRep` followed by `fromDualRep` is equivalent to contracting
  with two metric tensors on the right. -/
lemma toDualRep_fromDualRep_tensorTree_metrics (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    let y : S.F.obj (OverColor.mk ![c]) := (S.tensorToVec c).inv.hom x
    (S.fromDualRep c).hom ((S.toDualRep c).hom x) = (S.tensorToVec c).hom.hom
    ({y | μ ⊗ S.metricTensor (S.τ c) | μ ν ⊗ S.metricTensor (S.τ (S.τ c)) | ν σ}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl _)
      (fun x => by fin_cases x; exact (S.τ_involution c).symm))).tensor := by
  rw [toDualRep_tensorTree, fromDualRep_tensorTree]
  simp only
  apply congrArg
  rw [OverColor.Discrete.rep_iso_inv_hom_apply]
  conv_lhs =>
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_fst <| tensorNode_of_tree _]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_left _ _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 0 0 (by simp) (by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero,
        OverColor.mk_left, Functor.id_obj, OverColor.mk_hom, Equiv.refl_symm, Equiv.coe_refl,
        Function.comp_apply, id_eq, Fin.zero_eta, List.pmap.eq_1, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, OverColor.extractOne_homToEquiv,
        permProdLeft_toEquiv, OverColor.equivToHomEq_toEquiv, Equiv.sumCongr_refl, Equiv.refl_trans,
        Equiv.symm_trans_self, Equiv.refl_apply, HepLean.Fin.finExtractOnePerm_symm_apply,
        HepLean.Fin.finExtractOne_symm_inr_apply, Fin.zero_succAbove]
      decide)]
    rw [perm_perm]
  apply perm_congr _ rfl
  apply OverColor.Hom.fin_ext
  intro i
  fin_cases i
  simp only [OverColor.mk_left, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero,
    Functor.id_obj, OverColor.mk_hom, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq,
    Fin.zero_eta, List.pmap.eq_1, Matrix.cons_val_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    OverColor.extractOne_homToEquiv, HepLean.Fin.finExtractOnePerm_symm_apply, Category.assoc,
    OverColor.Hom.hom_comp, Over.comp_left, OverColor.equivToHomEq_hom_left, Equiv.toFun_as_coe,
    types_comp_apply, OverColor.mkIso_hom_hom_left_apply, OverColor.extractTwo_hom_left_apply,
    permProdLeft_toEquiv, OverColor.equivToHomEq_toEquiv, Equiv.sumCongr_refl, Equiv.refl_trans,
    Equiv.symm_trans_self, Equiv.refl_apply, HepLean.Fin.finExtractOne_symm_inr_apply,
    Fin.zero_succAbove, HepLean.Fin.finExtractOnePerm_apply]
  decide

/-- Applying `toDualRep` followed by `fromDualRep` is equivalent to contracting
  with a unit tensors on the right. -/
lemma toDualRep_fromDualRep_tensorTree_unitTensor (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    let y : S.F.obj (OverColor.mk ![c]) := (S.tensorToVec c).inv.hom x
    (S.fromDualRep c).hom ((S.toDualRep c).hom x) = (S.tensorToVec c).hom.hom
    ({y | μ ⊗ S.unitTensor c | μ ν}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl _)
      (fun x => by fin_cases x; rfl))).tensor := by
  rw [toDualRep_fromDualRep_tensorTree_metrics]
  apply congrArg
  conv_lhs =>
    rw [perm_tensor_eq <| assoc_one_two_two _ _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <|
      metricTensor_contr_dual_metricTensor_eq_unit _]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_right _ _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 0 1 (by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, OverColor.mk_left, Functor.id_obj,
        OverColor.mk_hom, permProdRight_toEquiv, OverColor.equivToHomEq_toEquiv,
        Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm,
        Equiv.sumCongr_apply, Equiv.coe_refl]
      rfl) (by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero,
        OverColor.mk_left, Functor.id_obj, OverColor.mk_hom, OverColor.extractOne_homToEquiv,
        permProdRight_toEquiv, OverColor.equivToHomEq_toEquiv, Equiv.symm_trans_apply,
        Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl,
        HepLean.Fin.finExtractOnePerm_symm_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
        Sum.map_map, CompTriple.comp_eq, Equiv.self_comp_symm, Sum.map_id_id, id_eq,
        Equiv.apply_symm_apply, HepLean.Fin.finExtractOne_symm_inr_apply, Fin.zero_succAbove,
        Fin.succ_zero_eq_one]
      rfl)]
    rw [perm_perm]
  conv_rhs =>
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| unitTensor_eq_dual_perm _]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_right _ _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 0 1 (by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, OverColor.mk_left, Functor.id_obj,
        OverColor.mk_hom, permProdRight_toEquiv, OverColor.equivToHomEq_toEquiv,
        Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm,
        Equiv.sumCongr_apply, Equiv.coe_refl]
      rfl) (by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero,
        OverColor.mk_left, Functor.id_obj, OverColor.mk_hom, Function.comp_apply,
        HepLean.Fin.finMapToEquiv_symm_apply, Matrix.cons_val_zero, OverColor.extractOne_homToEquiv,
        permProdRight_toEquiv, OverColor.equivToHomEq_toEquiv, Equiv.symm_trans_apply,
        Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl,
        HepLean.Fin.finExtractOnePerm_symm_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
        Sum.map_map, CompTriple.comp_eq, Equiv.self_comp_symm, Sum.map_id_id, id_eq,
        Equiv.apply_symm_apply, HepLean.Fin.finExtractOne_symm_inr_apply, Fin.zero_succAbove,
        Fin.succ_zero_eq_one]
      rfl)]
    rw [perm_perm]
  refine perm_congr (OverColor.Hom.fin_ext _ _ fun i => ?_) rfl
  fin_cases i
  simp only [OverColor.mk_left, Nat.succ_eq_add_one, Nat.reduceAdd, Functor.id_obj,
    OverColor.mk_hom, Fin.isValue, Fin.succAbove_zero, OverColor.extractOne_homToEquiv,
    HepLean.Fin.finExtractOnePerm_symm_apply, Category.assoc, OverColor.Hom.hom_comp, Fin.zero_eta,
    Over.comp_left, OverColor.equivToHomEq_hom_left, Equiv.toFun_as_coe, Equiv.coe_refl,
    types_comp_apply, OverColor.mkIso_hom_hom_left_apply, OverColor.extractTwo_hom_left_apply,
    permProdRight_toEquiv, OverColor.equivToHomEq_toEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply, Sum.map_map, CompTriple.comp_eq, Equiv.self_comp_symm, Sum.map_id_id,
    id_eq, Equiv.apply_symm_apply, HepLean.Fin.finExtractOne_symm_inr_apply, Fin.zero_succAbove,
    Fin.succ_zero_eq_one, HepLean.Fin.finExtractOnePerm_apply, Function.comp_apply,
    HepLean.Fin.finMapToEquiv_symm_apply, Matrix.cons_val_zero]

lemma toDualRep_fromDualRep_tensorTree (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    let y : S.F.obj (OverColor.mk ![c]) := (S.tensorToVec c).inv.hom x
    (S.fromDualRep c).hom ((S.toDualRep c).hom x) = (S.tensorToVec c).hom.hom
    ({y | μ}ᵀ).tensor := by
  rw [toDualRep_fromDualRep_tensorTree_unitTensor]
  apply congrArg
  conv_lhs =>
    rw [perm_tensor_eq <| vec_contr_unitTensor_eq_self _]
    rw [perm_perm]
    rw [perm_eq_id]

lemma toDualRep_fromDualRep_eq_self (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    (S.fromDualRep c).hom ((S.toDualRep c).hom x) = x := by
  rw [toDualRep_fromDualRep_tensorTree]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, tensorNode_tensor,
    OverColor.Discrete.rep_iso_hom_inv_apply]

lemma fromDualRep_toDualRep_eq_self (c : S.C) (x : S.FD.obj (Discrete.mk (S.τ c))) :
    (S.toDualRep c).hom ((S.fromDualRep c).hom x) = x := by
  rw [S.toDualRep_congr (S.τ_involution c).symm, fromDualRep]
  simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply]
  change (S.FD.map (Discrete.eqToHom _)).hom ((S.toDualRep (S.τ (S.τ c))).hom
    (((S.FD.map (Discrete.eqToHom _)) ≫ S.FD.map (Discrete.eqToHom _)).hom
    (((S.toDualRep (S.τ c)).hom x)))) = _
  rw [← S.FD.map_comp]
  simp only [eqToHom_trans, eqToHom_refl, Discrete.functor_map_id, Action.id_hom,
    ModuleCat.id_apply]
  conv_rhs => rw [← S.toDualRep_fromDualRep_eq_self (S.τ c) x]
  rfl

/-- The isomorphism between the representation associated with a color, and that associated with
  its dual. -/
def dualRepIsoDiscrete (c : S.C) : S.FD.obj (Discrete.mk c) ≅ S.FD.obj (Discrete.mk (S.τ c)) where
  hom := S.toDualRep c
  inv := S.fromDualRep c
  hom_inv_id := by
    ext x
    exact S.toDualRep_fromDualRep_eq_self c x
  inv_hom_id := by
    ext x
    exact S.fromDualRep_toDualRep_eq_self c x

informal_definition dualRepIso where
  math :≈ "Given a `i : Fin n` the isomorphism between `S.F.obj (OverColor.mk c)` and
    `S.F.obj (OverColor.mk (Function.update c i (S.τ (c i))))` induced by `dualRepIsoDiscrete`
    acting on the `i`-th component of the color."
  deps :≈ [``dualRepIsoDiscrete]

informal_lemma dualRepIso_unitTensor_fst where
  math :≈ "Acting with `dualRepIso` on the fst component of a `unitTensor` returns a metric."
  deps :≈ [``dualRepIso, ``unitTensor, ``metricTensor]

informal_lemma dualRepIso_unitTensor_snd where
  math :≈ "Acting with `dualRepIso` on the snd component of a `unitTensor` returns a metric."
  deps :≈ [``dualRepIso, ``unitTensor, ``metricTensor]

informal_lemma dualRepIso_metricTensor_fst where
  math :≈ "Acting with `dualRepIso` on the fst component of a `metricTensor` returns a unitTensor."
  deps :≈ [``dualRepIso, ``unitTensor, ``metricTensor]

informal_lemma dualRepIso_metricTensor_snd where
  math :≈ "Acting with `dualRepIso` on the snd component of a `metricTensor` returns a unitTensor."
  deps :≈ [``dualRepIso, ``unitTensor, ``metricTensor]

end TensorSpecies

end
