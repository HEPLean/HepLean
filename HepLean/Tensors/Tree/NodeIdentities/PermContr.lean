/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.NodeIdentities.Congr
import HepLean.Tensors.Tree.NodeIdentities.Basic
/-!

# The commutativity of Permutations and contractions.

There is very likely a better way to do this using `TensorSpecies.contrMap_tprod`.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorSpecies
noncomputable section

variable (S : TensorSpecies)

lemma contrFin1Fin1_naturality {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} (h : c1 (i.succAbove j) = S.τ (c1 i))
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map (extractTwoAux' i j σ)).hom ≫ (S.contrFin1Fin1 c1 i j h).hom.hom
    = (S.contrFin1Fin1 c ((Hom.toEquiv σ).symm i)
      ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
      (perm_contr_cond S h σ)).hom.hom
    ≫ ((Discrete.pairτ S.FD S.τ).map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i) :
      (Discrete.mk (c ((Hom.toEquiv σ).symm i))) ⟶ (Discrete.mk (c1 i)))).hom := by
  have h1 : (S.F.map (extractTwoAux' i j σ)) ≫ (S.contrFin1Fin1 c1 i j h).hom
    = (S.contrFin1Fin1 c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
    (perm_contr_cond S h σ)).hom
    ≫ ((Discrete.pairτ S.FD S.τ).map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i) :
    (Discrete.mk (c ((Hom.toEquiv σ).symm i))) ⟶ (Discrete.mk (c1 i)))) := by
    rw [← CategoryTheory.Iso.eq_comp_inv]
    rw [CategoryTheory.Category.assoc]
    rw [← CategoryTheory.Iso.inv_comp_eq]
    ext1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    simp only [Nat.succ_eq_add_one, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, CategoryStruct.comp,
      extractOne_homToEquiv, Action.Hom.comp_hom, LinearMap.coe_comp]
    trans (S.F.map (extractTwoAux' i j σ)).hom (PiTensorProduct.tprod S.k (fun k =>
      match k with | Sum.inl 0 => x | Sum.inr 0 => (S.FD.map
      (eqToHom (by
        simp only [Nat.succ_eq_add_one, Discrete.functor_obj_eq_as, Function.comp_apply,
          extractOne_homToEquiv, Fin.isValue, mk_hom, finExtractTwo_symm_inl_inr_apply,
          Discrete.mk.injEq]
        erw [perm_contr_cond S h σ]))).hom y))
    · rw [ModuleCat.Hom.hom, ConcreteCategory.hom]
      simp only [ModuleCat.instConcreteCategoryLinearMapIdCarrier, LinearMap.coe_comp,
        Function.comp_apply]
      apply congrArg
      have h1' {α :Type} {a b c d : α} (hab : a= b) (hcd : c = d) (h : a = d) : b = c := by
          rw [← hab, hcd]
          exact h
      have h1 := S.contrFin1Fin1_inv_tmul c ((Hom.toEquiv σ).symm i)
          ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
          (perm_contr_cond S h σ) x y
      refine h1' ?_ ?_ h1
      congr
      apply congrArg
      funext x
      match x with
      | Sum.inl 0 => rfl
      | Sum.inr 0 => rfl
    change _ = (S.contrFin1Fin1 c1 i j h).inv.hom
      ((S.FD.map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i))).hom x ⊗ₜ[S.k]
      (S.FD.map (Discrete.eqToHom (congrArg S.τ (Hom.toEquiv_comp_inv_apply σ i)))).hom y)
    rw [contrFin1Fin1_inv_tmul]
    change ((lift.obj S.FD).map (extractTwoAux' i j σ)).hom _ = _
    rw [lift.map_tprod]
    apply congrArg
    funext i
    match i with
    | Sum.inl 0 => rfl
    | Sum.inr 0 =>
      simp only [Nat.succ_eq_add_one, mk_hom, Fin.isValue, Function.comp_apply,
        extractOne_homToEquiv, lift.discreteFunctorMapEqIso, Functor.mapIso_hom, eqToIso.hom,
        Functor.mapIso_inv, eqToIso.inv, Functor.id_obj, Discrete.functor_obj_eq_as,
        LinearEquiv.ofLinear_apply]
      change ((S.FD.map (eqToHom _)) ≫ S.FD.map (eqToHom _)).hom y =
        ((S.FD.map (eqToHom _)) ≫ S.FD.map (eqToHom _)).hom y
      rw [← Functor.map_comp, ← Functor.map_comp]
      simp only [Fin.isValue, Nat.succ_eq_add_one, Discrete.functor_obj_eq_as, Function.comp_apply,
        eqToHom_trans]
  exact congrArg (λ f => Action.Hom.hom f) h1

lemma contrIso_comm_aux_1 {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    ((S.F.map σ).hom ≫ (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom) ≫
        (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom =
    (S.F.map (equivToIso (HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j))).hom).hom ≫
    (S.F.map (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm
    ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)).symm)).hom).hom
    ≫ (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)).hom := by
  ext X
  change ((S.F.map σ) ≫ (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom) ≫
    (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom)).hom X = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [extractTwo_finExtractTwo]
  simp only [Nat.succ_eq_add_one, extractOne_homToEquiv, Functor.map_comp, Action.comp_hom,
    ModuleCat.hom_comp, Function.comp_apply]
  rfl

lemma contrIso_comm_aux_2 {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)).hom ≫
    (Functor.Monoidal.μIso S.F
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom =
    (Functor.Monoidal.μIso S.F _ _).inv.hom ≫
    (S.F.map (extractTwoAux' i j σ) ⊗ S.F.map (extractTwoAux i j σ)).hom := by
  have h1 : (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)) ≫
    (Functor.Monoidal.μIso S.F
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv =
    (Functor.Monoidal.μIso S.F _ _).inv ≫
    (S.F.map (extractTwoAux' i j σ) ⊗ S.F.map (extractTwoAux i j σ)) := by
    apply (CategoryTheory.IsIso.comp_inv_eq _).mpr
    rw [CategoryTheory.Category.assoc]
    apply (CategoryTheory.IsIso.eq_inv_comp _).mpr
    exact (Functor.LaxMonoidal.μ_natural S.F (extractTwoAux' i j σ) (extractTwoAux i j σ)).symm
  exact congrArg (λ f => Action.Hom.hom f) h1

lemma contrIso_comm_aux_3 {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
      ((Action.functorCategoryEquivalence (ModuleCat S.k) (MonCat.of S.G)).symm.inverse.map
                  (S.F.map (extractTwoAux i j σ))).app
              PUnit.unit ≫
            (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom).hom
    = (S.F.map (mkIso (contrIso.proof_1 S c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j))).hom).hom ≫
    (S.F.map (extractTwo i j σ)).hom := by
  change (S.F.map (extractTwoAux i j σ)).hom ≫ _ = _
  have h1 : (S.F.map (extractTwoAux i j σ)) ≫ (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom) =
      (S.F.map (mkIso (contrIso.proof_1 S c ((Hom.toEquiv σ).symm i)
      ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j))).hom) ≫
      (S.F.map (extractTwo i j σ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (λ f => Action.Hom.hom f) h1

/-- A helper function used to proof the relation between perm and contr. -/
def contrIsoComm {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :=
  (((Discrete.pairτ S.FD S.τ).map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i) :
  (Discrete.mk (c ((Hom.toEquiv σ).symm i))) ⟶
  (Discrete.mk (c1 i)))) ⊗ (S.F.map (extractTwo i j σ)))

lemma contrIso_comm_aux_5 {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} (h : c1 (i.succAbove j) = S.τ (c1 i))
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map (extractTwoAux' i j σ) ⊗ S.F.map (extractTwoAux i j σ)).hom ≫
    ((S.contrFin1Fin1 c1 i j h).hom.hom ⊗ (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom).hom)
    = ((S.contrFin1Fin1 c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
    (perm_contr_cond S h σ)).hom.hom ⊗
    (S.F.map (mkIso (contrIso.proof_1 S c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j))).hom).hom)
    ≫ (S.contrIsoComm σ).hom := by
  conv_lhs =>
    erw [← CategoryTheory.MonoidalCategory.tensor_comp (f₁ := (S.F.map (extractTwoAux' i j σ)).hom)]
  rw [contrIso_comm_aux_3 S σ]
  rw [contrFin1Fin1_naturality S h σ]
  simp [contrIsoComm]

lemma contrIso_comm_map {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c1 (i.succAbove j) = S.τ (c1 i)}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
  (S.F.map σ) ≫ (S.contrIso c1 i j h).hom =
  (S.contrIso c ((OverColor.Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j) (S.perm_contr_cond h σ)).hom ≫
    contrIsoComm S σ := by
  ext1
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, Action.comp_hom,
    extractOne_homToEquiv, Action.instMonoidalCategory_tensorHom_hom]
  rw [contrIso_hom_hom]
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
    ← CategoryTheory.Category.assoc]
  rw [contrIso_comm_aux_1 S σ]
  rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc]
  rw [← CategoryTheory.Category.assoc (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)).hom]
  rw [contrIso_comm_aux_2 S σ]
  simp only [Nat.succ_eq_add_one, extractOne_homToEquiv, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorHom_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    contrIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom, Action.comp_hom,
    Category.assoc]
  apply congrArg
  apply congrArg
  apply congrArg
  simpa only [Nat.succ_eq_add_one, extractOne_homToEquiv, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorHom_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj] using contrIso_comm_aux_5 S h σ

/-- Contraction commutes with `S.F.map σ` on removing corresponding indices from `σ`. -/
lemma contrMap_naturality {n : ℕ} {c c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c1 (i.succAbove j) = S.τ (c1 i)}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map σ) ≫ (S.contrMap c1 i j h) =
    (S.contrMap c ((OverColor.Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j) (S.perm_contr_cond h σ)) ≫
    (S.F.map (extractTwo i j σ)) := by
  change (S.F.map σ) ≫ ((S.contrIso c1 i j h).hom ≫
    (tensorHom (S.contr.app (Discrete.mk (c1 i))) (𝟙 _)) ≫
    (MonoidalCategory.leftUnitor _).hom) =
    ((S.contrIso _ _ _ _).hom ≫
    (tensorHom (S.contr.app (Discrete.mk _)) (𝟙 _)) ≫ (MonoidalCategory.leftUnitor _).hom) ≫ _
  rw [← CategoryTheory.Category.assoc]
  rw [contrIso_comm_map S σ]
  repeat rw [CategoryTheory.Category.assoc]
  rw [← CategoryTheory.Category.assoc (S.contrIsoComm σ)]
  apply congrArg
  rw [← leftUnitor_naturality]
  repeat rw [← CategoryTheory.Category.assoc]
  apply congrFun
  apply congrArg
  rw [contrIsoComm]
  rw [← tensor_comp]
  have h1 : 𝟙_ (Rep S.k S.G) ◁ S.F.map (extractTwo i j σ) = 𝟙 _ ⊗ S.F.map (extractTwo i j σ) := by
    rfl
  rw [h1, ← tensor_comp]
  rw [CategoryTheory.Category.id_comp]
  erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id]
  rw [S.contr.naturality]
  rfl

end
end TensorSpecies

namespace TensorTree

variable {S : TensorSpecies}

/-- Permuting indices, and then contracting is equivalent to contracting and then permuting,
  once care is taking about ensuring one is contracting the same indices. -/
lemma perm_contr {n : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c1 (i.succAbove j) = S.τ (c1 i)} (t : TensorTree S c)
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (contr i j h (perm σ t)).tensor
    = (perm (extractTwo i j σ) (contr ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j) (S.perm_contr_cond h σ) t)).tensor := by
  rw [contr_tensor, perm_tensor, perm_tensor]
  change ((S.F.map σ) ≫ S.contrMap c1 i j h).hom t.tensor = _
  rw [S.contrMap_naturality σ]
  rfl

lemma perm_contr_congr_mkIso_cond {n : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)}
    {i' : Fin n.succ.succ} {j' : Fin n.succ}
    (hi : i' = ((Hom.toEquiv σ).symm i))
    (hj : j' = (((Hom.toEquiv (extractOne i σ))).symm j)) :
    c ∘ i'.succAbove ∘ j'.succAbove = c ∘ Fin.succAbove ((Hom.toEquiv σ).symm i) ∘
    Fin.succAbove ((Hom.toEquiv (extractOne i σ)).symm j) := by
  rw [hi, hj]

lemma perm_contr_congr_contr_cond {n : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    (h : c1 (i.succAbove j) = S.τ (c1 i))
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)}
    {i' : Fin n.succ.succ} {j' : Fin n.succ}
    (hi : i' = ((Hom.toEquiv σ).symm i))
    (hj : j' = (((Hom.toEquiv (extractOne i σ))).symm j)) :
    c (i'.succAbove j') = S.τ (c i') := by
  rw [hi, hj]
  exact S.perm_contr_cond h σ

lemma perm_contr_congr {n : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c1 (i.succAbove j) = S.τ (c1 i)} {t : TensorTree S c}
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)}
    (i' : Fin n.succ.succ) (j' : Fin n.succ)
    (hi : i' = ((Hom.toEquiv σ).symm i) := by decide)
    (hj : j' = (((Hom.toEquiv (extractOne i σ))).symm j) := by decide) :
  (contr i j h (perm σ t)).tensor = (perm ((mkIso (perm_contr_congr_mkIso_cond hi hj)).hom ≫
    extractTwo i j σ) (contr i' j' (perm_contr_congr_contr_cond h hi hj) t)).tensor := by
  rw [perm_contr]
  rw [perm_tensor_eq <| contr_congr i' j' hi.symm hj.symm]
  rw [perm_perm]

end TensorTree
