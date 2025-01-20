/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.Basic
/-!

## The contraction map

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct
noncomputable section

namespace TensorSpecies

variable (S : TensorSpecies)

/-- The isomorphism between the image of a map `Fin 1 ⊕ Fin 1 → S.C` constructed by `finExtractTwo`
  under `S.F.obj`, and an object in the image of `OverColor.Discrete.pairτ S.FD`. -/
def contrFin1Fin1 {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)) ≅
    (OverColor.Discrete.pairτ S.FD S.τ).obj { as := c i } := by
  apply (S.F.mapIso
    (OverColor.mkSum (((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)))).trans
  apply (Functor.Monoidal.μIso S.F _ _).symm.trans
  apply tensorIso ?_ ?_
  · symm
    apply (OverColor.forgetLiftApp S.FD (c i)).symm.trans
    apply S.F.mapIso
    apply OverColor.mkIso
    funext x
    fin_cases x
    rfl
  · symm
    apply (OverColor.forgetLiftApp S.FD (S.τ (c i))).symm.trans
    apply S.F.mapIso
    apply OverColor.mkIso
    funext x
    fin_cases x
    simp [h]

lemma contrFin1Fin1_inv_tmul {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i))
    (x : S.FD.obj { as := c i })
    (y : S.FD.obj { as := S.τ (c i) }) :
    (S.contrFin1Fin1 c i j h).inv.hom (x ⊗ₜ[S.k] y) =
    PiTensorProduct.tprod S.k (fun k =>
    match k with | Sum.inl 0 => x | Sum.inr 0 => (S.FD.map
    (eqToHom (by simp [h]))).hom y) := by
  simp only [Nat.succ_eq_add_one, contrFin1Fin1, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_inv, tensorIso_inv,
    Iso.symm_inv, Functor.mapIso_hom, tensor_comp, Functor.Monoidal.μIso_hom,
    Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Category.assoc, Functor.LaxMonoidal.μ_natural,
    Functor.mapIso_inv, Action.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorHom_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.hom_comp, mk_left, Functor.id_obj, mk_hom, Fin.isValue]
  change (S.F.map (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    ((S.F.map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
      ((Functor.LaxMonoidal.μ S.F (OverColor.mk fun _ => c i) (OverColor.mk fun _ => S.τ (c i))).hom
        ((((OverColor.forgetLiftApp S.FD (c i)).inv.hom x) ⊗ₜ[S.k]
        ((OverColor.forgetLiftApp S.FD (S.τ (c i))).inv.hom y))))) = _
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    forgetLiftApp, Action.mkIso_inv_hom, LinearEquiv.toModuleIso_inv_hom, Fin.isValue]
  erw [OverColor.forgetLiftAppV_symm_apply,
    OverColor.forgetLiftAppV_symm_apply S.FD (S.τ (c i))]
  change ((OverColor.lift.obj S.FD).map (OverColor.mkSum
    ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    (((OverColor.lift.obj S.FD).map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
    ((Functor.LaxMonoidal.μ (OverColor.lift.obj S.FD).toFunctor (OverColor.mk fun _ => c i)
    (OverColor.mk fun _ => S.τ (c i))).hom
    (((PiTensorProduct.tprod S.k) fun _ => x) ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) fun _ => y))) = _
  rw [OverColor.lift.obj_μ_tprod_tmul S.FD]
  change ((OverColor.lift.obj S.FD).map
    (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    (((OverColor.lift.obj S.FD).map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
    ((PiTensorProduct.tprod S.k) _)) = _
  rw [OverColor.lift.map_tprod S.FD]
  change ((OverColor.lift.obj S.FD).map
    (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    ((PiTensorProduct.tprod S.k _)) = _
  rw [OverColor.lift.map_tprod S.FD]
  apply congrArg
  funext r
  match r with
  | Sum.inl 0 =>
    simp only [Nat.succ_eq_add_one, mk_hom, Fin.isValue, Function.comp_apply,
      instMonoidalCategoryStruct_tensorObj_left, mkSum_inv_homToEquiv, Equiv.refl_symm,
      instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, lift.discreteSumEquiv, Sum.elim_inl,
      Sum.elim_inr, HepLean.PiTensorProduct.elimPureTensor]
    simp only [Fin.isValue, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    rfl
  | Sum.inr 0 =>
    simp only [Nat.succ_eq_add_one, mk_hom, Fin.isValue, Function.comp_apply,
      instMonoidalCategoryStruct_tensorObj_left, mkSum_inv_homToEquiv, Equiv.refl_symm,
      instMonoidalCategoryStruct_tensorObj_hom, lift.discreteFunctorMapEqIso, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, Functor.mapIso_hom,
      eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, Functor.id_obj, lift.discreteSumEquiv,
      Sum.elim_inl, Sum.elim_inr, HepLean.PiTensorProduct.elimPureTensor,
      LinearEquiv.ofLinear_apply]
    rfl

lemma contrFin1Fin1_hom_hom_tprod {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i))
    (x : (k : Fin 1 ⊕ Fin 1) → (S.FD.obj
      { as := (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).hom k })) :
    (S.contrFin1Fin1 c i j h).hom.hom (PiTensorProduct.tprod S.k x) =
    x (Sum.inl 0) ⊗ₜ[S.k] ((S.FD.map (eqToHom (by simp [h]))).hom (x (Sum.inr 0))) := by
  change ((Action.forget _ _).mapIso (S.contrFin1Fin1 c i j h)).hom _ = _
  trans ((Action.forget _ _).mapIso (S.contrFin1Fin1 c i j h)).toLinearEquiv
    (PiTensorProduct.tprod S.k x)
  · rfl
  erw [← LinearEquiv.eq_symm_apply]
  erw [contrFin1Fin1_inv_tmul]
  congr
  funext i
  match i with
  | Sum.inl 0 =>
    rfl
  | Sum.inr 0 =>
    simp only [Nat.succ_eq_add_one, Fin.isValue, mk_hom, Function.comp_apply,
      Discrete.functor_obj_eq_as]
    change _ = ((S.FD.map (eqToHom _)) ≫ (S.FD.map (eqToHom _))).hom (x (Sum.inr 0))
    rw [← Functor.map_comp]
    simp
  exact h

/-- The isomorphism of objects in `Rep S.k S.G` given an `i` in `Fin n.succ.succ` and
  a `j` in `Fin n.succ` allowing us to undertake contraction. -/
def contrIso {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ≅ ((OverColor.Discrete.pairτ S.FD S.τ).obj
      (Discrete.mk (c i))) ⊗
      (OverColor.lift.obj S.FD).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (S.F.mapIso (OverColor.equivToIso (HepLean.Fin.finExtractTwo i j))).trans <|
  (S.F.mapIso (OverColor.mkSum (c ∘ (HepLean.Fin.finExtractTwo i j).symm))).trans <|
  (Functor.Monoidal.μIso S.F _ _).symm.trans <| by
  refine tensorIso (S.contrFin1Fin1 c i j h) (S.F.mapIso (OverColor.mkIso (by ext x; simp)))

lemma contrIso_hom_hom {n : ℕ} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c1 (i.succAbove j) = S.τ (c1 i)} :
    (S.contrIso c1 i j h).hom.hom =
    (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom ≫
    (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom ≫
    (Functor.Monoidal.μIso S.F
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom ≫
    ((S.contrFin1Fin1 c1 i j h).hom.hom ⊗
    (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom).hom) := by
  rfl

/-- `contrMap` is a function that takes a natural number `n`, a function `c` from
`Fin n.succ.succ` to `S.C`, an index `i` of type `Fin n.succ.succ`, an index `j` of type
`Fin n.succ`, and a proof `h` that `c (i.succAbove j) = S.τ (c i)`. It returns a morphism
corresponding to the contraction of the `i`th index with the `i.succAbove j` index.
--/
def contrMap {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ⟶
    S.F.obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (S.contrIso c i j h).hom ≫
  (tensorHom (S.contr.app (Discrete.mk (c i))) (𝟙 _)) ≫
  (MonoidalCategory.leftUnitor _).hom

/-- Acting with `contrMap` on a `tprod` gives a `tprod` multiplied by a scalar. -/
lemma contrMap_tprod {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i))
    (x : (i : Fin n.succ.succ) → S.FD.obj (Discrete.mk (c i))) :
    (S.contrMap c i j h).hom (PiTensorProduct.tprod S.k x) =
    (S.castToField ((S.contr.app (Discrete.mk (c i))).hom ((x i) ⊗ₜ[S.k]
    (S.FD.map (Discrete.eqToHom h)).hom (x (i.succAbove j)))) : S.k)
    • (PiTensorProduct.tprod S.k (fun k => x (i.succAbove (j.succAbove k))) :
    S.F.obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))) := by
  rw [contrMap, contrIso]
  simp only [Nat.succ_eq_add_one, S.F_def, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorIso_hom, Monoidal.tensorUnit_obj, tensorHom_id,
    Category.assoc, Action.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorHom_hom, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_whiskerRight_hom, Functor.id_obj, mk_hom, ModuleCat.hom_comp,
    Function.comp_apply, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj, Discrete.functor_obj_eq_as]
  change (λ_ ((lift.obj S.FD).obj _)).hom.hom
    (((S.contr.app { as := c i }).hom ▷ ((lift.obj S.FD).obj
    (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))).V)
    (((S.contrFin1Fin1 c i j h).hom.hom ⊗ ((lift.obj S.FD).map (mkIso _).hom).hom)
    ((Functor.Monoidal.μIso (lift.obj S.FD).toFunctor
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom
    (((lift.obj S.FD).map (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom
    (((lift.obj S.FD).map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom
    ((PiTensorProduct.tprod S.k) x)))))) = _
  rw [lift.map_tprod]
  erw [lift.map_tprod]
  erw [lift.μIso_inv_tprod]
  change (λ_ ((lift.obj S.FD).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)))).hom.hom
    (((S.contr.app { as := c i }).hom ▷ ((lift.obj S.FD).obj
    (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))).V)
    ((TensorProduct.map (S.contrFin1Fin1 c i j h).hom.hom.hom
    ((lift.obj S.FD).map (mkIso _).hom).hom.hom)
    (((PiTensorProduct.tprod S.k) fun i_1 =>
    (lift.discreteFunctorMapEqIso S.FD _)
    ((lift.discreteFunctorMapEqIso S.FD _) (x
    ((Hom.toEquiv (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).symm
    ((Hom.toEquiv (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).symm
    (Sum.inl i_1)))))) ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) fun i_1 =>
    (lift.discreteFunctorMapEqIso S.FD _) ((lift.discreteFunctorMapEqIso S.FD _)
    (x ((Hom.toEquiv (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).symm
    ((Hom.toEquiv
    (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).symm (Sum.inr i_1)))))))) = _
  rw [TensorProduct.map_tmul]
  rw [contrFin1Fin1_hom_hom_tprod]
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorUnit_V, Fin.isValue, mk_hom, Function.comp_apply,
    Discrete.functor_obj_eq_as, instMonoidalCategoryStruct_tensorObj_left, mkSum_homToEquiv,
    Equiv.refl_symm, Functor.id_obj, ModuleCat.MonoidalCategory.whiskerRight_apply]
  rw [Action.instMonoidalCategory_leftUnitor_hom_hom]
  simp only [Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  congr 1
  /- The contraction. -/
  · simp only [Fin.isValue, castToField]
    congr 2
    · simp only [Fin.isValue, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
      rfl
    · simp only [Fin.isValue, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
      change (S.FD.map (eqToHom _)).hom
        (x (((HepLean.Fin.finExtractTwo i j)).symm ((Sum.inl (Sum.inr 0))))) = _
      simp only [Nat.succ_eq_add_one, Fin.isValue]
      have h1' {a b d: Fin n.succ.succ} (hbd : b =d) (h : c d = S.τ (c a)) (h' : c b = S.τ (c a)) :
          (S.FD.map (Discrete.eqToHom (h))).hom (x d) =
          (S.FD.map (Discrete.eqToHom h')).hom (x b) := by
        subst hbd
        rfl
      refine h1' ?_ ?_ ?_
      simp only [Nat.succ_eq_add_one, Fin.isValue, HepLean.Fin.finExtractTwo_symm_inl_inr_apply]
      simp [h]
  /- The tensor. -/
  · erw [lift.map_tprod]
    apply congrArg
    funext d
    simp only [mk_hom, Function.comp_apply, lift.discreteFunctorMapEqIso, Functor.mapIso_hom,
      eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom,
      Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    change (S.FD.map (eqToHom _)).hom
        ((x ((HepLean.Fin.finExtractTwo i j).symm (Sum.inr (d))))) = _
    simp only [Nat.succ_eq_add_one]
    have h1 : ((HepLean.Fin.finExtractTwo i j).symm (Sum.inr d))
      = (i.succAbove (j.succAbove d)) := HepLean.Fin.finExtractTwo_symm_inr_apply i j d
    have h1' {a b : Fin n.succ.succ} (h : a = b) :
      (S.FD.map (eqToHom (by rw [h]))).hom (x a) = x b := by
      subst h
      simp
    exact h1' h1

end TensorSpecies

end
