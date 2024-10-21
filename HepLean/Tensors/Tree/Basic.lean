/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Iso
import HepLean.Tensors.OverColor.Discrete
import HepLean.Tensors.OverColor.Lift
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
/-!

## Tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

/-- The sturcture of a type of tensors e.g. Lorentz tensors, Einstien tensors,
  complex Lorentz tensors. -/
structure TensorSpecies where
  /-- The colors of indices e.g. up or down. -/
  C : Type
  /-- The symmetry group acting on these tensor e.g. the Lorentz group or SL(2,ℂ). -/
  G : Type
  /-- An instance of `G` as a group. -/
  G_group : Group G
  /-- The field over which we want to consider the tensors to live in, usually `ℝ` or `ℂ`. -/
  k : Type
  /-- An instance of `k` as a commutative ring. -/
  k_commRing : CommRing k
  /-- A `MonoidalFunctor` from `OverColor C` giving the rep corresponding to a map of colors
    `X → C`. -/
  FDiscrete : Discrete C ⥤ Rep k G
  /-- A map from `C` to `C`. An involution. -/
  τ : C → C
  /-- The condition that `τ` is an involution. -/
  τ_involution : Function.Involutive τ
  /-- The natural transformation describing contraction. -/
  contr : OverColor.Discrete.pairτ FDiscrete τ ⟶ 𝟙_ (Discrete C ⥤ Rep k G)
  /-- The natural transformation describing the metric. -/
  metric : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.pair FDiscrete
  /-- The natural transformation describing the unit. -/
  unit : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.τPair FDiscrete τ
  /-- A specification of the dimension of each color in C. This will be used for explicit
    evaluation of tensors. -/
  evalNo : C → ℕ
  /-- Contraction is symmetric with respect to duals. -/
  contr_tmul_symm (c : C) (x : FDiscrete.obj (Discrete.mk c))
      (y : FDiscrete.obj (Discrete.mk (τ c))) :
    (contr.app (Discrete.mk c)).hom (x ⊗ₜ[k] y) = (contr.app (Discrete.mk (τ c))).hom
      (y ⊗ₜ (FDiscrete.map (Discrete.eqToHom (τ_involution c).symm)).hom x)

noncomputable section

namespace TensorSpecies
open OverColor

variable (S : TensorSpecies)

instance : CommRing S.k := S.k_commRing

instance : Group S.G := S.G_group

/-- The lift of the functor `S.F` to a monoidal functor. -/
def F : BraidedFunctor (OverColor S.C) (Rep S.k S.G) := (OverColor.lift).obj S.FDiscrete

lemma F_def : F S = (OverColor.lift).obj S.FDiscrete := rfl

lemma perm_contr_cond {n : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ}
    (h : c1 (i.succAbove j) = S.τ (c1 i)) (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    c (Fin.succAbove ((Hom.toEquiv σ).symm i) ((Hom.toEquiv (extractOne i σ)).symm j)) =
    S.τ (c ((Hom.toEquiv σ).symm i)) := by
  have h1 := Hom.toEquiv_comp_apply σ
  simp only [Nat.succ_eq_add_one, Functor.const_obj_obj, mk_hom] at h1
  rw [h1, h1]
  simp only [Nat.succ_eq_add_one, extractOne_homToEquiv, Equiv.apply_symm_apply]
  rw [← h]
  congr
  simp only [Nat.succ_eq_add_one, HepLean.Fin.finExtractOnePerm, HepLean.Fin.finExtractOnPermHom,
    HepLean.Fin.finExtractOne_symm_inr_apply, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
  erw [Equiv.apply_symm_apply]
  rw [HepLean.Fin.succsAbove_predAboveI]
  erw [Equiv.apply_symm_apply]
  simp only [Nat.succ_eq_add_one, ne_eq]
  erw [Equiv.apply_eq_iff_eq]
  exact (Fin.succAbove_ne i j).symm

/-- The isomorphism between the image of a map `Fin 1 ⊕ Fin 1 → S.C` contructed by `finExtractTwo`
  under `S.F.obj`, and an object in the image of `OverColor.Discrete.pairτ S.FDiscrete`. -/
def contrFin1Fin1 {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)) ≅
    (OverColor.Discrete.pairτ S.FDiscrete S.τ).obj { as := c i } := by
  apply (S.F.mapIso
    (OverColor.mkSum (((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)))).trans
  apply (S.F.μIso _ _).symm.trans
  apply tensorIso ?_ ?_
  · symm
    apply (OverColor.forgetLiftApp S.FDiscrete (c i)).symm.trans
    apply S.F.mapIso
    apply OverColor.mkIso
    funext x
    fin_cases x
    rfl
  · symm
    apply (OverColor.forgetLiftApp S.FDiscrete (S.τ (c i))).symm.trans
    apply S.F.mapIso
    apply OverColor.mkIso
    funext x
    fin_cases x
    simp [h]

lemma contrFin1Fin1_inv_tmul {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i))
    (x : S.FDiscrete.obj { as := c i })
    (y : S.FDiscrete.obj { as := S.τ (c i) }) :
    (S.contrFin1Fin1 c i j h).inv.hom (x ⊗ₜ[S.k] y) =
    PiTensorProduct.tprod S.k (fun k =>
    match k with | Sum.inl 0 => x | Sum.inr 0 => (S.FDiscrete.map
    (eqToHom (by simp [h]))).hom y) := by
  simp only [Nat.succ_eq_add_one, contrFin1Fin1, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_inv, tensorIso_inv,
    Iso.symm_inv, Functor.mapIso_hom, tensor_comp, MonoidalFunctor.μIso_hom, Category.assoc,
    LaxMonoidalFunctor.μ_natural, Functor.mapIso_inv, Action.comp_hom,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorHom_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Functor.id_obj, mk_hom,
    Fin.isValue]
  change (S.F.map (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    ((S.F.map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
      ((S.F.μ (OverColor.mk fun _ => c i) (OverColor.mk fun _ => S.τ (c i))).hom
        ((((OverColor.forgetLiftApp S.FDiscrete (c i)).inv.hom x) ⊗ₜ[S.k]
        ((OverColor.forgetLiftApp S.FDiscrete (S.τ (c i))).inv.hom y))))) = _
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    forgetLiftApp, Action.mkIso_inv_hom, LinearEquiv.toModuleIso_inv, Fin.isValue]
  erw [OverColor.forgetLiftAppV_symm_apply,
    OverColor.forgetLiftAppV_symm_apply S.FDiscrete (S.τ (c i))]
  change ((OverColor.lift.obj S.FDiscrete).map (OverColor.mkSum
    ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    (((OverColor.lift.obj S.FDiscrete).map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
    (((OverColor.lift.obj S.FDiscrete).μ (OverColor.mk fun _ => c i)
    (OverColor.mk fun _ => S.τ (c i))).hom
    (((PiTensorProduct.tprod S.k) fun _ => x) ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) fun _ => y))) = _
  rw [OverColor.lift.obj_μ_tprod_tmul S.FDiscrete]
  change ((OverColor.lift.obj S.FDiscrete).map
    (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    (((OverColor.lift.obj S.FDiscrete).map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
    ((PiTensorProduct.tprod S.k) _)) = _
  rw [OverColor.lift.map_tprod S.FDiscrete]
  change ((OverColor.lift.obj S.FDiscrete).map
    (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    ((PiTensorProduct.tprod S.k _)) = _
  rw [OverColor.lift.map_tprod S.FDiscrete]
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
    (x : (k : Fin 1 ⊕ Fin 1) → (S.FDiscrete.obj
      { as := (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).hom k })) :
    (S.contrFin1Fin1 c i j h).hom.hom (PiTensorProduct.tprod S.k x) =
    x (Sum.inl 0) ⊗ₜ[S.k] ((S.FDiscrete.map (eqToHom (by simp [h]))).hom (x (Sum.inr 0))) := by
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
    change _ = ((S.FDiscrete.map (eqToHom _)) ≫ (S.FDiscrete.map (eqToHom _))).hom (x (Sum.inr 0))
    rw [← Functor.map_comp]
    simp
  exact h

/-- The isomorphism of objects in `Rep S.k S.G` given an `i` in `Fin n.succ.succ` and
  a `j` in `Fin n.succ` allowing us to undertake contraction. -/
def contrIso {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ≅ ((OverColor.Discrete.pairτ S.FDiscrete S.τ).obj
      (Discrete.mk (c i))) ⊗
      (OverColor.lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (S.F.mapIso (OverColor.equivToIso (HepLean.Fin.finExtractTwo i j))).trans <|
  (S.F.mapIso (OverColor.mkSum (c ∘ (HepLean.Fin.finExtractTwo i j).symm))).trans <|
  (S.F.μIso _ _).symm.trans <| by
  refine tensorIso (S.contrFin1Fin1 c i j h) (S.F.mapIso (OverColor.mkIso (by ext x; simp)))

lemma contrIso_hom_hom {n : ℕ} {c1 : Fin n.succ.succ → S.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c1 (i.succAbove j) = S.τ (c1 i)} :
    (S.contrIso c1 i j h).hom.hom =
    (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom ≫
    (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom ≫
    (S.F.μIso (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
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

/-- Casts an element of the monoidal unit of `Rep S.k S.G` to the field `S.k`. -/
def castToField (v : (↑((𝟙_ (Discrete S.C ⥤ Rep S.k S.G)).obj { as := c }).V)) : S.k := v

lemma contrMap_tprod {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i))
    (x : (i : Fin n.succ.succ) → S.FDiscrete.obj (Discrete.mk (c i))) :
    (S.contrMap c i j h).hom (PiTensorProduct.tprod S.k x) =
    (S.castToField ((S.contr.app (Discrete.mk (c i))).hom ((x i) ⊗ₜ[S.k]
    (S.FDiscrete.map (Discrete.eqToHom h)).hom (x (i.succAbove j)))) : S.k)
    • (PiTensorProduct.tprod S.k (fun k => x (i.succAbove (j.succAbove k))) :
    S.F.obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))) := by
  rw [contrMap, contrIso]
  simp only [Nat.succ_eq_add_one, S.F_def, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorIso_hom, Monoidal.tensorUnit_obj, tensorHom_id,
    Category.assoc, Action.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorHom_hom, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_whiskerRight_hom, Functor.id_obj, mk_hom, ModuleCat.coe_comp,
    Function.comp_apply, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj, Discrete.functor_obj_eq_as]
  change (λ_ ((lift.obj S.FDiscrete).obj _)).hom.hom
    (((S.contr.app { as := c i }).hom ▷ ((lift.obj S.FDiscrete).obj
    (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))).V)
    (((S.contrFin1Fin1 c i j h).hom.hom ⊗ ((lift.obj S.FDiscrete).map (mkIso _).hom).hom)
    (((lift.obj S.FDiscrete).μIso (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)
    ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom
    (((lift.obj S.FDiscrete).map (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom
    (((lift.obj S.FDiscrete).map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom
    ((PiTensorProduct.tprod S.k) x)))))) = _
  rw [lift.map_tprod]
  change (λ_ ((lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)))).hom.hom
    (((S.contr.app { as := c i }).hom ▷
    ((lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))).V)
    (((S.contrFin1Fin1 c i j h).hom.hom ⊗ ((lift.obj S.FDiscrete).map (mkIso _).hom).hom)
    (((lift.obj S.FDiscrete).μIso (OverColor.mk
    ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom
    (((lift.obj S.FDiscrete).map (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom
    ((PiTensorProduct.tprod S.k) fun i_1 =>
    (lift.discreteFunctorMapEqIso S.FDiscrete _)
    (x ((Hom.toEquiv (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).symm i_1))))))) = _
  rw [lift.map_tprod]
  change (λ_ ((lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)))).hom.hom
    (((S.contr.app { as := c i }).hom ▷ ((lift.obj S.FDiscrete).obj
    (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))).V)
    (((S.contrFin1Fin1 c i j h).hom.hom ⊗ ((lift.obj S.FDiscrete).map (mkIso _).hom).hom)
    (((lift.obj S.FDiscrete).μIso
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom
    ((PiTensorProduct.tprod S.k) fun i_1 =>
    (lift.discreteFunctorMapEqIso S.FDiscrete _)
    ((lift.discreteFunctorMapEqIso S.FDiscrete _)
    (x ((Hom.toEquiv (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).symm
    ((Hom.toEquiv (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).symm i_1)))))))) = _
  rw [lift.μIso_inv_tprod]
  change (λ_ ((lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)))).hom.hom
    (((S.contr.app { as := c i }).hom ▷ ((lift.obj S.FDiscrete).obj
    (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove))).V)
    ((TensorProduct.map (S.contrFin1Fin1 c i j h).hom.hom
    ((lift.obj S.FDiscrete).map (mkIso _).hom).hom)
    (((PiTensorProduct.tprod S.k) fun i_1 =>
    (lift.discreteFunctorMapEqIso S.FDiscrete _)
    ((lift.discreteFunctorMapEqIso S.FDiscrete _) (x
    ((Hom.toEquiv (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).symm
    ((Hom.toEquiv (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).symm
    (Sum.inl i_1)))))) ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) fun i_1 =>
    (lift.discreteFunctorMapEqIso S.FDiscrete _) ((lift.discreteFunctorMapEqIso S.FDiscrete _)
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
      change (S.FDiscrete.map (eqToHom _)).hom
        (x (((HepLean.Fin.finExtractTwo i j)).symm ((Sum.inl (Sum.inr 0))))) = _
      simp only [Nat.succ_eq_add_one, Fin.isValue]
      have h1' {a b d: Fin n.succ.succ} (hbd : b =d) (h : c d = S.τ (c a)) (h' : c b = S.τ (c a)) :
          (S.FDiscrete.map (Discrete.eqToHom (h))).hom (x d) =
          (S.FDiscrete.map (Discrete.eqToHom h')).hom (x b) := by
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
    change (S.FDiscrete.map (eqToHom _)).hom
        ((x ((HepLean.Fin.finExtractTwo i j).symm (Sum.inr (d))))) = _
    simp only [Nat.succ_eq_add_one]
    have h1 : ((HepLean.Fin.finExtractTwo i j).symm (Sum.inr d))
      = (i.succAbove (j.succAbove d)) := HepLean.Fin.finExtractTwo_symm_inr_apply i j d
    have h1' {a b : Fin n.succ.succ} (h : a = b) :
      (S.FDiscrete.map (eqToHom (by rw [h]))).hom (x a) = x b := by
      subst h
      simp
    exact h1' h1

end TensorSpecies

/-- A syntax tree for tensor expressions. -/
inductive TensorTree (S : TensorSpecies) : ∀ {n : ℕ}, (Fin n → S.C) → Type where
  /-- A general tensor node. -/
  | tensorNode {n : ℕ} {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) : TensorTree S c
  /-- A node consisting of a single vector. -/
  | vecNode {c : S.C} (v : S.FDiscrete.obj (Discrete.mk c)) : TensorTree S ![c]
  /-- A node consisting of a two tensor. -/
  | twoNode {c1 c2 : S.C}
    (v : (S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)).V) :
    TensorTree S ![c1, c2]
  /-- A node consisting of a three tensor. -/
  | threeNode {c1 c2 c3 : S.C}
    (v : S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2) ⊗
      S.FDiscrete.obj (Discrete.mk c3)) : TensorTree S ![c1, c2, c3]
  /-- A general constant node. -/
  | constNode {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep S.k S.G) ⟶ S.F.obj (OverColor.mk c)) :
    TensorTree S c
  /-- A constant vector. -/
  | constVecNode {c : S.C} (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c)) :
    TensorTree S ![c]
  /-- A constant two tensor (e.g. metric and unit). -/
  | constTwoNode {c1 c2 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)) :
    TensorTree S ![c1, c2]
  /-- A constant three tensor (e.g. Pauli-matrices). -/
  | constThreeNode {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2) ⊗
      S.FDiscrete.obj (Discrete.mk c3)) : TensorTree S ![c1, c2, c3]
  /-- A node corresponding to the addition of two tensors. -/
  | add {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c → TensorTree S c
  /-- A node corresponding to the permutation of indices of a tensor. -/
  | perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) : TensorTree S c1
  | prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t : TensorTree S c) (t1 : TensorTree S c1) : TensorTree S (Sum.elim c c1 ∘ finSumFinEquiv.symm)
  | smul {n : ℕ} {c : Fin n → S.C} : S.k → TensorTree S c → TensorTree S c
  /-- The negative of a node. -/
  | neg {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c
  | contr {n : ℕ} {c : Fin n.succ.succ → S.C} : (i : Fin n.succ.succ) →
    (j : Fin n.succ) → (h : c (i.succAbove j) = S.τ (c i)) → TensorTree S c →
    TensorTree S (c ∘ Fin.succAbove i ∘ Fin.succAbove j)
  | eval {n : ℕ} {c : Fin n.succ → S.C} :
    (i : Fin n.succ) → (x : Fin (S.evalNo (c i))) → TensorTree S c →
    TensorTree S (c ∘ Fin.succAbove i)

namespace TensorTree

variable {S : TensorSpecies} {n : ℕ} {c : Fin n → S.C} (T : TensorTree S c)

open MonoidalCategory
open TensorProduct

/-- The node `twoNode` of a tensor tree, with all arguments explicit. -/
abbrev twoNodeE (S : TensorSpecies) (c1 c2 : S.C)
    (v : (S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)).V) :
    TensorTree S ![c1, c2] := twoNode v

/-- The node `constTwoNodeE` of a tensor tree, with all arguments explicit. -/
abbrev constTwoNodeE (S : TensorSpecies) (c1 c2 : S.C)
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)) :
    TensorTree S ![c1, c2] := constTwoNode v

/-- The node `constThreeNodeE` of a tensor tree, with all arguments explicit. -/
abbrev constThreeNodeE (S : TensorSpecies) (c1 c2 c3 : S.C)
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2) ⊗
      S.FDiscrete.obj (Discrete.mk c3)) : TensorTree S ![c1, c2, c3] :=
    constThreeNode v

/-- The number of nodes in a tensor tree. -/
def size : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → ℕ := fun
  | tensorNode _ => 1
  | vecNode _ => 1
  | twoNode _ => 1
  | threeNode _ => 1
  | constNode _ => 1
  | constVecNode _ => 1
  | constTwoNode _ => 1
  | constThreeNode _ => 1
  | add t1 t2 => t1.size + t2.size + 1
  | perm _ t => t.size + 1
  | neg t => t.size + 1
  | smul _ t => t.size + 1
  | prod t1 t2 => t1.size + t2.size + 1
  | contr _ _ _ t => t.size + 1
  | eval _ _ t => t.size + 1

noncomputable section

/-- The underlying tensor a tensor tree corresponds to.
  Note: This function is not fully defined yet. -/
def tensor : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → S.F.obj (OverColor.mk c) := fun
  | tensorNode t => t
  | twoNode t => (OverColor.Discrete.pairIsoSep S.FDiscrete).hom.hom t
  | constTwoNode t => (OverColor.Discrete.pairIsoSep S.FDiscrete).hom.hom (t.hom (1 : S.k))
  | add t1 t2 => t1.tensor + t2.tensor
  | perm σ t => (S.F.map σ).hom t.tensor
  | neg t => - t.tensor
  | smul a t => a • t.tensor
  | prod t1 t2 => (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor))
  | contr i j h t => (S.contrMap _ i j h).hom t.tensor
  | _ => 0

/-!

## Tensor on different nodes.

-/

@[simp]
lemma tensorNode_tensor {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    (tensorNode T).tensor = T := rfl

@[simp]
lemma constTwoNode_tensor {c1 c2 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)) :
    (constTwoNode v).tensor =
    (OverColor.Discrete.pairIsoSep S.FDiscrete).hom.hom (v.hom (1 : S.k)) :=
  rfl

lemma prod_tensor {c1 : Fin n → S.C} {c2 : Fin m → S.C} (t1 : TensorTree S c1)
    (t2 : TensorTree S c2) :
    (prod t1 t2).tensor = (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor)) := rfl

lemma add_tensor (t1 t2 : TensorTree S c) : (add t1 t2).tensor = t1.tensor + t2.tensor := rfl

lemma perm_tensor (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
    (perm σ t).tensor = (S.F.map σ).hom t.tensor := rfl

lemma contr_tensor {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)} (t : TensorTree S c) :
    (contr i j h t).tensor = (S.contrMap c i j h).hom t.tensor := rfl

lemma neg_tensor (t : TensorTree S c) : (neg t).tensor = - t.tensor := rfl

/-!

## Equality of tensors and rewrites.

-/
lemma contr_tensor_eq {n : ℕ} {c : Fin n.succ.succ → S.C} {T1 T2 : TensorTree S c}
    (h : T1.tensor = T2.tensor) {i : Fin n.succ.succ} {j : Fin n.succ}
    {h' : c (i.succAbove j) = S.τ (c i)} :
    (contr i j h' T1).tensor = (contr i j h' T2).tensor := by
  simp only [Nat.succ_eq_add_one, contr_tensor]
  rw [h]

lemma prod_tensor_eq_fst {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {T1 T1' : TensorTree S c} { T2 : TensorTree S c1}
    (h : T1.tensor = T1'.tensor) :
    (prod T1 T2).tensor = (prod T1' T2).tensor := by
  simp only [prod_tensor, Functor.id_obj, OverColor.mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [h]

lemma prod_tensor_eq_snd {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {T1 : TensorTree S c} {T2 T2' : TensorTree S c1}
    (h : T2.tensor = T2'.tensor) :
    (prod T1 T2).tensor = (prod T1 T2').tensor := by
  simp only [prod_tensor, Functor.id_obj, OverColor.mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [h]

lemma perm_tensor_eq {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)} {T1 T2 : TensorTree S c}
    (h : T1.tensor = T2.tensor) :
    (perm σ T1).tensor = (perm σ T2).tensor := by
  simp only [perm_tensor]
  rw [h]

/-- A structure containing a pair of indices (i, j) to be contracted in a tensor.
  This is used in some proofs of node identities for tensor trees. -/
structure ContrPair {n : ℕ} (c : Fin n.succ.succ → S.C) where
  /-- The first index in the pair, appearing on the left in the contraction
    node `contr i j h _`. -/
  i : Fin n.succ.succ
  /-- The second index in the pair, appearing on the right in the contraction
    node `contr i j h _`. -/
  j : Fin n.succ
  /-- A proof that the two indices can be contracted. -/
  h : c (i.succAbove j) = S.τ (c i)

namespace ContrPair
variable {n : ℕ} {c : Fin n.succ.succ → S.C} {q q' : ContrPair c}

lemma ext (hi : q.i = q'.i) (hj : q.j = q'.j) : q = q' := by
  cases q
  cases q'
  subst hi
  subst hj
  rfl

/-- The contraction map for a pair of indices. -/
def contrMap := S.contrMap c q.i q.j q.h

end ContrPair
end

end TensorTree

end
