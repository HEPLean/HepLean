/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Discrete
/-!

# Tensor species

- A tensor species is a structure including all of the ingredients needed to define a type of
  tensor.
- Examples of tensor species will include real Lorentz tensors, complex Lorentz tensors, and
  Einstein tensors.
- Tensor species are built upon symmetric monoidal categories.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

/-- The structure of a type of tensors e.g. Lorentz tensors, ordinary tensors
  (vectors and matrices), complex Lorentz tensors. -/
structure TensorSpecies where
  /-- The commutative ring over which we want to consider the tensors to live in,
    usually `ℝ` or `ℂ`. -/
  k : Type
  /-- An instance of `k` as a commutative ring. -/
  k_commRing : CommRing k
  /-- The symmetry group acting on these tensor e.g. the Lorentz group or SL(2,ℂ). -/
  G : Type
  /-- An instance of `G` as a group. -/
  G_group : Group G
  /-- The colors of indices e.g. up or down. -/
  C : Type
  /-- A functor from `C` to `Rep k G` giving our building block representations.
    Equivalently a function `C → Re k G`. -/
  FD : Discrete C ⥤ Rep k G
  /-- A specification of the dimension of each color in C. This will be used for explicit
    evaluation of tensors. -/
  repDim : C → ℕ
  /-- repDim is not zero for any color. This allows casting of `ℕ` to `Fin (S.repDim c)`. -/
  repDim_neZero (c : C) : NeZero (repDim c)
  /-- A basis for each Module, determined by the evaluation map. -/
  basis : (c : C) → Basis (Fin (repDim c)) k (FD.obj (Discrete.mk c)).V
  /-- A map from `C` to `C`. An involution. -/
  τ : C → C
  /-- The condition that `τ` is an involution. -/
  τ_involution : Function.Involutive τ
  /-- The natural transformation describing contraction. -/
  contr : OverColor.Discrete.pairτ FD τ ⟶ 𝟙_ (Discrete C ⥤ Rep k G)
  /-- Contraction is symmetric with respect to duals. -/
  contr_tmul_symm (c : C) (x : FD.obj (Discrete.mk c))
      (y : FD.obj (Discrete.mk (τ c))) :
    (contr.app (Discrete.mk c)).hom (x ⊗ₜ[k] y) = (contr.app (Discrete.mk (τ c))).hom
    (y ⊗ₜ (FD.map (Discrete.eqToHom (τ_involution c).symm)).hom x)
  /-- The natural transformation describing the unit. -/
  unit : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.τPair FD τ
  /-- The unit is symmetric. -/
  unit_symm (c : C) :
    ((unit.app (Discrete.mk c)).hom (1 : k)) =
    ((FD.obj (Discrete.mk (τ (c)))) ◁
      (FD.map (Discrete.eqToHom (τ_involution c)))).hom
    ((β_ (FD.obj (Discrete.mk (τ (τ c)))) (FD.obj (Discrete.mk (τ (c))))).hom.hom
    ((unit.app (Discrete.mk (τ c))).hom (1 : k)))
  /-- Contraction with unit leaves invariant. -/
  contr_unit (c : C) (x : FD.obj (Discrete.mk (c))) :
    (λ_ (FD.obj (Discrete.mk (c)))).hom.hom
    (((contr.app (Discrete.mk c)) ▷ (FD.obj (Discrete.mk (c)))).hom
    ((α_ _ _ (FD.obj (Discrete.mk (c)))).inv.hom
    (x ⊗ₜ[k] (unit.app (Discrete.mk c)).hom (1 : k)))) = x
  /-- The natural transformation describing the metric. -/
  metric : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.pair FD
  /-- On contracting metrics we get back the unit. -/
  contr_metric (c : C) :
    (β_ (FD.obj (Discrete.mk c)) (FD.obj (Discrete.mk (τ c)))).hom.hom
    (((FD.obj (Discrete.mk c)) ◁ (λ_ (FD.obj (Discrete.mk (τ c)))).hom).hom
    (((FD.obj (Discrete.mk c)) ◁ ((contr.app (Discrete.mk c)) ▷
    (FD.obj (Discrete.mk (τ c))))).hom
    (((FD.obj (Discrete.mk c)) ◁ (α_ (FD.obj (Discrete.mk (c)))
      (FD.obj (Discrete.mk (τ c))) (FD.obj (Discrete.mk (τ c)))).inv).hom
    ((α_ (FD.obj (Discrete.mk (c))) (FD.obj (Discrete.mk (c)))
      (FD.obj (Discrete.mk (τ c)) ⊗ FD.obj (Discrete.mk (τ c)))).hom.hom
    ((metric.app (Discrete.mk c)).hom (1 : k) ⊗ₜ[k]
      (metric.app (Discrete.mk (τ c))).hom (1 : k))))))
    = (unit.app (Discrete.mk c)).hom (1 : k)

noncomputable section

namespace TensorSpecies
open OverColor

variable (S : TensorSpecies)

/-- The field `k` of a TensorSpecies has the instance of a commutative ring. -/
instance : CommRing S.k := S.k_commRing

/-- The field `G` of a TensorSpecies has the instance of a group. -/
instance : Group S.G := S.G_group

/-- The field `repDim` of a TensorSpecies is non-zero for all colors. -/
instance (c : S.C) : NeZero (S.repDim c) := S.repDim_neZero c

/-- The lift of the functor `S.F` to functor. -/
def F : Functor (OverColor S.C) (Rep S.k S.G) := ((OverColor.lift).obj S.FD).toFunctor

/- The definition of `F` as a lemma. -/
lemma F_def : F S = ((OverColor.lift).obj S.FD).toFunctor := rfl

/-- The functor `F` is monoidal. -/
instance F_monoidal : Functor.Monoidal S.F :=
  lift.instMonoidalRepObjFunctorDiscreteLaxBraidedFunctor S.FD

/-- The functor `F` is lax-braided. -/
instance F_laxBraided : Functor.LaxBraided S.F :=
  lift.instLaxBraidedRepObjFunctorDiscreteLaxBraidedFunctor S.FD

/-- The functor `F` is braided. -/
instance F_braided : Functor.Braided S.F := Functor.Braided.mk
  (fun X Y => Functor.LaxBraided.braided X Y)

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

/-- Casts an element of the monoidal unit of `Rep S.k S.G` to the field `S.k`. -/
def castToField (v : (↑((𝟙_ (Discrete S.C ⥤ Rep S.k S.G)).obj { as := c }).V)) : S.k := v

/-- Casts an element of `(S.F.obj (OverColor.mk c)).V` for `c` a map from `Fin 0` to an
  element of the field. -/
def castFin0ToField {c : Fin 0 → S.C} : (S.F.obj (OverColor.mk c)).V →ₗ[S.k] S.k :=
  (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap

lemma castFin0ToField_tprod {c : Fin 0 → S.C}
    (x : (i : Fin 0) → S.FD.obj (Discrete.mk (c i))) :
    castFin0ToField S (PiTensorProduct.tprod S.k x) = 1 := by
  simp only [castFin0ToField, mk_hom, Functor.id_obj, LinearEquiv.coe_coe]
  erw [PiTensorProduct.isEmptyEquiv_apply_tprod]

/-!

## Evalutation of indices.

-/

/-- The isomorphism of objects in `Rep S.k S.G` given an `i` in `Fin n.succ`
  allowing us to undertake evaluation. -/
def evalIso {n : ℕ} (c : Fin n.succ → S.C)
    (i : Fin n.succ) : S.F.obj (OverColor.mk c) ≅ (S.FD.obj (Discrete.mk (c i))) ⊗
      (OverColor.lift.obj S.FD).obj (OverColor.mk (c ∘ i.succAbove)) :=
  (S.F.mapIso (OverColor.equivToIso (HepLean.Fin.finExtractOne i))).trans <|
  (S.F.mapIso (OverColor.mkSum (c ∘ (HepLean.Fin.finExtractOne i).symm))).trans <|
  (Functor.Monoidal.μIso S.F _ _).symm.trans <|
  tensorIso
    ((S.F.mapIso (OverColor.mkIso (by ext x; fin_cases x; rfl))).trans
    (OverColor.forgetLiftApp S.FD (c i))) (S.F.mapIso (OverColor.mkIso (by ext x; simp)))

lemma evalIso_tprod {n : ℕ} {c : Fin n.succ → S.C} (i : Fin n.succ)
    (x : (i : Fin n.succ) → S.FD.obj (Discrete.mk (c i))) :
    (S.evalIso c i).hom.hom (PiTensorProduct.tprod S.k x) =
    x i ⊗ₜ[S.k] (PiTensorProduct.tprod S.k (fun k => x (i.succAbove k))) := by
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, F_def, evalIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom, Action.comp_hom,
    Action.instMonoidalCategory_tensorHom_hom, Functor.id_obj, mk_hom, ModuleCat.hom_comp,
    Function.comp_apply]
  change (((lift.obj S.FD).map (mkIso _).hom).hom ≫
    (forgetLiftApp S.FD (c i)).hom.hom ⊗
    ((lift.obj S.FD).map (mkIso _).hom).hom)
    ((Functor.Monoidal.μIso (lift.obj S.FD).toFunctor
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractOne i).symm) ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractOne i).symm) ∘ Sum.inr))).inv.hom
    (((lift.obj S.FD).map (mkSum (c ∘ ⇑(HepLean.Fin.finExtractOne i).symm)).hom).hom
    (((lift.obj S.FD).map (equivToIso (HepLean.Fin.finExtractOne i)).hom).hom
    ((PiTensorProduct.tprod S.k) _)))) =_
  rw [lift.map_tprod]
  change (((lift.obj S.FD).map (mkIso _).hom).hom ≫
    (forgetLiftApp S.FD (c i)).hom.hom ⊗
    ((lift.obj S.FD).map (mkIso _).hom).hom)
    ((Functor.Monoidal.μIso (lift.obj S.FD).toFunctor
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractOne i).symm) ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractOne i).symm) ∘ Sum.inr))).inv.hom
    (((lift.obj S.FD).map (mkSum (c ∘ ⇑(HepLean.Fin.finExtractOne i).symm)).hom).hom
    (((PiTensorProduct.tprod S.k) _)))) =_
  rw [lift.map_tprod]
  change ((TensorProduct.map (((lift.obj S.FD).map (mkIso _).hom).hom ≫
    (forgetLiftApp S.FD (c i)).hom.hom).hom
    ((lift.obj S.FD).map (mkIso _).hom).hom.hom))
    ((Functor.Monoidal.μIso (lift.obj S.FD).toFunctor
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractOne i).symm) ∘ Sum.inl))
    (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractOne i).symm) ∘ Sum.inr))).inv.hom.hom
    ((((PiTensorProduct.tprod S.k) _)))) =_
  rw [lift.μIso_inv_tprod]
  rw [TensorProduct.map_tmul]
  erw [lift.map_tprod]
  simp only [Nat.succ_eq_add_one, CategoryStruct.comp, Functor.id_obj,
    instMonoidalCategoryStruct_tensorObj_hom, mk_hom, Sum.elim_inl, Function.comp_apply,
    instMonoidalCategoryStruct_tensorObj_left, mkSum_homToEquiv, Equiv.refl_symm,
    LinearMap.coe_comp, Sum.elim_inr]
  congr 1
  · change (forgetLiftApp S.FD (c i)).hom.hom
      (((lift.obj S.FD).map (mkIso _).hom).hom
      ((PiTensorProduct.tprod S.k) _)) = _
    rw [lift.map_tprod]
    rw [forgetLiftApp_hom_hom_apply_eq]
    apply congrArg
    funext i
    match i with
    | (0 : Fin 1) =>
      simp only [mk_hom, Fin.isValue, Function.comp_apply, lift.discreteFunctorMapEqIso,
        eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv,
        LinearEquiv.ofLinear_apply]
      rfl
  · apply congrArg
    funext k
    simp only [lift.discreteFunctorMapEqIso, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
      eqToIso.inv, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv,
      LinearEquiv.ofLinear_apply]
    change (S.FD.map (eqToHom _)).hom
      (x ((HepLean.Fin.finExtractOne i).symm ((Sum.inr k)))) = _
    have h1' {a b : Fin n.succ} (h : a = b) :
      (S.FD.map (eqToHom (by rw [h]))).hom (x a) = x b := by
      subst h
      simp
    refine h1' ?_
    exact HepLean.Fin.finExtractOne_symm_inr_apply i k

/-- The linear map giving the coordinate of a vector with respect to the given basis.
  Important Note: This is not a morphism in the category of representations. In general,
  it cannot be lifted thereto. -/
def evalLinearMap {n : ℕ} {c : Fin n.succ → S.C} (i : Fin n.succ) (e : Fin (S.repDim (c i))) :
    S.FD.obj { as := c i } →ₗ[S.k] S.k where
  toFun := fun v => (S.basis (c i)).repr v e
  map_add' := by simp
  map_smul' := by simp

/-- The evaluation map, used to evaluate indices of tensors.
  Important Note: The evaluation map is in general, not equivariant with respect to
  group actions. It is a morphism in the underlying module category, not the category
  of representations. -/
def evalMap {n : ℕ} {c : Fin n.succ → S.C} (i : Fin n.succ) (e : Fin (S.repDim (c i))) :
    (S.F.obj (OverColor.mk c)).V ⟶ (S.F.obj (OverColor.mk (c ∘ i.succAbove))).V :=
  (S.evalIso c i).hom.hom ≫ (Functor.Monoidal.μIso (Action.forget _ _) _ _).inv
  ≫ ModuleCat.ofHom (TensorProduct.map (S.evalLinearMap i e) LinearMap.id) ≫
  ModuleCat.ofHom (TensorProduct.lid S.k _).toLinearMap

lemma evalMap_tprod {n : ℕ} {c : Fin n.succ → S.C} (i : Fin n.succ) (e : Fin (S.repDim (c i)))
    (x : (i : Fin n.succ) → S.FD.obj (Discrete.mk (c i))) :
    (S.evalMap i e) (PiTensorProduct.tprod S.k x) =
    (((S.basis (c i)).repr (x i) e) : S.k) •
    (PiTensorProduct.tprod S.k
    (fun k => x (i.succAbove k)) : S.F.obj (OverColor.mk (c ∘ i.succAbove))) := by
  rw [evalMap]
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, Action.forget_obj,
    Functor.Monoidal.μIso_inv, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, Action.forget_δ,
    mk_left, Functor.id_obj, mk_hom, Function.comp_apply, Category.id_comp, ModuleCat.hom_comp]
  simp_rw [LinearMap.comp_apply]
  erw [evalIso_tprod]
  change ((TensorProduct.lid S.k ↑((lift.obj S.FD).obj (OverColor.mk (c ∘ i.succAbove))).V))
    (((TensorProduct.map (S.evalLinearMap i e) LinearMap.id))
    ((Functor.Monoidal.μIso (Action.forget (ModuleCat S.k) (MonCat.of S.G)) (S.FD.obj { as := c i })
    ((lift.obj S.FD).obj (OverColor.mk (c ∘ i.succAbove)))).inv
    (x i ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) fun k => x (i.succAbove k)))) = _
  simp only [Nat.succ_eq_add_one, Action.forget_obj, Action.instMonoidalCategory_tensorObj_V,
    Functor.Monoidal.μIso_inv, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, Action.forget_δ,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, mk_left, Functor.id_obj, mk_hom,
    Function.comp_apply, ModuleCat.id_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    TensorProduct.lid_tmul]
  rfl

/-!

## The equivalence turning vecs into tensors

-/

/-- The equivalence between tensors based on `![c]` and vectors in ` S.FD.obj (Discrete.mk c)`. -/
def tensorToVec (c : S.C) : S.F.obj (OverColor.mk ![c]) ≅ S.FD.obj (Discrete.mk c) :=
  OverColor.forgetLiftAppCon S.FD c

lemma tensorToVec_inv_apply_expand (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    (S.tensorToVec c).inv.hom x =
    ((lift.obj S.FD).map (OverColor.mkIso (by
    funext i
    fin_cases i
    rfl)).hom).hom ((OverColor.forgetLiftApp S.FD c).inv.hom x) :=
  forgetLiftAppCon_inv_apply_expand S.FD c x

lemma tensorToVec_naturality_eqToHom (c c1 : S.C) (h : c = c1) :
    (S.tensorToVec c).hom ≫ S.FD.map (Discrete.eqToHom h) =
    S.F.map (OverColor.mkIso (by rw [h])).hom ≫ (S.tensorToVec c1).hom :=
  OverColor.forgetLiftAppCon_naturality_eqToHom S.FD c c1 h

lemma tensorToVec_naturality_eqToHom_apply (c c1 : S.C) (h : c = c1)
    (x : S.F.obj (OverColor.mk ![c])) :
    (S.FD.map (Discrete.eqToHom h)).hom ((S.tensorToVec c).hom.hom x) =
    (S.tensorToVec c1).hom.hom (((S.F.map (OverColor.mkIso (by rw [h])).hom).hom x)) :=
  forgetLiftAppCon_naturality_eqToHom_apply S.FD c c1 h x

end TensorSpecies

end
