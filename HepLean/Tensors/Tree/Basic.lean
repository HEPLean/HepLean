/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Iso
import HepLean.Tensors.OverColor.Discrete
import HepLean.Tensors.OverColor.Lift
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import LLMLean
/-!

## Tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

/-- The sturcture of a type of tensors e.g. Lorentz tensors, Einstien tensors,
  complex Lorentz tensors.
  Note: This structure is not fully defined yet. -/
structure TensorStruct where
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

noncomputable section

namespace TensorStruct

variable (S : TensorStruct)

instance : CommRing S.k := S.k_commRing

instance : Group S.G := S.G_group

/-- The lift of the functor `S.F` to a monoidal functor. -/
def F : MonoidalFunctor (OverColor S.C) (Rep S.k S.G) := (OverColor.lift).obj S.FDiscrete

/-
def metric (c : S.C) : S.F.obj (OverColor.mk ![c, c]) :=
  (OverColor.Discrete.pairIso S.FDiscrete c).hom.hom <|
  (S.metricNat.app (Discrete.mk c)).hom (1 : S.k)
-/

/-- The isomorphism between the image of a map `Fin 1 ⊕ Fin 1 → S.C` contructed by `finExtractTwo`
 under `S.F.obj`, and an object in the image of `OverColor.Discrete.pairτ S.FDiscrete`. -/
def contrFin1Fin1 {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)) ≅
    (OverColor.Discrete.pairτ S.FDiscrete S.τ).obj { as := c i } := by
  apply (S.F.mapIso (OverColor.mkSum (((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)))).trans
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
  simp [contrFin1Fin1]
  change (S.F.map (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    ((S.F.map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
      ((S.F.μ (OverColor.mk fun x => c i) (OverColor.mk fun x => S.τ (c i))).hom
        ((((OverColor.forgetLiftApp S.FDiscrete (c i)).inv.hom x) ⊗ₜ[S.k]
        ((OverColor.forgetLiftApp S.FDiscrete (S.τ (c i))).inv.hom y))))) = _
  simp [OverColor.forgetLiftApp]
  erw [OverColor.forgetLiftAppV_symm_apply, OverColor.forgetLiftAppV_symm_apply S.FDiscrete (S.τ (c i))]
  change  ((OverColor.lift.obj S.FDiscrete).map (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    (((OverColor.lift.obj S.FDiscrete).map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
      (((OverColor.lift.obj S.FDiscrete).μ (OverColor.mk fun x => c i) (OverColor.mk fun x => S.τ (c i))).hom
        (((PiTensorProduct.tprod S.k) fun x_1 => x) ⊗ₜ[S.k] (PiTensorProduct.tprod S.k) fun x => y))) = _
  rw [OverColor.lift.obj_μ_tprod_tmul S.FDiscrete]
  change ((OverColor.lift.obj S.FDiscrete).map (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    (((OverColor.lift.obj S.FDiscrete).map ((OverColor.mkIso _).hom ⊗ (OverColor.mkIso _).hom)).hom
      ((PiTensorProduct.tprod S.k) _))  = _
  rw [OverColor.lift.map_tprod S.FDiscrete]
  change  ((OverColor.lift.obj S.FDiscrete).map (OverColor.mkSum ((c ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl)).inv).hom
    ((PiTensorProduct.tprod S.k _)) = _
  rw [OverColor.lift.map_tprod S.FDiscrete]
  apply congrArg
  funext r
  match r with
  | Sum.inl 0 =>
    simp [OverColor.lift.discreteSumEquiv, HepLean.PiTensorProduct.elimPureTensor]
    simp [OverColor.lift.discreteFunctorMapEqIso]
    rfl
  | Sum.inr 0 =>
    simp [OverColor.lift.discreteFunctorMapEqIso, OverColor.lift.discreteSumEquiv, HepLean.PiTensorProduct.elimPureTensor]
    rfl


lemma contrFin1Fin1_inv_tmul' {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i))
    (x :  ↑(((Action.functorCategoryEquivalence (ModuleCat S.k) (MonCat.of S.G)).symm.inverse.obj
        (S.FDiscrete.obj { as := c ( i) })).obj
    PUnit.unit))
    (y : ↑(((Action.functorCategoryEquivalence (ModuleCat S.k) (MonCat.of S.G)).symm.inverse.obj
        ((Discrete.functor (Discrete.mk ∘ S.τ) ⋙ S.FDiscrete).obj { as := c ( i) })).obj
    PUnit.unit)) :
    (S.contrFin1Fin1 c i j h).inv.hom (x ⊗ₜ[S.k] y) =
    PiTensorProduct.tprod S.k (fun k =>
    match k with | Sum.inl 0 => x | Sum.inr 0 => (S.FDiscrete.map
    (eqToHom (by simp [h]))).hom y) := by
  exact contrFin1Fin1_inv_tmul S c i j h x y

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

open OverColor
lemma perm_contr_cond {n : ℕ} {c : Fin n.succ.succ.succ → S.C} {c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    (h : c1 (i.succAbove j) = S.τ (c1 i)) (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    c (Fin.succAbove ((Hom.toEquiv σ).symm i) ((Hom.toEquiv (extractOne i σ)).symm j)) =
    S.τ (c ((Hom.toEquiv σ).symm i)) := by
  have h1 := Hom.toEquiv_comp_apply σ
  simp at h1
  rw [h1, h1]
  simp
  rw [← h]
  congr
  simp [HepLean.Fin.finExtractOnePerm, HepLean.Fin.finExtractOnPermHom]
  erw [Equiv.apply_symm_apply]
  rw [HepLean.Fin.succsAbove_predAboveI]
  erw [Equiv.apply_symm_apply]
  simp
  erw [Equiv.apply_eq_iff_eq]
  exact (Fin.succAbove_ne i j).symm

lemma contrIso_comm_aux_1 {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    ((S.F.map σ).hom ≫ (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom) ≫
        (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom =
     (S.F.map (equivToIso (HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
     ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j))).hom).hom  ≫ (S.F.map
     (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)).symm)).hom).hom
     ≫ (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)).hom
     := by
  ext X
  change ((S.F.map σ) ≫ (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom) ≫ (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom)).hom X = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [extractTwo_finExtractTwo]
  simp only [Nat.succ_eq_add_one, extractOne_homToEquiv, Functor.map_comp, Action.comp_hom,
    ModuleCat.coe_comp, Function.comp_apply]
  rfl

lemma contrIso_comm_aux_2 {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)).hom ≫
    (S.F.μIso (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom  =
    (S.F.μIso _ _).inv.hom ≫ (S.F.map (extractTwoAux' i j σ) ⊗ S.F.map (extractTwoAux i j σ)).hom
     := by
  have h1 : (S.F.map (extractTwoAux' i j σ ⊗ extractTwoAux i j σ)) ≫
    (S.F.μIso (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
    (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv  =
    (S.F.μIso _ _).inv ≫ (S.F.map (extractTwoAux' i j σ) ⊗ S.F.map (extractTwoAux i j σ)) := by
    erw [CategoryTheory.IsIso.comp_inv_eq, CategoryTheory.Category.assoc]
    erw [CategoryTheory.IsIso.eq_inv_comp ]
    exact Eq.symm
        (LaxMonoidalFunctor.μ_natural S.F.toLaxMonoidalFunctor (extractTwoAux' i j σ)
          (extractTwoAux i j σ))
  exact congrArg (λ f => Action.Hom.hom f) h1

lemma contrIso_comm_aux_3 {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
      ((Action.functorCategoryEquivalence (ModuleCat S.k) (MonCat.of S.G)).symm.inverse.map
                  (S.F.map (extractTwoAux i j σ))).app
              PUnit.unit ≫
            (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom).hom
    = (S.F.map (mkIso (contrIso.proof_1 S c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j) )).hom).hom  ≫
    (S.F.map (extractTwo i j σ)).hom := by
  change  (S.F.map (extractTwoAux i j σ)).hom ≫ _ = _
  have h1 : (S.F.map (extractTwoAux i j σ)) ≫ (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom) =
  (S.F.map (mkIso (contrIso.proof_1 S c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j) )).hom) ≫ (S.F.map (extractTwo i j σ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg
    rfl
  exact congrArg (λ f => Action.Hom.hom f) h1

lemma contrFin1Fin1_naturality {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ} (h : c1 (i.succAbove j) = S.τ (c1 i))
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map (extractTwoAux' i j σ)).hom ≫ (S.contrFin1Fin1 c1 i j h).hom.hom
    = (S.contrFin1Fin1 c ((Hom.toEquiv σ).symm i)
      ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
      (perm_contr_cond S h σ)).hom.hom

    ≫ ((Discrete.pairτ S.FDiscrete S.τ).map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i)
      : (Discrete.mk (c ((Hom.toEquiv σ).symm i))) ⟶ (Discrete.mk (c1 i)) )).hom
    := by
  have h1 : (S.F.map (extractTwoAux' i j σ)) ≫ (S.contrFin1Fin1 c1 i j h).hom
    = (S.contrFin1Fin1 c ((Hom.toEquiv σ).symm i)
      ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
      (perm_contr_cond S h σ)).hom

    ≫ ((Discrete.pairτ S.FDiscrete S.τ).map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i)
      : (Discrete.mk (c ((Hom.toEquiv σ).symm i))) ⟶ (Discrete.mk (c1 i)) )) := by
    erw [← CategoryTheory.Iso.eq_comp_inv ]
    rw [CategoryTheory.Category.assoc]
    erw [← CategoryTheory.Iso.inv_comp_eq ]
    ext1
    apply TensorProduct.ext'
    intro x  y
    simp only [Nat.succ_eq_add_one, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, CategoryStruct.comp,
      extractOne_homToEquiv, Action.Hom.comp_hom, LinearMap.coe_comp]

    trans (S.F.map (extractTwoAux' i j σ)).hom (PiTensorProduct.tprod S.k (fun k =>
      match k with | Sum.inl 0 => x | Sum.inr 0 => (S.FDiscrete.map
      (eqToHom (by simp; erw [perm_contr_cond S h σ]))).hom y) )
    · apply congrArg
      have h1' {α :Type} {a b c d : α} (hab : a= b) (hcd : c =d ) (h : a = d) : b = c := by
          rw [← hab,  hcd]
          exact h
      have h1 := S.contrFin1Fin1_inv_tmul c ((Hom.toEquiv σ).symm i)
          ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
          (perm_contr_cond S h σ ) x y
      refine h1' ?_ ?_ h1
      congr
      apply congrArg
      funext x
      match x with
      | Sum.inl 0 => rfl
      | Sum.inr 0 => rfl
    change _ = (S.contrFin1Fin1 c1 i j h).inv.hom
      ((S.FDiscrete.map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i))).hom x ⊗ₜ[S.k]
      (S.FDiscrete.map (Discrete.eqToHom (congrArg S.τ (Hom.toEquiv_comp_inv_apply σ i)))).hom y)
    rw [contrFin1Fin1_inv_tmul]
    change  ((lift.obj S.FDiscrete).map (extractTwoAux' i j σ)).hom _ = _
    rw [lift.map_tprod]
    apply congrArg
    funext i
    match i with
    | Sum.inl 0 => rfl
    | Sum.inr 0 =>
      simp [lift.discreteFunctorMapEqIso]
      change  ((S.FDiscrete.map (eqToHom _)) ≫ S.FDiscrete.map (eqToHom _)).hom y =  ((S.FDiscrete.map (eqToHom _)) ≫ S.FDiscrete.map (eqToHom _)).hom y
      rw [← Functor.map_comp, ← Functor.map_comp]
      simp only [Fin.isValue, Nat.succ_eq_add_one, Discrete.functor_obj_eq_as, Function.comp_apply,
        eqToHom_trans]
  exact congrArg (λ f => Action.Hom.hom f) h1

def contrIsoComm  {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}

    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :=
     (((Discrete.pairτ S.FDiscrete S.τ).map (Discrete.eqToHom (Hom.toEquiv_comp_inv_apply σ i)
      : (Discrete.mk (c ((Hom.toEquiv σ).symm i))) ⟶ (Discrete.mk (c1 i)) )) ⊗ (S.F.map (extractTwo i j σ)))

lemma contrIso_comm_aux_5 {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ} (h : c1 (i.succAbove j) = S.τ (c1 i))
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (S.F.map (extractTwoAux' i j σ) ⊗ S.F.map (extractTwoAux i j σ)).hom ≫
    ((S.contrFin1Fin1 c1 i j h).hom.hom ⊗ (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom).hom)
    = ((S.contrFin1Fin1 c  ((Hom.toEquiv σ).symm i)
      ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
      (perm_contr_cond S h σ)).hom.hom ⊗ (S.F.map (mkIso (contrIso.proof_1 S c ((Hom.toEquiv σ).symm i)
    ((HepLean.Fin.finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j) )).hom).hom)
    ≫ (S.contrIsoComm σ).hom
     := by
  erw [← CategoryTheory.MonoidalCategory.tensor_comp (f₁ := (S.F.map (extractTwoAux' i j σ)).hom)]
  rw [contrIso_comm_aux_3 S σ]
  rw [contrFin1Fin1_naturality S h σ]
  simp [contrIsoComm]


lemma contrIso_hom_hom {n : ℕ} {c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    {h : c1 (i.succAbove j) = S.τ (c1 i)} :
 (S.contrIso c1 i j h).hom.hom =
  (S.F.map (equivToIso (HepLean.Fin.finExtractTwo i j)).hom).hom ≫
      (S.F.map (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom).hom ≫
        (S.F.μIso (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inl))
                (OverColor.mk ((c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm) ∘ Sum.inr))).inv.hom ≫
          ((S.contrFin1Fin1 c1 i j h).hom.hom ⊗ (S.F.map (mkIso (contrIso.proof_1 S c1 i j)).hom).hom)
   := by
  rw [contrIso]
  simp  [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, Action.comp_hom,
    extractOne_homToEquiv, Action.instMonoidalCategory_tensorHom_hom]

open OverColor in
lemma contrIso_comm_map {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    {h : c1 (i.succAbove j) = S.τ (c1 i)}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
  (S.F.map σ) ≫ (S.contrIso c1 i j h).hom =
  (S.contrIso c ((OverColor.Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j) (S.perm_contr_cond h σ)).hom  ≫
    contrIsoComm S σ  := by
  ext1
  simp only [Nat.succ_eq_add_one, Action.instMonoidalCategory_tensorObj_V, Action.comp_hom,
    extractOne_homToEquiv, Action.instMonoidalCategory_tensorHom_hom]
  rw [contrIso_hom_hom]
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc  ]
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

/--
`contrMap` is a function that takes a natural number `n`, a function `c` from
`Fin n.succ.succ` to `S.C`, an index `i` of type `Fin n.succ.succ`, an index `j` of type
`Fin n.succ`, and a proof `h` that `c (i.succAbove j) = S.τ (c i)`. It returns a morphism
corresponding to the contraction of the `i`th index with the `i.succAbove j` index.
--/
def contrMap {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ⟶
    (OverColor.lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (S.contrIso c i j h).hom ≫
  (tensorHom (S.contr.app (Discrete.mk (c i))) (𝟙 _)) ≫
  (MonoidalCategory.leftUnitor _).hom

lemma contrMap_naturality {n : ℕ} {c c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ} {h : c1 (i.succAbove j) = S.τ (c1 i)}
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
  have h1 : 𝟙_ (Rep S.k S.G) ◁ S.F.map (extractTwo i j σ) = 𝟙 _ ⊗ S.F.map (extractTwo i j σ)  := by
    rfl
  rw [h1, ← tensor_comp]
  erw [CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]
  erw [CategoryTheory.Category.comp_id]
  rw [S.contr.naturality]
  simp only [Nat.succ_eq_add_one, extractOne_homToEquiv, Monoidal.tensorUnit_obj,
    Monoidal.tensorUnit_map, Category.comp_id]




end TensorStruct

/-- A syntax tree for tensor expressions. -/
inductive TensorTree (S : TensorStruct) : ∀ {n : ℕ}, (Fin n → S.C) → Type where
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

variable {S : TensorStruct} {n : ℕ} {c : Fin n → S.C} (T : TensorTree S c)

open MonoidalCategory
open TensorProduct

/-- The node `twoNode` of a tensor tree, with all arguments explicit. -/
abbrev twoNodeE (S : TensorStruct) (c1 c2 : S.C)
    (v : (S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)).V) :
    TensorTree S ![c1, c2] := twoNode v

/-- The node `constTwoNodeE` of a tensor tree, with all arguments explicit. -/
abbrev constTwoNodeE (S : TensorStruct) (c1 c2 : S.C)
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)) :
    TensorTree S ![c1, c2] := constTwoNode v

/-- The node `constThreeNodeE` of a tensor tree, with all arguments explicit. -/
abbrev constThreeNodeE (S : TensorStruct) (c1 c2 c3 : S.C)
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
lemma tensoreNode_tensor {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    (tensorNode T).tensor = T := rfl

@[simp]
lemma constTwoNode_tensor {c1 c2 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FDiscrete.obj (Discrete.mk c1) ⊗ S.FDiscrete.obj (Discrete.mk c2)) :
    (constTwoNode v).tensor = (OverColor.Discrete.pairIsoSep S.FDiscrete).hom.hom (v.hom (1 : S.k)) :=
  rfl

lemma prod_tensor {c1 : Fin n → S.C} {c2 : Fin m → S.C} (t1 : TensorTree S c1) (t2 : TensorTree S c2) :
    (prod t1 t2).tensor = (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor))  := rfl

lemma add_tensor (t1 t2 : TensorTree S c) : (add t1 t2).tensor = t1.tensor + t2.tensor := rfl

lemma perm_tensor (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
    (perm σ t).tensor = (S.F.map σ).hom t.tensor := rfl

lemma contr_tensor {n : ℕ} {c : Fin n.succ.succ → S.C}  {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = S.τ (c i)}
    (t : TensorTree S c) : (contr i j h t).tensor = (S.contrMap c i j h).hom t.tensor := rfl

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
    {T1  T1' : TensorTree S c} { T2 : TensorTree S c1}
    (h : T1.tensor = T1'.tensor) :
    (prod T1 T2).tensor = (prod T1' T2).tensor := by
  simp [prod_tensor]
  rw [h]

lemma prod_tensor_eq_snd {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {T1 : TensorTree S c} {T2 T2' : TensorTree S c1}
    (h : T2.tensor = T2'.tensor) :
    (prod T1 T2).tensor = (prod T1 T2').tensor := by
  simp [prod_tensor]
  rw [h]

/-!

## Negation lemmas

We define the simp lemmas here so that negation is always moved to the top of the tree.
-/

@[simp]
lemma neg_neg (t : TensorTree S c) : (neg (neg t)).tensor = t.tensor := by
  simp only [neg_tensor, _root_.neg_neg]

@[simp]
lemma neg_fst_prod  {c1 : Fin n → S.C} {c2 : Fin m → S.C} (T1 : TensorTree S c1)
    (T2 : TensorTree S c2) :
    (prod (neg T1) T2).tensor = (neg (prod T1 T2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, neg_tensor, neg_tmul, map_neg]

@[simp]
lemma neg_snd_prod  {c1 : Fin n → S.C} {c2 : Fin m → S.C} (T1 : TensorTree S c1)
    (T2 : TensorTree S c2) :
    (prod T1 (neg T2)).tensor = (neg (prod T1 T2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, neg_tensor, tmul_neg, map_neg]

@[simp]
lemma neg_contr {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = S.τ (c i)}
    (t : TensorTree S c) : (contr i j h (neg t)).tensor = (neg (contr i j h t)).tensor := by
  simp only [Nat.succ_eq_add_one, contr_tensor, neg_tensor, map_neg]

lemma neg_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
    (perm σ (neg t)).tensor = (neg (perm σ t)).tensor := by
  simp only [perm_tensor, neg_tensor, map_neg]

/-!

## Permutation lemmas

-/


open OverColor

lemma perm_contr {n : ℕ} {c : Fin n.succ.succ.succ → S.C} {c1 : Fin n.succ.succ.succ → S.C}
    {i : Fin n.succ.succ.succ} {j : Fin n.succ.succ}
    {h : c1 (i.succAbove j) = S.τ (c1 i)} (t : TensorTree S c)
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) :
    (contr i j h (perm σ t)).tensor
    = (perm (extractTwo i j σ) (contr ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j) (S.perm_contr_cond h σ) t)).tensor := by
  rw [contr_tensor, perm_tensor, perm_tensor]
  change ((S.F.map σ) ≫ S.contrMap c1 i j h).hom t.tensor = _
  rw [S.contrMap_naturality σ]
  rfl

end

end TensorTree

end
