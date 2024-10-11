/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
import HepLean.Tensors.OverColor.Functors
import HepLean.Tensors.ComplexLorentz.ColorFun
import HepLean.Mathematics.PiTensorProduct
/-!

## The contraction monoidal natural transformation

-/

namespace Fermion

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace pairwiseRepFun

/-- Given an object `c : OverColor Color` the representation defined by
  `⨂[R] x, colorToRep (c.hom x) ⊗[R] colorToRep (τ (c.hom x))`. -/
def obj' (c : OverColor Color) : Rep ℂ SL(2, ℂ) := Rep.of {
  toFun := fun M => PiTensorProduct.map (fun x =>
    TensorProduct.map ((colorToRep (c.hom x)).ρ M) ((colorToRep (τ (c.hom x))).ρ M)),
  map_one' := by
    simp
  map_mul' := fun x y => by
    simp only [Functor.id_obj, _root_.map_mul]
    ext x' : 2
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.mul_apply]
    apply congrArg
    funext i
    change _ = (TensorProduct.map _ _ ∘ₗ TensorProduct.map _ _) (x' i)
    rw [← TensorProduct.map_comp]
    rfl}

/-- Given a morphism in `OverColor Color` the corresopnding linear equivalence between `obj' _`
  induced by reindexing. -/
def mapToLinearEquiv' {f g : OverColor Color} (m : f ⟶ g) : (obj' f).V ≃ₗ[ℂ] (obj' g).V :=
  (PiTensorProduct.reindex ℂ (fun x => (colorToRep (f.hom x)).V ⊗[ℂ] (colorToRep (τ (f.hom x))).V)
  (OverColor.Hom.toEquiv m)).trans
  (PiTensorProduct.congr (fun i =>
    TensorProduct.congr (colorToRepCongr (OverColor.Hom.toEquiv_symm_apply m i))
    ((colorToRepCongr (congrArg τ (OverColor.Hom.toEquiv_symm_apply m i))))))

lemma mapToLinearEquiv'_tprod {f g : OverColor Color} (m : f ⟶ g)
    (x : (i : f.left) → (colorToRep (f.hom i)).V ⊗[ℂ] (colorToRep (τ (f.hom i))).V) :
    mapToLinearEquiv' m (PiTensorProduct.tprod ℂ x) =
    PiTensorProduct.tprod ℂ fun i =>
    (TensorProduct.congr (colorToRepCongr (OverColor.Hom.toEquiv_symm_apply m i))
    (colorToRepCongr (mapToLinearEquiv'.proof_4 m i))) (x ((OverColor.Hom.toEquiv m).symm i)) := by
  simp [mapToLinearEquiv']
  change (PiTensorProduct.congr fun i => TensorProduct.congr (colorToRepCongr _)
    (colorToRepCongr _)) ((PiTensorProduct.reindex ℂ
    (fun x => ↑(colorToRep (f.hom x)).V ⊗[ℂ] ↑(colorToRep (τ (f.hom x))).V)
    (OverColor.Hom.toEquiv m)) ((PiTensorProduct.tprod ℂ) x)) = _
  rw [PiTensorProduct.reindex_tprod]
  erw [PiTensorProduct.congr_tprod]
  rfl

end pairwiseRepFun

/-

def contrPairPairwiseRep (c : OverColor Color) :
    (colorFunMon.obj c) ⊗ colorFunMon.obj ((OverColor.map τ).obj c) ⟶
    pairwiseRep c where
  hom := TensorProduct.lift (PiTensorProduct.map₂ (fun x =>
      TensorProduct.mk ℂ (colorToRep (c.hom x)).V (colorToRep (τ (c.hom x))).V))
  comm M := by
    refine HepLean.PiTensorProduct.induction_tmul (fun x y => ?_)
    simp only [Functor.id_obj, CategoryStruct.comp, Action.instMonoidalCategory_tensorObj_V,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, Action.tensor_ρ', LinearMap.coe_comp,
      Function.comp_apply]
    change (TensorProduct.lift
      (PiTensorProduct.map₂ fun x => TensorProduct.mk ℂ ↑(colorToRep (c.hom x)).V
      ↑(colorToRep (τ (c.hom x))).V))
      ((TensorProduct.map _ _)
      ((PiTensorProduct.tprod ℂ) x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) y)) = _
    rw [TensorProduct.map_tmul]
    erw [colorFun.obj_ρ_tprod, colorFun.obj_ρ_tprod]
    simp only [Functor.id_obj, lift.tmul]
    erw [PiTensorProduct.map₂_tprod_tprod]
    change _ = ((pairwiseRep c).ρ M)
      ((TensorProduct.lift
        (PiTensorProduct.map₂ fun x => TensorProduct.mk ℂ ↑(colorToRep (c.hom x)).V
        ↑(colorToRep (τ (c.hom x))).V))
      ((PiTensorProduct.tprod ℂ) x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) y))
    simp only [mk_apply, Functor.id_obj, lift.tmul]
    rw [PiTensorProduct.map₂_tprod_tprod]
    simp only [pairwiseRep, Functor.id_obj, Rep.coe_of, Rep.of_ρ, MonoidHom.coe_mk, OneHom.coe_mk,
      mk_apply]
    erw [PiTensorProduct.map_tprod]
    rfl
-/
end
end Fermion
