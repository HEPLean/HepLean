/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Tensors.TensorSpecies.Basic
/-!

# Basis for tensors in a tensor species

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory


namespace TensorSpecies
open OverColor

variable (S : TensorSpecies)
noncomputable section

/--
 The multi-linear map from `(fun i => S.FD.obj (Discrete.mk (c i)))` to `S.k` giving
 the coordinate with respect to the basis described by `b`.
-/
def coordinateMultiLinearSingle {n : ℕ} (c : Fin n → S.C) (b : Π j, Fin (S.repDim (c j))) :
    MultilinearMap S.k (fun i => S.FD.obj (Discrete.mk (c i))) S.k where
  toFun := fun t => ∏ i, (S.basis (c i)).repr (t i) (b i)
  map_update_add' t i x y := by
    simp only
    cases n
    · exact Fin.elim0 i
    rename_i n d
    rw [Fin.prod_univ_succAbove _ i, Fin.prod_univ_succAbove _ i, Fin.prod_univ_succAbove _ i]
    simp only [Function.update_self, map_add, Finsupp.coe_add, Pi.add_apply]
    have hjx (j : Fin n) : (Function.update t i x (i.succAbove j)) =
      (Function.update t i (x + y) (i.succAbove j)) := by
      rw [Function.update_of_ne, Function.update_of_ne]
      · exact Fin.succAbove_ne i j
      · exact Fin.succAbove_ne i j
    have hjy (j : Fin n) : (Function.update t i y (i.succAbove j)) =
      (Function.update t i (x + y) (i.succAbove j)) := by
      rw [Function.update_of_ne, Function.update_of_ne]
      · exact Fin.succAbove_ne i j
      · exact Fin.succAbove_ne i j
    simp only [add_mul, hjx, hjy]
  map_update_smul' t i x y := by
    simp only [smul_eq_mul]
    cases n
    · exact Fin.elim0 i
    rename_i n d
    rw [Fin.prod_univ_succAbove _ i, Fin.prod_univ_succAbove _ i]
    simp only [Function.update_self, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hjx (j : Fin n) : (Function.update t i y (i.succAbove j)) =
      (Function.update t i (x • y) (i.succAbove j)) := by
      rw [Function.update_of_ne, Function.update_of_ne]
      · exact Fin.succAbove_ne i j
      · exact Fin.succAbove_ne i j
    simp only [mul_assoc, hjx]

/--
 The multi-linear map from `(fun i => S.FD.obj (Discrete.mk (c i)))` to
 `((Π j, Fin (S.repDim (c j))) → S.k)` giving
 the coordinates with respect to the basis defined in `S`.
-/
def coordinateMultiLinear {n : ℕ} (c : Fin n → S.C) :
    MultilinearMap S.k (fun i => S.FD.obj (Discrete.mk (c i)))
    ((Π j, Fin (S.repDim (c j))) → S.k) where
  toFun t := fun b => coordinateMultiLinearSingle S c b t
  map_update_add' t i x y := by
    ext b
    simp only [coordinateMultiLinearSingle, MultilinearMap.map_update_add, MultilinearMap.coe_mk,
      Pi.add_apply]
  map_update_smul' t i x y := by
    ext b
    simp only [coordinateMultiLinearSingle, MultilinearMap.map_update_smul, MultilinearMap.coe_mk,
      smul_eq_mul, Pi.smul_apply]

/-- The linear map from tensors to coordinates. -/
def coordinate {n : ℕ} (c : Fin n → S.C) :
    S.F.obj (OverColor.mk c) →ₗ[S.k] ((Π j, Fin (S.repDim (c j))) → S.k)  :=
  (S.liftTensor (c := c)).toFun (S.coordinateMultiLinear c)

lemma coordinate_tprod {n : ℕ} (c : Fin n → S.C) (x : (i : Fin n) → S.FD.obj (Discrete.mk (c i))) :
    S.coordinate c (PiTensorProduct.tprod S.k x) = S.coordinateMultiLinear c x := by
  simp only [coordinate, liftTensor, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    LinearEquiv.coe_coe, mk_left, Functor.id_obj, mk_hom]
  erw [PiTensorProduct.lift.tprod]

/-- The basis vector of tensors given a `b : Π j, Fin (S.repDim (c j))` . -/
def basisVector {n : ℕ} (c : Fin n → S.C) (b : Π j, Fin (S.repDim (c j))) :
    S.F.obj (OverColor.mk c) :=
  PiTensorProduct.tprod S.k (fun i => S.basis (c i) (b i))

lemma coordinate_basisVector {n : ℕ} (c : Fin n → S.C) (b1 b2 : Π j, Fin (S.repDim (c j))) :
    S.coordinate c (S.basisVector c b1) b2 = if b1 = b2 then 1 else 0 := by
  simp only [basisVector, mk_left, Functor.id_obj, mk_hom]
  erw [coordinate_tprod]
  simp only [coordinateMultiLinear, coordinateMultiLinearSingle, MultilinearMap.coe_mk,
    Basis.repr_self]
  by_cases h : b1 = b2
  · subst h
    simp only [Finsupp.single_eq_same, Finset.prod_const_one, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    rw [funext_iff] at h
    simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Finsupp.single_eq_of_ne hi]

/-- The linear map taking a `((Π j, Fin (S.repDim (c j))) → S.k)` to a tensor, defined
  by summing over basis. -/
def fromCoordinates {n : ℕ} (c : Fin n → S.C) :
    ((Π j, Fin (S.repDim (c j))) → S.k) →ₗ[S.k] S.F.obj (OverColor.mk c) where
  toFun fb := ∑ b, fb b • S.basisVector c b
  map_add' fb gb := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' fb r := by
    simp [smul_smul, Finset.smul_sum]

lemma coordinate_fromCoordinate_left_inv  {n : ℕ} (c : Fin n → S.C) :
    Function.LeftInverse (S.fromCoordinates c) (S.coordinate c) := by
  intro x
  refine PiTensorProduct.induction_on' x (fun r b => ?_) <| fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.hom_comp,
        Function.comp_apply, hy]
  simp only [mk_left, Functor.id_obj, mk_hom, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul]
  apply congr_arg
  erw [coordinate_tprod]
  simp only [fromCoordinates, basisVector, mk_left, Functor.id_obj, mk_hom, coordinateMultiLinear,
    coordinateMultiLinearSingle, MultilinearMap.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 (x : (j : Fin n) → Fin (S.repDim (c j))) :
      (∏ i : Fin n, ((S.basis (c i)).repr (b i)) (x i)) •
      ((PiTensorProduct.tprod S.k) fun i => (S.basis (c i) (x i))  )
      = (PiTensorProduct.tprod S.k) fun i => (((S.basis (c i)).repr (b i)) (x i))
        • (S.basis (c i) (x i)) :=
          Eq.symm
            (MultilinearMap.map_smul_univ (PiTensorProduct.tprod S.k)
              (fun i => ((S.basis (c i)).repr (b i)) (x i)) fun i => (S.basis (c i)) (x i))
  conv_lhs =>
    enter [2, x]
    erw [h1]
  trans (PiTensorProduct.tprod S.k) fun i =>
    ∑ x, ((S.basis (c i)).repr (b i)) x • (S.basis (c i)) x
  · exact (MultilinearMap.map_sum (PiTensorProduct.tprod S.k) fun i j =>
      ((S.basis (c i)).repr (b i)) j • (S.basis (c i)) j).symm
  congr
  funext i
  simp only [mk_hom]
  exact Basis.sum_equivFun (S.basis (c i)) (b i)

lemma coordinate_fromCoordinate_right_inv  {n : ℕ} (c : Fin n → S.C) :
    Function.RightInverse (S.fromCoordinates c) (S.coordinate c) := by
  intro x
  simp only [fromCoordinates, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  funext fb
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change  ∑ gb : (j : Fin n) → Fin (S.repDim (c j)), x gb *
    ((S.coordinate c) (S.basisVector c gb) fb)  = _
  conv_lhs =>
    enter [2, x]
    rw [coordinate_basisVector]
  simp


/-- The basis of tensors. -/
def tensorBasis {n : ℕ} (c : Fin n → S.C) :
    Basis (Π j, Fin (S.repDim (c j))) S.k (S.F.obj (OverColor.mk c)) where
  repr := (LinearEquiv.mk (S.coordinate c) (S.fromCoordinates c)
    (S.coordinate_fromCoordinate_left_inv c) (S.coordinate_fromCoordinate_right_inv c)).trans
    (Finsupp.linearEquivFunOnFinite S.k S.k ((j : Fin n) → Fin (S.repDim (c j)))).symm

lemma tensorBasis_eq_basisVector {n : ℕ} (c : Fin n → S.C) (b : Π j, Fin (S.repDim (c j))) :
    S.tensorBasis c b = S.basisVector c b := by
  simp [tensorBasis]
  change (S.fromCoordinates _) _ = _
  simp only [fromCoordinates, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' hb
    simp_all only [Finset.mem_univ, ne_eq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul,
      implies_true]
  · simp

end


namespace TensorBasis

variable {S : TensorSpecies}

/-- The equivalence between the indexing set of basis of Lorentz tensors
  induced by an equivalence on indices. -/
def congr {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ  : Fin n ≃ Fin m)
    (h :  ∀ i, c i = c1 (σ i)) :
    (Π j, Fin (S.repDim (c1 j))) ≃ Π j, Fin (S.repDim (c j)) where
  toFun b := fun i => Fin.cast (congrArg S.repDim (h i).symm) (b (σ i))
  invFun b := fun i => Fin.cast (congrArg S.repDim (by simp [h])) (b (σ.symm i))
  left_inv b := by
    funext i
    ext
    simp only [Fin.cast_trans, Fin.coe_cast]
    congr
    · exact Equiv.apply_symm_apply σ i
    · exact Equiv.apply_symm_apply σ i
  right_inv b := by
    funext i
    ext
    simp only [Fin.cast_trans, Fin.coe_cast]
    congr
    · exact Equiv.symm_apply_apply σ i
    · exact Equiv.symm_apply_apply σ i

lemma map_tensorBasis {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)}
    (b : Π j, Fin (S.repDim (c j))) :
    (S.F.map σ).hom.hom (S.tensorBasis c b) =
    S.tensorBasis c1 ((congr (OverColor.Hom.toEquiv σ)
    (OverColor.Hom.toEquiv_comp_apply σ)).symm b) := by
  rw [tensorBasis_eq_basisVector, basisVector]
  simp only [F_def]
  erw [lift.objMap'_tprod]
  erw [tensorBasis_eq_basisVector]
  simp only [basisVector, Functor.id_obj, mk_hom]
  congr
  funext i
  simp [lift.discreteFunctorMapEqIso, congr]
  rw [FD_map_basis]
  exact OverColor.Hom.toEquiv_symm_apply σ i

end TensorBasis

end TensorSpecies
