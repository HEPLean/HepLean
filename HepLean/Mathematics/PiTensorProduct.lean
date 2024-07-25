/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.FinsuppVectorSpace
/-!
# Pi Tensor Products

This file contains some proofs regarding Pi tensor products authored by Sophie Morel
in this Mathlib pull-request:

https://github.com/leanprover-community/mathlib4/pull/11156

Once this pull request has being merged, this file will be deleted.

-/

noncomputable section

namespace MultilinearMap

open DirectSum LinearMap BigOperators Function

variable (R : Type*) [CommSemiring R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (κ : ι → Type*) [(i : ι) → DecidableEq (κ i)]

variable {M : (i : ι) → κ i → Type*} {M' : Type*}

variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']

variable [Π i (j : κ i), Module R (M i j)] [Module R M']

variable [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]

theorem fromDirectSum_aux1 (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) {p : Π i, κ i}
    (hp : p ∉ Fintype.piFinset (fun i ↦ (x i).support)) :
    (f p) (fun j ↦ (x j) (p j)) = 0 := by
  simp only [Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  exact (f p).map_coord_zero i hi

theorem fromDirectSum_aux2 (x : Π i, ⨁ (j : κ i), M i j) (i : ι) (p : Π i, κ i)
    (a : ⨁ (j : κ i), M i j) :
    (fun j ↦ (update x i a j) (p j)) = update (fun j ↦ x j (p j)) i (a (p i)) := by
  ext j
  by_cases h : j =i
  · rw [h]; simp only [update_same]
  · simp only [ne_eq, h, not_false_eq_true, update_noteq]

/-- Given a family indexed by `p : Π i : ι, κ i` of multilinear maps on the
`fun i ↦ M i (p i)`, construct a multilinear map on `fun i ↦ ⨁ j : κ i, M i j`.-/
def fromDirectSum (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M') :
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' where
  toFun x := ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i))
  map_add' x i a b := by
    simp only
    rename_i myinst _ _ _ _ _ _ _
    conv_lhs => rw [← Finset.sum_union_eq_right (s₁ := @Fintype.piFinset _ myinst _ _
        (fun j ↦ (update x i a j).support)
        ∪ @Fintype.piFinset _ myinst _ _ (fun j ↦ (update x i b j).support))
        (fun p _ hp ↦ by
          letI := myinst
          exact fromDirectSum_aux1 _ _ f _ hp)]
    rw [Finset.sum_congr rfl (fun p _ ↦ by rw [fromDirectSum_aux2 _ _ _ p (a + b)])]
    erw [Finset.sum_congr rfl (fun p _ ↦ (f p).map_add _ i (a (p i)) (b (p i)))]
    rw [Finset.sum_add_distrib]
    congr 1
    · conv_lhs => rw [← Finset.sum_congr rfl (fun p _ ↦ by rw [← fromDirectSum_aux2 _ _ _ p a]),
                    Finset.sum_congr (Finset.union_assoc _ _ _) (fun _ _ ↦ rfl)]
      rw [Finset.sum_union_eq_left (fun p _ hp ↦ by
        letI := myinst
        exact fromDirectSum_aux1 _ _ f _ hp)]
    · conv_lhs => rw [← Finset.sum_congr rfl (fun p _ ↦ by rw [← fromDirectSum_aux2 _ _ _ p b]),
        Finset.sum_congr (Finset.union_assoc _ _ _) (fun _ _ ↦ rfl),
        Finset.sum_congr (Finset.union_comm _ _) (fun _ _ ↦ rfl),
        Finset.sum_congr (Finset.union_assoc _ _ _) (fun _ _ ↦ rfl)]
      rw [Finset.sum_union_eq_left (fun p _ hp ↦ by
        letI := myinst
        exact fromDirectSum_aux1 _ _ f _ hp)]
  map_smul' x i c a := by
    simp only
    rename_i myinst _ _ _ _ _ _ _
    conv_lhs => rw [← Finset.sum_union_eq_right (s₁ := @Fintype.piFinset _ myinst _ _
      (fun j ↦ (update x i a j).support))
        (fun p _ hp ↦ by
          letI := myinst
          exact fromDirectSum_aux1 _ _ f _ hp),
      Finset.sum_congr rfl (fun p _ ↦ by rw [fromDirectSum_aux2 _ _ _ p _])]
    erw [Finset.sum_congr rfl (fun p _ ↦ (f p).map_smul _ i c (a (p i)))]
    rw [← Finset.smul_sum]
    conv_lhs => rw [← Finset.sum_congr rfl (fun p _ ↦ by rw [← fromDirectSum_aux2 _ _ _ p _]),
      Finset.sum_union_eq_left (fun p _ hp ↦ by
          letI := myinst
          exact fromDirectSum_aux1 _ _ f _ hp)]

@[simp]
theorem fromDirectSum_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) : fromDirectSum R κ f x =
    ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := rfl

/-- The construction `MultilinearMap.fromDirectSum`, as an `R`-linear map.-/
def fromDirectSumₗ : ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') →ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' where
  toFun := fromDirectSum R κ
  map_add' f g := by
    ext x
    simp only [fromDirectSum_apply, Pi.add_apply, MultilinearMap.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp only [fromDirectSum_apply, Pi.smul_apply, MultilinearMap.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem fromDirectSumₗ_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) : fromDirectSumₗ R κ f x =
    ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := rfl

theorem _root_.piFinset_support_lof_sub (p : Π i, κ i) (a : Π i, M i (p i)) :
    Fintype.piFinset (fun i ↦ DFinsupp.support (lof R (κ i) (M i) (p i) (a i))) ⊆ {p} := by
  intro q
  simp only [Fintype.mem_piFinset, ne_eq, Finset.mem_singleton]
  simp_rw [DirectSum.lof_eq_of]
  exact fun hq ↦ funext fun i ↦ Finset.mem_singleton.mp (DirectSum.support_of_subset _ (hq i))

/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ ⨁ j : κ i, M i j`.-/
def fromDirectSumEquiv : ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' := by
  refine LinearEquiv.ofLinear (fromDirectSumₗ R κ) (LinearMap.pi
    (fun p ↦ MultilinearMap.compLinearMapₗ (fun i ↦ DirectSum.lof R (κ i) _ (p i)))) ?_ ?_
  · ext f x
    simp only [coe_comp, Function.comp_apply, fromDirectSumₗ_apply, pi_apply,
      MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply, id_coe, id_eq]
    change _ = f (fun i ↦ x i)
    rw [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (fun j ↦ M i j) (x i)))]
    rw [MultilinearMap.map_sum_finset]
    sorry
  · ext f p a
    simp only [coe_comp, Function.comp_apply, LinearMap.pi_apply, compLinearMapₗ_apply,
      compLinearMap_apply, fromDirectSumₗ_apply, id_coe, id_eq]
    rw [Finset.sum_subset (piFinset_support_lof_sub R κ p a)]
    · rw [Finset.sum_singleton]
      simp only [lof_apply]
    · simp only [Finset.mem_singleton, Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq,
        not_forall, not_not, forall_exists_index, forall_eq, lof_apply]
      intro i hi
      exact (f p).map_coord_zero i hi

@[simp]
theorem fromDirectSumEquiv_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) : fromDirectSumEquiv R κ f x =
    ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := rfl

@[simp]
theorem fromDirectSumEquiv_symm_apply (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : Π i, κ i) : (fromDirectSumEquiv R κ).symm f p =
    f.compLinearMap (fun i ↦ DirectSum.lof R (κ i) _ (p i)) := rfl

end MultilinearMap

namespace PiTensorProduct

open PiTensorProduct DirectSum LinearMap

open scoped TensorProduct

variable (R : Type*) [CommSemiring R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {κ : ι → Type*} [(i : ι) → DecidableEq (κ i)]

variable (M : (i : ι) → κ i → Type*) (M' : Type*)

variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']

variable [Π i (j : κ i), Module R (M i j)] [Module R M']

variable [Π i (j : κ i) (x : M i j),  Decidable (x ≠ 0)]

/-- The linear equivalence `⨂[R] i, (⨁ j : κ i, M i j) ≃ ⨁ p : (i : ι) → κ i, ⨂[R] i, M i (p i)`,
 i.e. "tensor product distributes over direct sum". -/
protected def directSum :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) := by
  refine LinearEquiv.ofLinear (R := R) (R₂ := R) ?toFun ?invFun ?left ?right
  · exact lift (MultilinearMap.fromDirectSumEquiv R (M := M)
      (fun p ↦ (DirectSum.lof R _ _ p).compMultilinearMap (PiTensorProduct.tprod R)))
  · exact DirectSum.toModule R _ _ (fun p ↦ lift (LinearMap.compMultilinearMap
      (PiTensorProduct.map (fun i ↦ DirectSum.lof R _ _ (p i))) (tprod R)))
  · ext p x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, toModule_lof, lift.tprod,
      map_tprod, MultilinearMap.fromDirectSumEquiv_apply, id_comp]
    rw [Finset.sum_subset (piFinset_support_lof_sub R κ p x)]
    · rw [Finset.sum_singleton]
      simp only [lof_apply]
    · simp only [Finset.mem_singleton, Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq,
        not_forall, not_not, forall_exists_index, forall_eq, lof_apply]
      intro i hi
      rw [(tprod R).map_coord_zero i hi, LinearMap.map_zero]
  · ext x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, lift.tprod,
      MultilinearMap.fromDirectSumEquiv_apply, map_sum, toModule_lof, map_tprod, id_coe, id_eq]
    change _ = tprod R (fun i ↦ x i)
    rw [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (fun j ↦ M i j) (x i)))]
    rw [MultilinearMap.map_sum_finset]
    sorry

end PiTensorProduct

/-!
The case of `PiTensorProduct`.
-/

open DirectSum Set LinearMap Submodule TensorProduct


section PiTensorProduct

open PiTensorProduct BigOperators

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R]

variable {ι : Type*}

variable [Fintype ι]

variable [DecidableEq ι]

variable (κ : ι → Type*) [(i : ι) → DecidableEq (κ i)]

variable (M : ι → Type*)

variable [∀ i, AddCommMonoid (M i)]

variable [∀ i, Module R (M i)]

variable [(i : ι) → (x : M i) → Decidable (x ≠ 0)]

/-- If `ι` is a `Fintype`, `κ i` is a family of types indexed by `ι` and `M i` is a family
of modules indexed by `ι`, then the tensor product of the family `κ i →₀ M i` is linearly
equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/
def finsuppPiTensorProduct : (⨂[R] i, κ i →₀ M i) ≃ₗ[R] ((i : ι) → κ i) →₀ ⨂[R] i, M i :=
  PiTensorProduct.congr (fun i ↦ finsuppLEquivDirectSum R (M i) (κ i)) ≪≫ₗ
  (PiTensorProduct.directSum R (fun (i : ι) ↦ fun (_ : κ i) ↦ M i)) ≪≫ₗ
  (finsuppLEquivDirectSum R (⨂[R] i, M i) ((i : ι) → κ i)).symm

@[simp]
theorem finsuppPiTensorProduct_single (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    finsuppPiTensorProduct R κ M (⨂ₜ[R] i, Finsupp.single (p i) (m i)) =
    Finsupp.single p (⨂ₜ[R] i, m i) := by
  classical
  simp only [finsuppPiTensorProduct, PiTensorProduct.directSum, LinearEquiv.trans_apply,
    congr_tprod, finsuppLEquivDirectSum_single, LinearEquiv.ofLinear_apply, lift.tprod,
    MultilinearMap.fromDirectSumEquiv_apply, compMultilinearMap_apply, map_sum,
    finsuppLEquivDirectSum_symm_lof]
  rw [Finset.sum_subset (piFinset_support_lof_sub R κ p _)]
  · rw [Finset.sum_singleton]
    simp only [lof_apply]
  · intro q _ hq
    simp only [Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq, not_forall, not_not] at hq
    obtain ⟨i, hi⟩ := hq
    simp only [Finsupp.single_eq_zero]
    exact (tprod R).map_coord_zero i hi

@[simp]
theorem finsuppPiTensorProduct_apply (f : (i : ι) → (κ i →₀ M i)) (p : (i : ι) → κ i) :
    finsuppPiTensorProduct R κ M (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i) := by
  rw [congrArg (tprod R) (funext (fun i ↦ (Eq.symm (Finsupp.sum_single (f i)))))]
  erw [MultilinearMap.map_sum_finset (tprod R)]
  simp only [map_sum, finsuppPiTensorProduct_single]
  rw [Finset.sum_apply']
  rw [← Finset.sum_union_eq_right (s₁ := {p}) (fun _ _ h ↦ by
       simp only [Fintype.mem_piFinset, Finsupp.mem_support_iff, ne_eq, not_forall, not_not] at h
       obtain ⟨i, hi⟩ := h
       rw [(tprod R).map_coord_zero i hi, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]),
   Finset.sum_union_eq_left (fun _ _ h ↦ Finsupp.single_eq_of_ne (Finset.not_mem_singleton.mp h)),
   Finset.sum_singleton, Finsupp.single_eq_same]

@[simp]
theorem finsuppPiTensorProduct_symm_single (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    (finsuppPiTensorProduct R κ M).symm (Finsupp.single p (⨂ₜ[R] i, m i)) =
    ⨂ₜ[R] i, Finsupp.single (p i) (m i) :=
  (LinearEquiv.symm_apply_eq _).2 (finsuppPiTensorProduct_single _ _ _ _ _).symm

variable [(x : R) → Decidable (x ≠ 0)]

/-- A variant of `finsuppPiTensorProduct` where all modules `M i` are the ground ring.
-/
def finsuppPiTensorProduct' : (⨂[R] i, (κ i →₀ R)) ≃ₗ[R] ((i : ι) → κ i) →₀ R :=
  finsuppPiTensorProduct R κ (fun _ ↦ R) ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) → κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]
theorem finsuppPiTensorProduct'_apply_apply (f : (i : ι) → κ i →₀ R) (p : (i : ι) → κ i) :
    finsuppPiTensorProduct' R κ (⨂ₜ[R] i, f i) p = ∏ i, f i (p i) := by
  simp only [finsuppPiTensorProduct', LinearEquiv.trans_apply, Finsupp.lcongr_apply_apply,
    Equiv.refl_symm, Equiv.refl_apply, finsuppPiTensorProduct_apply, AlgEquiv.toLinearEquiv_apply,
    constantBaseRingEquiv_tprod]

@[simp]
theorem finsuppPiTensorProduct'_tprod_single (p : (i : ι) → κ i) (r : ι → R) :
    finsuppPiTensorProduct' R κ (⨂ₜ[R] i, Finsupp.single (p i) (r i)) =
    Finsupp.single p (∏ i, r i) := by
  ext q
  simp only [finsuppPiTensorProduct'_apply_apply]
  by_cases h : q = p
  · rw [h]; simp only [Finsupp.single_eq_same]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Finsupp.single_eq_of_ne (Ne.symm h), Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [(Finsupp.single_eq_of_ne (Ne.symm hi))])]

end PiTensorProduct

section PiTensorProduct

open PiTensorProduct BigOperators

attribute [local ext] PiTensorProduct.ext

open LinearMap

open scoped TensorProduct

variable {ι R : Type*} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {κ : ι → Type*}

variable [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)] [(x : R) → Decidable (x ≠ 0)]

/-- Let `ι` be a `Fintype` and `M` be a family of modules indexed by `ι`. If `b i : κ i → M i`
is a basis for every `i` in `ι`, then `fun (p : Π i, κ i) ↦ ⨂ₜ[R] i, b i (p i)` is a basis
of `⨂[R] i, M i`.
-/
def Basis.piTensorProduct (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i ↦ (b i).repr)).trans <|
        (finsuppPiTensorProduct R _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

theorem Basis.piTensorProduct_apply (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i) :
    Basis.piTensorProduct b p = ⨂ₜ[R] i, (b i) (p i) := by
  simp only [piTensorProduct, LinearEquiv.trans_symm, Finsupp.lcongr_symm, Equiv.refl_symm,
    AlgEquiv.toLinearEquiv_symm, map_apply, Finsupp.coe_basisSingleOne, LinearEquiv.trans_apply,
    Finsupp.lcongr_single, Equiv.refl_apply, AlgEquiv.toLinearEquiv_apply, _root_.map_one]
  apply LinearEquiv.injective (PiTensorProduct.congr (fun i ↦ (b i).repr))
  simp only [LinearEquiv.apply_symm_apply, congr_tprod, repr_self]
  apply LinearEquiv.injective (finsuppPiTensorProduct R κ fun _ ↦ R)
  simp only [LinearEquiv.apply_symm_apply, finsuppPiTensorProduct_single]
  rfl

end PiTensorProduct
