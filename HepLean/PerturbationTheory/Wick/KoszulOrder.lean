/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Signs.StaticWickCoef
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Given a relation `r` on `I` sorts elements of `MonoidAlgebra ℂ (FreeMonoid I)` by `r` giving it
  a signed dependent on `q`. -/
def koszulOrderMonoidAlgebra :
    MonoidAlgebra ℂ (FreeMonoid 𝓕) →ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid 𝓕) :=
  Finsupp.lift (MonoidAlgebra ℂ (FreeMonoid 𝓕)) ℂ (List 𝓕)
    (fun i => Finsupp.lsingle (R := ℂ) (List.insertionSort le i) (koszulSign q le i))

lemma koszulOrderMonoidAlgebra_ofList (i : List 𝓕) :
    koszulOrderMonoidAlgebra q le (MonoidAlgebra.of ℂ (FreeMonoid 𝓕) i) =
    (koszulSign q le i) • (MonoidAlgebra.of ℂ (FreeMonoid 𝓕) (List.insertionSort le i)) := by
  simp only [koszulOrderMonoidAlgebra, Finsupp.lsingle_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.smul_single', mul_one]
  rw [MonoidAlgebra.ext_iff]
  intro x
  erw [Finsupp.lift_apply]
  simp only [MonoidAlgebra.smul_single', zero_mul, Finsupp.single_zero, Finsupp.sum_single_index,
    one_mul]

@[simp]
lemma koszulOrderMonoidAlgebra_single (l : FreeMonoid 𝓕) (x : ℂ) :
    koszulOrderMonoidAlgebra q le (MonoidAlgebra.single l x)
    = (koszulSign q le l) • (MonoidAlgebra.single (List.insertionSort le l) x) := by
  simp only [koszulOrderMonoidAlgebra, Finsupp.lsingle_apply, MonoidAlgebra.smul_single']
  rw [MonoidAlgebra.ext_iff]
  intro x'
  erw [Finsupp.lift_apply]
  simp only [MonoidAlgebra.smul_single', zero_mul, Finsupp.single_zero, Finsupp.sum_single_index,
    one_mul, MonoidAlgebra.single]
  congr 2
  rw [NonUnitalNormedCommRing.mul_comm]

/-- Given a relation `r` on `I` sorts elements of `FreeAlgebra ℂ I` by `r` giving it
  a signed dependent on `q`. -/
def koszulOrder : FreeAlgebra ℂ 𝓕 →ₗ[ℂ] FreeAlgebra ℂ 𝓕 :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toLinearMap
  ∘ₗ koszulOrderMonoidAlgebra q le
  ∘ₗ FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toLinearMap

@[simp]
lemma koszulOrder_ι (i : 𝓕) : koszulOrder q le (FreeAlgebra.ι ℂ i) = FreeAlgebra.ι ℂ i := by
  simp only [koszulOrder, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
    koszulOrderMonoidAlgebra, Finsupp.lsingle_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply]
  rw [AlgEquiv.symm_apply_eq]
  simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    AlgEquiv.ofAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rw [@MonoidAlgebra.ext_iff]
  intro x
  erw [Finsupp.lift_apply]
  simp only [MonoidAlgebra.smul_single', List.insertionSort, List.orderedInsert,
    koszulSign_freeMonoid_of, mul_one, Finsupp.single_zero, Finsupp.sum_single_index]
  rfl

@[simp]
lemma koszulOrder_single (l : FreeMonoid 𝓕) :
    koszulOrder q le (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x))
    = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.single (List.insertionSort le l) (koszulSign q le l * x)) := by
  simp [koszulOrder]

@[simp]
lemma koszulOrder_ι_pair (i j : 𝓕) : koszulOrder q le (FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j) =
    if le i j then FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j else
    (koszulSign q le [i, j]) • (FreeAlgebra.ι ℂ j * FreeAlgebra.ι ℂ i) := by
  have h1 : FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j =
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [i, j] 1) := by
    simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
    rfl
  conv_lhs => rw [h1]
  simp only [koszulOrder, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
    LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
    koszulOrderMonoidAlgebra_single, List.insertionSort, List.orderedInsert,
    MonoidAlgebra.smul_single', mul_one]
  by_cases hr : le i j
  · rw [if_pos hr, if_pos hr]
    simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single]
    have hKS : koszulSign q le [i, j] = 1 := by
      simp only [koszulSign, koszulSignInsert, Fin.isValue, mul_one, ite_eq_left_iff,
        ite_eq_right_iff, and_imp]
      exact fun a a_1 a_2 => False.elim (a hr)
    rw [hKS]
    simp only [one_smul]
    rfl
  · rw [if_neg hr, if_neg hr]
    simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single]
    rfl

@[simp]
lemma koszulOrder_one : koszulOrder q le 1 = 1 := by
  trans koszulOrder q le (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [] 1))
  congr
  · simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
    rfl
  · simp only [koszulOrder_single, List.insertionSort, mul_one, EmbeddingLike.map_eq_one_iff]
    rfl

lemma mul_koszulOrder_le (i : 𝓕) (A : FreeAlgebra ℂ 𝓕) (hi : ∀ j, le i j) :
    FreeAlgebra.ι ℂ i * koszulOrder q le A = koszulOrder q le (FreeAlgebra.ι ℂ i * A) := by
  let f : FreeAlgebra ℂ 𝓕 →ₗ[ℂ] FreeAlgebra ℂ 𝓕 := {
    toFun := fun x => FreeAlgebra.ι ℂ i * x,
    map_add' := fun x y => by
      simp [mul_add],
    map_smul' := by simp}
  change (f ∘ₗ koszulOrder q le) A = (koszulOrder q le ∘ₗ f) _
  have f_single (l : FreeMonoid 𝓕) (x : ℂ) :
      f ((FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)))
      = (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single (i :: l) x)) := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, f]
    have hf : FreeAlgebra.ι ℂ i = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        (MonoidAlgebra.single [i] 1) := by
      simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
        AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
      rfl
    rw [hf]
    rw [@AlgEquiv.eq_symm_apply]
    simp only [map_mul, AlgEquiv.apply_symm_apply, MonoidAlgebra.single_mul_single, one_mul]
    rfl
  have h1 : f ∘ₗ koszulOrder q le = koszulOrder q le ∘ₗ f := by
    let e : FreeAlgebra ℂ 𝓕 ≃ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid 𝓕) :=
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv
    apply (LinearEquiv.eq_comp_toLinearMap_iff (e₁₂ := e.symm) _ _).mp
    apply MonoidAlgebra.lhom_ext'
    intro l
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      MonoidAlgebra.lsingle_apply]
    erw [koszulOrder_single]
    rw [f_single]
    erw [f_single]
    rw [koszulOrder_single]
    congr 2
    · simp only [List.insertionSort]
      have hi (l : List 𝓕) : i :: l = List.orderedInsert le i l := by
        induction l with
        | nil => rfl
        | cons j l ih =>
          refine (List.orderedInsert_of_le le l (hi j)).symm
      exact hi _
    · congr 1
      rw [koszulSign]
      have h1 (l : List 𝓕) : koszulSignInsert q le i l = 1 := by
        exact koszulSignInsert_le_forall q le i l hi
      rw [h1]
      simp
  rw [h1]

lemma koszulOrder_mul_ge (i : 𝓕) (A : FreeAlgebra ℂ 𝓕) (hi : ∀ j, le j i) :
    koszulOrder q le A * FreeAlgebra.ι ℂ i = koszulOrder q le (A * FreeAlgebra.ι ℂ i) := by
  let f : FreeAlgebra ℂ 𝓕 →ₗ[ℂ] FreeAlgebra ℂ 𝓕 := {
    toFun := fun x => x * FreeAlgebra.ι ℂ i,
    map_add' := fun x y => by
      simp [add_mul],
    map_smul' := by simp}
  change (f ∘ₗ koszulOrder q le) A = (koszulOrder q le ∘ₗ f) A
  have f_single (l : FreeMonoid 𝓕) (x : ℂ) :
      f ((FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)))
      = (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
      (MonoidAlgebra.single (l.toList ++ [i]) x)) := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, f]
    have hf : FreeAlgebra.ι ℂ i = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        (MonoidAlgebra.single [i] 1) := by
      simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
        AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
      rfl
    rw [hf]
    rw [@AlgEquiv.eq_symm_apply]
    simp only [map_mul, AlgEquiv.apply_symm_apply, MonoidAlgebra.single_mul_single, mul_one]
    rfl
  have h1 : f ∘ₗ koszulOrder q le = koszulOrder q le ∘ₗ f := by
    let e : FreeAlgebra ℂ 𝓕 ≃ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid 𝓕) :=
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv
    apply (LinearEquiv.eq_comp_toLinearMap_iff (e₁₂ := e.symm) _ _).mp
    apply MonoidAlgebra.lhom_ext'
    intro l
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      MonoidAlgebra.lsingle_apply]
    erw [koszulOrder_single]
    rw [f_single]
    erw [f_single]
    rw [koszulOrder_single]
    congr 3
    · change (List.insertionSort le l) ++ [i] = List.insertionSort le (l.toList ++ [i])
      have hoi (l : List 𝓕) (j : 𝓕) : List.orderedInsert le j (l ++ [i]) =
          List.orderedInsert le j l ++ [i] := by
        induction l with
        | nil => simp [hi]
        | cons b l ih =>
          simp only [List.orderedInsert, List.append_eq]
          by_cases hr : le j b
          · rw [if_pos hr, if_pos hr]
            rfl
          · rw [if_neg hr, if_neg hr]
            rw [ih]
            rfl
      have hI (l : List 𝓕) : (List.insertionSort le l) ++ [i] =
          List.insertionSort le (l ++ [i]) := by
        induction l with
        | nil => rfl
        | cons j l ih =>
          simp only [List.insertionSort, List.append_eq]
          rw [← ih]
          rw [hoi]
      rw [hI]
      rfl
    · have hI (l : List 𝓕) : koszulSign q le l = koszulSign q le (l ++ [i]) := by
        induction l with
        | nil => simp [koszulSign, koszulSignInsert]
        | cons j l ih =>
          simp only [koszulSign, List.append_eq]
          rw [ih]
          simp only [mul_eq_mul_right_iff]
          apply Or.inl
          rw [koszulSignInsert_ge_forall_append q le l j i hi]
      rw [hI]
      rfl
  rw [h1]

end
end Wick
