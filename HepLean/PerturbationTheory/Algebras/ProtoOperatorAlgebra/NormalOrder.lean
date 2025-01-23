/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.NormalOrder
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Normal ordering of the operator algebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

namespace ProtoOperatorAlgebra
variable {𝓞 : ProtoOperatorAlgebra 𝓕}
open CrAnAlgebra
open FieldStatistic

/-!

## Normal order of super-commutators.

The main result of this section is
`crAnF_normalOrder_superCommute_eq_zero_mul`.

-/
lemma crAnF_normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList
    (φc φc' : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφc' : 𝓕 |>ᶜ φc' = CreateAnnihilate.create)
    (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder
    (ofCrAnList φs * superCommute (ofCrAnState φc) (ofCrAnState φc') * ofCrAnList φs')) = 0 := by
  rw [normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList φc φc' hφc hφc' φs φs']
  rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_create_create φc φc' hφc hφc']
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList
    (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕 |>ᶜ φa' = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder
    (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') * ofCrAnList φs')) = 0 := by
  rw [normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
  rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_annihilate_annihilate φa φa' hφa hφa']
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder
      (ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa') * ofCrAnList φs')) = 0 := by
  rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa) with hφa | hφa
  <;> rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa') with hφa' | hφa'
  · rw [normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_create_create φa φa' hφa hφa']
    simp
  · rw [normalOrder_superCommute_create_annihilate φa φa' hφa hφa' (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrder_superCommute_annihilate_create φa' φa hφa' hφa (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommute_annihilate_annihilate φa φa' hφa hφa']
    simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates)
    (a : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (ofCrAnList φs *
    superCommute (ofCrAnState φa) (ofCrAnState φa') * a)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap ((ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa')))) a = 0
  have hf : 𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
      mulLinearMap ((ofCrAnList φs * superCommute (ofCrAnState φa) (ofCrAnState φa'))) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp only [ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    exact crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero φa φa' φs l
  rw [hf]
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnState_eq_zero_mul (φa φa' : 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnState φa) (ofCrAnState φa') * b)) = 0 := by
  rw [mul_assoc]
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap.flip
    ((superCommute (ofCrAnState φa) (ofCrAnState φa') * b))) a = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap.flip
      ((superCommute (ofCrAnState φa) (ofCrAnState φa') * b))) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [← mul_assoc]
    exact crAnF_normalOrder_superCommute_ofCrAnList_eq_zero φa φa' _ _
  rw [hf]
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnState_ofCrAnList_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnState φa) (ofCrAnList φs) * b)) = 0 := by
  rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b, ofCrAnList_singleton]
  rw [crAnF_normalOrder_superCommute_ofCrAnState_eq_zero_mul]

lemma crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnState_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnList φs) (ofCrAnState φa) * b)) = 0 := by
  rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_symm, ofCrAnList_singleton]
  simp only [FieldStatistic.instCommGroup.eq_1, FieldStatistic.ofList_singleton, mul_neg,
    Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, map_neg, map_smul]
  rw [crAnF_normalOrder_superCommute_ofCrAnState_ofCrAnList_eq_zero_mul]
  simp

lemma crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero_mul
    (φs φs' : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnList φs) (ofCrAnList φs') * b)) = 0 := by
  rw [superCommute_ofCrAnList_ofCrAnList_eq_sum, Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b]
  rw [crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnState_eq_zero_mul]

lemma crAnF_normalOrder_superCommute_ofCrAnList_eq_zero_mul
    (φs : List 𝓕.CrAnStates)
    (a b c : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrder (a * superCommute (ofCrAnList φs) c * b)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute (ofCrAnList φs)) c = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute (ofCrAnList φs)) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs'
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [crAnF_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero_mul
    (a b c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (a * superCommute d c * b)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute.flip c) d = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute.flip c) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [crAnF_normalOrder_superCommute_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero_mul_right
    (b c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (superCommute d c * b)) = 0 := by
  rw [← crAnF_normalOrder_superCommute_eq_zero_mul 1 b c d]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero_mul_left
    (a c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (a * superCommute d c)) = 0 := by
  rw [← crAnF_normalOrder_superCommute_eq_zero_mul a 1 c d]
  simp

@[simp]
lemma crAnF_normalOrder_superCommute_eq_zero
    (c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrder (superCommute d c)) = 0 := by
  rw [← crAnF_normalOrder_superCommute_eq_zero_mul 1 1 c d]
  simp

/-!

## Swapping terms in a normal order.

-/

lemma crAnF_normalOrder_ofState_ofState_swap (φ φ' : 𝓕.States) :
    𝓞.crAnF (normalOrder (ofState φ * ofState φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓞.crAnF (normalOrder (ofState φ' * ofState φ)) := by
  rw [← ofStateList_singleton, ← ofStateList_singleton,
    ofStateList_mul_ofStateList_eq_superCommute]
  simp

lemma crAnF_normalOrder_ofCrAnState_ofCrAnList_swap (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrder (ofCrAnState φ * ofCrAnList φs)) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓞.crAnF (normalOrder (ofCrAnList φs * ofCrAnState φ)) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp

lemma crAnF_normalOrder_ofCrAnState_ofStatesList_swap (φ : 𝓕.CrAnStates)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrder (ofCrAnState φ * ofStateList φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrder (ofStateList φ' * ofCrAnState φ)) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofStateList_eq_superCommute]
  simp

lemma crAnF_normalOrder_anPart_ofStatesList_swap (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrder (ofStateList φ' * anPart (StateAlgebra.ofState φ))) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPart_position, instCommGroup.eq_1]
    rw [crAnF_normalOrder_ofCrAnState_ofStatesList_swap]
    rfl
  | .outAsymp φ =>
    simp only [anPart_posAsymp, instCommGroup.eq_1]
    rw [crAnF_normalOrder_ofCrAnState_ofStatesList_swap]
    rfl

lemma crAnF_normalOrder_ofStatesList_anPart_swap (φ : 𝓕.States) (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrder (ofStateList φ' * anPart (StateAlgebra.ofState φ)))
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) := by
  rw [crAnF_normalOrder_anPart_ofStatesList_swap]
  simp [smul_smul, FieldStatistic.exchangeSign_mul_self]

lemma crAnF_normalOrder_ofStatesList_mul_anPart_swap (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrder (ofStateList φ') * anPart (StateAlgebra.ofState φ)) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) := by
  rw [← normalOrder_mul_anPart]
  rw [crAnF_normalOrder_ofStatesList_anPart_swap]

/-!

## Super commutators with a normal ordered term as sums

-/
lemma crAnF_ofCrAnState_superCommute_normalOrder_ofCrAnList_eq_sum (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) : 𝓞.crAnF (⟨ofCrAnState φ, normalOrder (ofCrAnList φs)⟩ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
      𝓞.crAnF (⟨ofCrAnState φ, ofCrAnState φs[n]⟩ₛca)
      * 𝓞.crAnF (normalOrder (ofCrAnList (φs.eraseIdx n))) := by
  rw [normalOrder_ofCrAnList, map_smul, map_smul]
  rw [crAnF_superCommute_ofCrAnState_ofCrAnList_eq_sum, sum_normalOrderList_length]
  simp only [instCommGroup.eq_1, List.get_eq_getElem, normalOrderList_get_normalOrderEquiv,
    normalOrderList_eraseIdx_normalOrderEquiv, Algebra.smul_mul_assoc, map_sum, map_smul, map_mul,
    Finset.smul_sum, Fin.getElem_fin]
  congr
  funext n
  rw [ofCrAnList_eq_normalOrder, map_smul, mul_smul_comm, smul_smul, smul_smul]
  by_cases hs : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[n])
  · congr
    erw [normalOrderSign_eraseIdx, ← hs]
    trans (normalOrderSign φs * normalOrderSign φs) *
      (𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ ((normalOrderList φs).take (normalOrderEquiv n))) *
      𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ ((normalOrderList φs).take (normalOrderEquiv n))))
      * 𝓢(𝓕 |>ₛ (φs.get n), 𝓕 |>ₛ (φs.take n))
    · ring_nf
      rw [hs]
      rfl
    · simp [hs]
  · erw [𝓞.superCommute_different_statistics _ _ hs]
    simp

lemma crAnF_ofCrAnState_superCommute_normalOrder_ofStateList_eq_sum (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.States) : 𝓞.crAnF (⟨ofCrAnState φ, normalOrder (ofStateList φs)⟩ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    𝓞.crAnF (⟨ofCrAnState φ, ofState φs[n]⟩ₛca)
    * 𝓞.crAnF (normalOrder (ofStateList (φs.eraseIdx n))) := by
  conv_lhs =>
    rw [ofStateList_sum, map_sum, map_sum, map_sum]
    enter [2, s]
    rw [crAnF_ofCrAnState_superCommute_normalOrder_ofCrAnList_eq_sum,
      CrAnSection.sum_over_length]
    enter [2, n]
    rw [CrAnSection.take_statistics_eq_take_state_statistics, smul_mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [instCommGroup.eq_1, Fin.coe_cast, Fin.getElem_fin,
    CrAnSection.sum_eraseIdxEquiv n _ n.prop,
    CrAnSection.eraseIdxEquiv_symm_getElem,
    CrAnSection.eraseIdxEquiv_symm_eraseIdx, ← Finset.smul_sum, Algebra.smul_mul_assoc]
  conv_lhs =>
    enter [2, 2, n]
    rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← ofState, ← map_sum, ← map_sum, ← ofStateList_sum]

lemma crAnF_anPart_superCommute_normalOrder_ofStateList_eq_sum (φ : 𝓕.States) (φs : List 𝓕.States) :
    𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φs)⟩ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), ofState φs[n]⟩ₛca)
    * 𝓞.crAnF (normalOrder (ofStateList (φs.eraseIdx n))) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPart_position, instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc]
    rw [crAnF_ofCrAnState_superCommute_normalOrder_ofStateList_eq_sum]
    simp [crAnStatistics]
  | .outAsymp φ =>
    simp only [anPart_posAsymp, instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc]
    rw [crAnF_ofCrAnState_superCommute_normalOrder_ofStateList_eq_sum]
    simp [crAnStatistics]

/-!

## Multiplying with normal ordered terms

-/
lemma crAnF_anPart_mul_normalOrder_ofStatesList_eq_superCommute (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (anPart (StateAlgebra.ofState φ) * normalOrder (ofStateList φ')) =
    𝓞.crAnF (normalOrder (anPart (StateAlgebra.ofState φ) * ofStateList φ')) +
    𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φ')⟩ₛca) := by
  rw [anPart_mul_normalOrder_ofStateList_eq_superCommute]
  simp only [instCommGroup.eq_1, map_add, map_smul]
  congr
  rw [crAnF_normalOrder_anPart_ofStatesList_swap]

lemma crAnF_ofState_mul_normalOrder_ofStatesList_eq_superCommute (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (ofState φ * normalOrder (ofStateList φ')) =
    𝓞.crAnF (normalOrder (ofState φ * ofStateList φ')) +
    𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), normalOrder (ofStateList φ')⟩ₛca) := by
  conv_lhs => rw [ofState_eq_crPart_add_anPart]
  rw [add_mul, map_add, crAnF_anPart_mul_normalOrder_ofStatesList_eq_superCommute, ← add_assoc,
    ← normalOrder_crPart_mul, ← map_add]
  conv_lhs =>
    lhs
    rw [← map_add, ← add_mul, ← ofState_eq_crPart_add_anPart]

/-- In the expansion of `ofState φ * normalOrder (ofStateList φs)` the element
  of `𝓞.A` associated with contracting `φ` with the (optional) `n`th element of `φs`. -/
noncomputable def contractStateAtIndex (φ : 𝓕.States) (φs : List 𝓕.States)
    (n : Option (Fin φs.length)) : 𝓞.A :=
  match n with
  | none => 1
  | some n => 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
        𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), ofState φs[n]⟩ₛca)

lemma crAnF_ofState_mul_normalOrder_ofStatesList_eq_sum (φ : 𝓕.States)
    (φs : List 𝓕.States) :
    𝓞.crAnF (ofState φ * normalOrder (ofStateList φs)) =
    ∑ n : Option (Fin φs.length),
      contractStateAtIndex φ φs n *
      𝓞.crAnF (normalOrder (ofStateList (HepLean.List.optionEraseZ φs φ n))) := by
  rw [crAnF_ofState_mul_normalOrder_ofStatesList_eq_superCommute]
  rw [crAnF_anPart_superCommute_normalOrder_ofStateList_eq_sum]
  simp only [instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc, contractStateAtIndex,
    Fintype.sum_option, one_mul]
  rfl

/-!

## Cons vs insertIdx for a normal ordered term.

-/

lemma crAnF_ofState_normalOrder_insert (φ : 𝓕.States) (φs : List 𝓕.States)
    (k : Fin φs.length.succ) :
    𝓞.crAnF (normalOrder (ofStateList (φ :: φs))) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs.take k) • 𝓞.crAnF (normalOrder (ofStateList (φs.insertIdx k φ))) := by
  have hl : φs.insertIdx k φ = φs.take k ++ [φ] ++ φs.drop k := by
    rw [HepLean.List.insertIdx_eq_take_drop]
    simp
  rw [hl]
  rw [ofStateList_append, ofStateList_append]
  rw [ofStateList_mul_ofStateList_eq_superCommute, add_mul]
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one, ofList_singleton, Algebra.smul_mul_assoc,
    map_add, map_smul, crAnF_normalOrder_superCommute_eq_zero_mul_right, add_zero, smul_smul,
    exchangeSign_mul_self_swap, one_smul]
  rw [← ofStateList_append, ← ofStateList_append]
  simp

end ProtoOperatorAlgebra

end FieldSpecification
