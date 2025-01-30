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
`crAnF_normalOrderF_superCommuteF_eq_zero_mul`.

-/

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_create_create_ofCrAnList
    (φc φc' : 𝓕.CrAnStates) (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφc' : 𝓕 |>ᶜ φc' = CreateAnnihilate.create) (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (𝓝ᶠ(ofCrAnList φs * [ofCrAnState φc, ofCrAnState φc']ₛca * ofCrAnList φs')) = 0 := by
  rw [normalOrderF_superCommuteF_ofCrAnList_create_create_ofCrAnList φc φc' hφc hφc' φs φs']
  rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommuteF_create_create φc φc' hφc hφc']
  simp

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_annihilate_annihilate_ofCrAnList
    (φa φa' : 𝓕.CrAnStates) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕 |>ᶜ φa' = CreateAnnihilate.annihilate) (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (𝓝ᶠ(ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca * ofCrAnList φs')) = 0 := by
  rw [normalOrderF_superCommuteF_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
  rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommuteF_annihilate_annihilate φa φa' hφa hφa']
  simp

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrderF
      (ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca * ofCrAnList φs')) = 0 := by
  rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa) with hφa | hφa
  <;> rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa') with hφa' | hφa'
  · rw [normalOrderF_superCommuteF_ofCrAnList_create_create_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommuteF_create_create φa φa' hφa hφa']
    simp
  · rw [normalOrderF_superCommuteF_create_annihilate φa φa' hφa hφa' (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrderF_superCommuteF_annihilate_create φa' φa hφa' hφa (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrderF_superCommuteF_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, 𝓞.superCommuteF_annihilate_annihilate φa φa' hφa hφa']
    simp

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates)
    (a : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrderF (ofCrAnList φs *
    [ofCrAnState φa, ofCrAnState φa']ₛca * a)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap ((ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca))) a = 0
  have hf : 𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ
      mulLinearMap (ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp only [ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    exact crAnF_normalOrderF_superCommuteF_ofCrAnList_ofCrAnList_eq_zero φa φa' φs l
  rw [hf]
  simp

lemma crAnF_normalOrderF_superCommuteF_ofCrAnState_eq_zero_mul (φa φa' : 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrderF (a * [ofCrAnState φa, ofCrAnState φa']ₛca * b)) = 0 := by
  rw [mul_assoc]
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ mulLinearMap.flip
    ([ofCrAnState φa, ofCrAnState φa']ₛca * b)) a = 0
  have hf : 𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ mulLinearMap.flip
      ([ofCrAnState φa, ofCrAnState φa']ₛca * b) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [← mul_assoc]
    exact crAnF_normalOrderF_superCommuteF_ofCrAnList_eq_zero φa φa' _ _
  rw [hf]
  simp

lemma crAnF_normalOrderF_superCommuteF_ofCrAnState_ofCrAnList_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrderF (a * [ofCrAnState φa, ofCrAnList φs]ₛca * b)) = 0 := by
  rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b, ofCrAnList_singleton]
  rw [crAnF_normalOrderF_superCommuteF_ofCrAnState_eq_zero_mul]

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_ofCrAnState_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrderF (a * [ofCrAnList φs, ofCrAnState φa]ₛca * b)) = 0 := by
  rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList_symm, ofCrAnList_singleton]
  simp only [FieldStatistic.instCommGroup.eq_1, FieldStatistic.ofList_singleton, mul_neg,
    Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, map_neg, map_smul]
  rw [crAnF_normalOrderF_superCommuteF_ofCrAnState_ofCrAnList_eq_zero_mul]
  simp

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_ofCrAnList_eq_zero_mul
    (φs φs' : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrderF (a * [ofCrAnList φs, ofCrAnList φs']ₛca * b)) = 0 := by
  rw [superCommuteF_ofCrAnList_ofCrAnList_eq_sum, Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b]
  rw [crAnF_normalOrderF_superCommuteF_ofCrAnList_ofCrAnState_eq_zero_mul]

lemma crAnF_normalOrderF_superCommuteF_ofCrAnList_eq_zero_mul
    (φs : List 𝓕.CrAnStates)
    (a b c : 𝓕.CrAnAlgebra) :
    𝓞.crAnF (normalOrderF (a * [ofCrAnList φs, c]ₛca * b)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF (ofCrAnList φs)) c = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF (ofCrAnList φs)) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs'
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [crAnF_normalOrderF_superCommuteF_ofCrAnList_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma crAnF_normalOrderF_superCommuteF_eq_zero_mul
    (a b c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrderF (a * [d, c]ₛca * b)) = 0 := by
  change (𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF.flip c) d = 0
  have hf : (𝓞.crAnF.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF.flip c) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [crAnF_normalOrderF_superCommuteF_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma crAnF_normalOrderF_superCommuteF_eq_zero_mul_right
    (b c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrderF ([d, c]ₛca * b)) = 0 := by
  rw [← crAnF_normalOrderF_superCommuteF_eq_zero_mul 1 b c d]
  simp

@[simp]
lemma crAnF_normalOrderF_superCommuteF_eq_zero_mul_left
    (a c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrderF (a * [d, c]ₛca)) = 0 := by
  rw [← crAnF_normalOrderF_superCommuteF_eq_zero_mul a 1 c d]
  simp

@[simp]
lemma crAnF_normalOrderF_superCommuteF_eq_zero
    (c d : 𝓕.CrAnAlgebra) : 𝓞.crAnF (normalOrderF [d, c]ₛca) = 0 := by
  rw [← crAnF_normalOrderF_superCommuteF_eq_zero_mul 1 1 c d]
  simp

/-!

## Swapping terms in a normal order.

-/

lemma crAnF_normalOrderF_ofState_ofState_swap (φ φ' : 𝓕.States) :
    𝓞.crAnF (normalOrderF (ofState φ * ofState φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓞.crAnF (normalOrderF (ofState φ' * ofState φ)) := by
  rw [← ofStateList_singleton, ← ofStateList_singleton,
    ofStateList_mul_ofStateList_eq_superCommuteF]
  simp

lemma crAnF_normalOrderF_ofCrAnState_ofCrAnList_swap (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) :
    𝓞.crAnF (normalOrderF (ofCrAnState φ * ofCrAnList φs)) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓞.crAnF (normalOrderF (ofCrAnList φs * ofCrAnState φ)) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommuteF]
  simp

lemma crAnF_normalOrderF_ofCrAnState_ofStatesList_swap (φ : 𝓕.CrAnStates)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrderF (ofCrAnState φ * ofStateList φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrderF (ofStateList φ' * ofCrAnState φ)) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofStateList_eq_superCommuteF]
  simp

lemma crAnF_normalOrderF_anPartF_ofStatesList_swap (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrderF (anPartF φ * ofStateList φ')) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrderF (ofStateList φ' * anPartF φ)) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPartF_position, instCommGroup.eq_1]
    rw [crAnF_normalOrderF_ofCrAnState_ofStatesList_swap]
    rfl
  | .outAsymp φ =>
    simp only [anPartF_posAsymp, instCommGroup.eq_1]
    rw [crAnF_normalOrderF_ofCrAnState_ofStatesList_swap]
    rfl

lemma crAnF_normalOrderF_ofStatesList_anPartF_swap (φ : 𝓕.States) (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrderF (ofStateList φ' * anPartF φ))
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrderF (anPartF φ * ofStateList φ')) := by
  rw [crAnF_normalOrderF_anPartF_ofStatesList_swap]
  simp [smul_smul, FieldStatistic.exchangeSign_mul_self]

lemma crAnF_normalOrderF_ofStatesList_mul_anPartF_swap (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (normalOrderF (ofStateList φ') * anPartF φ) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓞.crAnF (normalOrderF (anPartF φ * ofStateList φ')) := by
  rw [← normalOrderF_mul_anPartF]
  rw [crAnF_normalOrderF_ofStatesList_anPartF_swap]

/-!

## Super commutators with a normal ordered term as sums

-/
lemma crAnF_ofCrAnState_superCommuteF_normalOrderF_ofCrAnList_eq_sum (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) : 𝓞.crAnF ([ofCrAnState φ, normalOrderF (ofCrAnList φs)]ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
      𝓞.crAnF ([ofCrAnState φ, ofCrAnState φs[n]]ₛca)
      * 𝓞.crAnF (normalOrderF (ofCrAnList (φs.eraseIdx n))) := by
  rw [normalOrderF_ofCrAnList, map_smul, map_smul]
  rw [crAnF_superCommuteF_ofCrAnState_ofCrAnList_eq_sum, sum_normalOrderList_length]
  simp only [instCommGroup.eq_1, List.get_eq_getElem, normalOrderList_get_normalOrderEquiv,
    normalOrderList_eraseIdx_normalOrderEquiv, Algebra.smul_mul_assoc, map_sum, map_smul, map_mul,
    Finset.smul_sum, Fin.getElem_fin]
  congr
  funext n
  rw [ofCrAnList_eq_normalOrderF, map_smul, mul_smul_comm, smul_smul, smul_smul]
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
  · erw [𝓞.superCommuteF_different_statistics _ _ hs]
    simp

lemma crAnF_ofCrAnState_superCommuteF_normalOrderF_ofStateList_eq_sum (φ : 𝓕.CrAnStates)
    (φs : List 𝓕.States) : 𝓞.crAnF ([ofCrAnState φ, normalOrderF (ofStateList φs)]ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    𝓞.crAnF ([ofCrAnState φ, ofState φs[n]]ₛca)
    * 𝓞.crAnF (normalOrderF (ofStateList (φs.eraseIdx n))) := by
  conv_lhs =>
    rw [ofStateList_sum, map_sum, map_sum, map_sum]
    enter [2, s]
    rw [crAnF_ofCrAnState_superCommuteF_normalOrderF_ofCrAnList_eq_sum,
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

/--
Within a proto-operator algebra we have that
`[anPartF φ, 𝓝ᶠ(φs)] = ∑ i, sᵢ • [anPartF φ, φᵢ]ₛca * 𝓝ᶠ(φ₀…φᵢ₋₁φᵢ₊₁…φₙ)`
where `sᵢ` is the exchange sign for `φ` and `φ₀…φᵢ₋₁`.

The origin of this result is
- `superCommuteF_ofCrAnList_ofCrAnList_eq_sum`
-/
lemma crAnF_anPartF_superCommuteF_normalOrderF_ofStateList_eq_sum (φ : 𝓕.States) (φs : List 𝓕.States) :
    𝓞.crAnF ([anPartF φ, 𝓝ᶠ(φs)]ₛca) =
    ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    𝓞.crAnF ([anPartF φ, ofState φs[n]]ₛca) * 𝓞.crAnF 𝓝ᶠ(φs.eraseIdx n) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPartF_position, instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc]
    rw [crAnF_ofCrAnState_superCommuteF_normalOrderF_ofStateList_eq_sum]
    simp [crAnStatistics]
  | .outAsymp φ =>
    simp only [anPartF_posAsymp, instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc]
    rw [crAnF_ofCrAnState_superCommuteF_normalOrderF_ofStateList_eq_sum]
    simp [crAnStatistics]

/-!

## Multiplying with normal ordered terms

-/
/--
Within a proto-operator algebra we have that
`anPartF φ * 𝓝ᶠ(φ₀φ₁…φₙ) = 𝓝ᶠ((anPartF φ)φ₀φ₁…φₙ) + [anpart φ, 𝓝ᶠ(φ₀φ₁…φₙ)]ₛca`.
-/
lemma crAnF_anPartF_mul_normalOrderF_ofStatesList_eq_superCommuteF (φ : 𝓕.States)
    (φ' : List 𝓕.States) :
    𝓞.crAnF (anPartF φ * normalOrderF (ofStateList φ')) =
    𝓞.crAnF (normalOrderF (anPartF φ * ofStateList φ')) +
    𝓞.crAnF ([anPartF φ, normalOrderF (ofStateList φ')]ₛca) := by
  rw [anPartF_mul_normalOrderF_ofStateList_eq_superCommuteF]
  simp only [instCommGroup.eq_1, map_add, map_smul]
  congr
  rw [crAnF_normalOrderF_anPartF_ofStatesList_swap]

/--
Within a proto-operator algebra we have that
`φ * 𝓝ᶠ(φ₀φ₁…φₙ) = 𝓝ᶠ(φφ₀φ₁…φₙ) + [anpart φ, 𝓝ᶠ(φ₀φ₁…φₙ)]ₛca`.
-/
lemma crAnF_ofState_mul_normalOrderF_ofStatesList_eq_superCommuteF (φ : 𝓕.States)
    (φs : List 𝓕.States) : 𝓞.crAnF (ofState φ * 𝓝ᶠ(φs)) =
    𝓞.crAnF (normalOrderF (ofState φ * ofStateList φs)) +
    𝓞.crAnF ([anPartF φ, 𝓝ᶠ(φs)]ₛca) := by
  conv_lhs => rw [ofState_eq_crPartF_add_anPartF]
  rw [add_mul, map_add, crAnF_anPartF_mul_normalOrderF_ofStatesList_eq_superCommuteF, ← add_assoc,
    ← normalOrderF_crPartF_mul, ← map_add]
  conv_lhs =>
    lhs
    rw [← map_add, ← add_mul, ← ofState_eq_crPartF_add_anPartF]

/-- In the expansion of `ofState φ * normalOrderF (ofStateList φs)` the element
  of `𝓞.A` associated with contracting `φ` with the (optional) `n`th element of `φs`. -/
noncomputable def contractStateAtIndex (φ : 𝓕.States) (φs : List 𝓕.States)
    (n : Option (Fin φs.length)) : 𝓞.A :=
  match n with
  | none => 1
  | some n => 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    𝓞.crAnF ([anPartF φ, ofState φs[n]]ₛca)

/--
Within a proto-operator algebra,
`φ * N(φ₀φ₁…φₙ) = N(φφ₀φ₁…φₙ) + ∑ i, (sᵢ • [anPartF φ, φᵢ]ₛ) * N(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)`,
where `sₙ` is the exchange sign for `φ` and `φ₀φ₁…φᵢ₋₁`.
-/
lemma crAnF_ofState_mul_normalOrderF_ofStatesList_eq_sum (φ : 𝓕.States)
    (φs : List 𝓕.States) :
    𝓞.crAnF (ofState φ * normalOrderF (ofStateList φs)) =
    ∑ n : Option (Fin φs.length),
      contractStateAtIndex φ φs n *
      𝓞.crAnF (normalOrderF (ofStateList (HepLean.List.optionEraseZ φs φ n))) := by
  rw [crAnF_ofState_mul_normalOrderF_ofStatesList_eq_superCommuteF]
  rw [crAnF_anPartF_superCommuteF_normalOrderF_ofStateList_eq_sum]
  simp only [instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc, contractStateAtIndex,
    Fintype.sum_option, one_mul]
  rfl

/-!

## Cons vs insertIdx for a normal ordered term.

-/

/--
Within a proto-operator algebra, `N(φφ₀φ₁…φₙ) = s • N(φ₀…φₖ₋₁φφₖ…φₙ)`, where
`s` is the exchange sign for `φ` and `φ₀…φₖ₋₁`.
-/
lemma crAnF_ofState_normalOrderF_insert (φ : 𝓕.States) (φs : List 𝓕.States)
    (k : Fin φs.length.succ) :
    𝓞.crAnF (normalOrderF (ofStateList (φ :: φs))) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs.take k) • 𝓞.crAnF (normalOrderF (ofStateList (φs.insertIdx k φ))) := by
  have hl : φs.insertIdx k φ = φs.take k ++ [φ] ++ φs.drop k := by
    rw [HepLean.List.insertIdx_eq_take_drop]
    simp
  rw [hl]
  rw [ofStateList_append, ofStateList_append]
  rw [ofStateList_mul_ofStateList_eq_superCommuteF, add_mul]
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one, ofList_singleton, Algebra.smul_mul_assoc,
    map_add, map_smul, crAnF_normalOrderF_superCommuteF_eq_zero_mul_right, add_zero, smul_smul,
    exchangeSign_mul_self_swap, one_smul]
  rw [← ofStateList_append, ← ofStateList_append]
  simp

end ProtoOperatorAlgebra

end FieldSpecification
