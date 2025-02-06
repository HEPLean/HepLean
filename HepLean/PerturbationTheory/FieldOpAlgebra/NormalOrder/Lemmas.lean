/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.NormalOrder.Basic
/-!

# Basic properties of normal ordering

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-!

## Properties of normal ordering.

-/

lemma normalOrder_eq_ι_normalOrderF (a : 𝓕.FieldOpFreeAlgebra) :
    𝓝(ι a) = ι 𝓝ᶠ(a) := rfl

lemma normalOrder_ofCrAnFieldOpList (φs : List 𝓕.CrAnFieldOp) :
    𝓝(ofCrAnFieldOpList φs) = normalOrderSign φs • ofCrAnFieldOpList (normalOrderList φs) := by
  rw [ofCrAnFieldOpList, normalOrder_eq_ι_normalOrderF, normalOrderF_ofCrAnListF]
  rfl

@[simp]
lemma normalOrder_one_eq_one : normalOrder (𝓕 := 𝓕) 1 = 1 := by
  have h1 : 1 = ofCrAnFieldOpList (𝓕 := 𝓕) [] := by simp [ofCrAnFieldOpList]
  rw [h1]
  rw [normalOrder_ofCrAnFieldOpList]
  simp

@[simp]
lemma normalOrder_ofFieldOpList_nil : normalOrder (𝓕 := 𝓕) (ofFieldOpList []) = 1 := by
  rw [ofFieldOpList]
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [ofFieldOpListF_nil]
  change normalOrder (𝓕 := 𝓕) 1 = _
  simp

@[simp]
lemma normalOrder_ofCrAnFieldOpList_nil : normalOrder (𝓕 := 𝓕) (ofCrAnFieldOpList []) = 1 := by
  rw [normalOrder_ofCrAnFieldOpList]
  simp only [normalOrderSign_nil, normalOrderList_nil, one_smul]
  rfl

lemma ofCrAnFieldOpList_eq_normalOrder (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnFieldOpList (normalOrderList φs) = normalOrderSign φs • 𝓝(ofCrAnFieldOpList φs) := by
  rw [normalOrder_ofCrAnFieldOpList, smul_smul, normalOrderSign, Wick.koszulSign_mul_self,
    one_smul]

lemma normalOrder_normalOrder_mid (a b c : 𝓕.FieldOpAlgebra) :
    𝓝(a * b * c) = 𝓝(a * 𝓝(b) * c) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [← map_mul]
  rw [normalOrder_eq_ι_normalOrderF]
  rw [normalOrderF_normalOrderF_mid]
  rfl

lemma normalOrder_normalOrder_left (a b : 𝓕.FieldOpAlgebra) :
    𝓝(a * b) = 𝓝(𝓝(a) * b) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [← map_mul]
  rw [normalOrder_eq_ι_normalOrderF]
  rw [normalOrderF_normalOrderF_left]
  rfl

lemma normalOrder_normalOrder_right (a b : 𝓕.FieldOpAlgebra) :
    𝓝(a * b) = 𝓝(a * 𝓝(b)) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [← map_mul]
  rw [normalOrder_eq_ι_normalOrderF]
  rw [normalOrderF_normalOrderF_right]
  rfl

lemma normalOrder_normalOrder (a : 𝓕.FieldOpAlgebra) : 𝓝(𝓝(a)) = 𝓝(a) := by
  trans 𝓝(𝓝(a) * 1)
  · simp
  · rw [← normalOrder_normalOrder_left]
    simp

/-!

## mul anpart and crpart
-/

lemma normalOrder_mul_anPart (φ : 𝓕.FieldOp) (a : 𝓕.FieldOpAlgebra) :
    𝓝(a * anPart φ) = 𝓝(a) * anPart φ := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  rw [anPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_mul_anPartF]
  rfl

lemma crPart_mul_normalOrder (φ : 𝓕.FieldOp) (a : 𝓕.FieldOpAlgebra) :
    𝓝(crPart φ * a) = crPart φ * 𝓝(a) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  rw [crPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_crPartF_mul]
  rfl

/-!

### Normal order and super commutes

-/

@[simp]
lemma normalOrder_superCommute_eq_zero (a b : 𝓕.FieldOpAlgebra) :
    𝓝([a, b]ₛ) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [superCommute_eq_ι_superCommuteF, normalOrder_eq_ι_normalOrderF]
  simp

@[simp]
lemma normalOrder_superCommute_left_eq_zero (a b c: 𝓕.FieldOpAlgebra) :
    𝓝([a, b]ₛ * c) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [superCommute_eq_ι_superCommuteF, ← map_mul, normalOrder_eq_ι_normalOrderF]
  simp

@[simp]
lemma normalOrder_superCommute_right_eq_zero (a b c: 𝓕.FieldOpAlgebra) :
    𝓝(c * [a, b]ₛ) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [superCommute_eq_ι_superCommuteF, ← map_mul, normalOrder_eq_ι_normalOrderF]
  simp

@[simp]
lemma normalOrder_superCommute_mid_eq_zero (a b c d : 𝓕.FieldOpAlgebra) :
    𝓝(a * [c, d]ₛ * b) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  obtain ⟨d, rfl⟩ := ι_surjective d
  rw [superCommute_eq_ι_superCommuteF, ← map_mul, ← map_mul, normalOrder_eq_ι_normalOrderF]
  simp

/-!

### Swapping terms in a normal order.

-/

lemma normalOrder_ofFieldOp_ofFieldOp_swap (φ φ' : 𝓕.FieldOp) :
    𝓝(ofFieldOp φ * ofFieldOp φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝(ofFieldOp φ' * ofFieldOp φ) := by
  rw [ofFieldOp_mul_ofFieldOp_eq_superCommute]
  simp

lemma normalOrder_ofCrAnFieldOp_ofCrAnFieldOpList (φ : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) : 𝓝(ofCrAnFieldOp φ * ofCrAnFieldOpList φs) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓝(ofCrAnFieldOpList φs * ofCrAnFieldOp φ) := by
  rw [← ofCrAnFieldOpList_singleton, ofCrAnFieldOpList_mul_ofCrAnFieldOpList_eq_superCommute]
  simp

lemma normalOrder_ofCrAnFieldOp_ofFieldOpList_swap (φ : 𝓕.CrAnFieldOp) (φ' : List 𝓕.FieldOp) :
    𝓝(ofCrAnFieldOp φ * ofFieldOpList φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓝(ofFieldOpList φ' * ofCrAnFieldOp φ) := by
  rw [← ofCrAnFieldOpList_singleton, ofCrAnFieldOpList_mul_ofFieldOpList_eq_superCommute]
  simp

lemma normalOrder_anPart_ofFieldOpList_swap (φ : 𝓕.FieldOp) (φ' : List 𝓕.FieldOp) :
    𝓝(anPart φ * ofFieldOpList φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝(ofFieldOpList φ' * anPart φ) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPart_position, instCommGroup.eq_1]
    rw [normalOrder_ofCrAnFieldOp_ofFieldOpList_swap]
    rfl
  | .outAsymp φ =>
    simp only [anPart_posAsymp, instCommGroup.eq_1]
    rw [normalOrder_ofCrAnFieldOp_ofFieldOpList_swap]
    rfl

lemma normalOrder_ofFieldOpList_anPart_swap (φ : 𝓕.FieldOp) (φ' : List 𝓕.FieldOp) :
    𝓝(ofFieldOpList φ' * anPart φ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝(anPart φ * ofFieldOpList φ') := by
  rw [normalOrder_anPart_ofFieldOpList_swap]
  simp [smul_smul, FieldStatistic.exchangeSign_mul_self]

lemma normalOrder_ofFieldOpList_mul_anPart_swap (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    𝓝(ofFieldOpList φs) * anPart φ = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓝(anPart φ * ofFieldOpList φs) := by
  rw [← normalOrder_mul_anPart]
  rw [normalOrder_ofFieldOpList_anPart_swap]

lemma anPart_mul_normalOrder_ofFieldOpList_eq_superCommute (φ : 𝓕.FieldOp)
    (φs' : List 𝓕.FieldOp) : anPart φ * 𝓝(ofFieldOpList φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • 𝓝(ofFieldOpList φs' * anPart φ) +
    [anPart φ, 𝓝(ofFieldOpList φs')]ₛ := by
  rw [anPart, ofFieldOpList, normalOrder_eq_ι_normalOrderF, ← map_mul]
  rw [anPartF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF]
  simp only [instCommGroup.eq_1, map_add, map_smul]
  rfl

/-!

## Super commutators with a normal ordered term as sums

-/

/--
For a `CrAnFieldOp` `φ` and a list of `CrAnFieldOp`s `φs`, the following is true
`[φ, 𝓝(φ₀…φₙ)]ₛ = ∑ i, 𝓢(φ, φ₀…φᵢ₋₁) • [φ, φᵢ]ₛ * 𝓝(φ₀…φᵢ₋₁φᵢ₊₁…φₙ)`.

The proof of this result ultimetly depends on
- `superCommuteF_ofCrAnListF_ofFieldOpListF_eq_sum`
- `normalOrderSign_eraseIdx`
-/
lemma ofCrAnFieldOp_superCommute_normalOrder_ofCrAnFieldOpList_sum (φ : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) : [ofCrAnFieldOp φ, 𝓝(ofCrAnFieldOpList φs)]ₛ = ∑ n : Fin φs.length,
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) • [ofCrAnFieldOp φ, ofCrAnFieldOp φs[n]]ₛ
    * 𝓝(ofCrAnFieldOpList (φs.eraseIdx n)) := by
  rw [normalOrder_ofCrAnFieldOpList, map_smul]
  rw [superCommute_ofCrAnFieldOp_ofCrAnFieldOpList_eq_sum, Finset.smul_sum,
    sum_normalOrderList_length]
  congr
  funext n
  simp only [instCommGroup.eq_1, List.get_eq_getElem, normalOrderList_get_normalOrderEquiv,
    normalOrderList_eraseIdx_normalOrderEquiv, Algebra.smul_mul_assoc, Fin.getElem_fin]
  rw [ofCrAnFieldOpList_eq_normalOrder, mul_smul_comm, smul_smul, smul_smul]
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
  · erw [superCommute_diff_statistic hs]
    simp

lemma ofCrAnFieldOp_superCommute_normalOrder_ofFieldOpList_sum (φ : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.FieldOp) :
    [ofCrAnFieldOp φ, 𝓝(ofFieldOpList φs)]ₛ = ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    [ofCrAnFieldOp φ, ofFieldOp φs[n]]ₛ * 𝓝(ofFieldOpList (φs.eraseIdx n)) := by
  conv_lhs =>
    rw [ofFieldOpList_eq_sum, map_sum, map_sum]
    enter [2, s]
    rw [ofCrAnFieldOp_superCommute_normalOrder_ofCrAnFieldOpList_sum, CrAnSection.sum_over_length]
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
  rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← ofFieldOp_eq_sum, ← ofFieldOpList_eq_sum]

/--
The commutor of the annihilation part of a field operator with a normal ordered list of field
operators can be decomponsed into the sum of the commutators of the annihilation part with each
element of the list of field operators, i.e.
`[anPart φ, 𝓝(φ₀…φₙ)]ₛ= ∑ i, 𝓢(φ, φ₀…φᵢ₋₁) • [anPart φ, φᵢ]ₛ * 𝓝(φ₀…φᵢ₋₁φᵢ₊₁…φₙ)`.
-/
lemma anPart_superCommute_normalOrder_ofFieldOpList_sum (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [anPart φ, 𝓝(ofFieldOpList φs)]ₛ = ∑ n : Fin φs.length, 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) •
    [anPart φ, ofFieldOpF φs[n]]ₛ * 𝓝(ofFieldOpList (φs.eraseIdx n)) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPart_position, instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc]
    rw [ofCrAnFieldOp_superCommute_normalOrder_ofFieldOpList_sum]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod,
      Fin.getElem_fin, Algebra.smul_mul_assoc]
    rfl
  | .outAsymp φ =>
    simp only [anPart_posAsymp, instCommGroup.eq_1, Fin.getElem_fin, Algebra.smul_mul_assoc]
    rw [ofCrAnFieldOp_superCommute_normalOrder_ofFieldOpList_sum]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod,
      Fin.getElem_fin, Algebra.smul_mul_assoc]
    rfl

/-!

## Multiplying with normal ordered terms

-/
/--
Within a proto-operator algebra we have that
`anPartF φ * 𝓝(φ₀φ₁…φₙ) = 𝓝((anPart φ)φ₀φ₁…φₙ) + [anpart φ, 𝓝(φ₀φ₁…φₙ)]ₛ`.
-/
lemma anPart_mul_normalOrder_ofFieldOpList_eq_superCommute_reorder (φ : 𝓕.FieldOp)
    (φs : List 𝓕.FieldOp) : anPart φ * 𝓝(ofFieldOpList φs) =
    𝓝(anPart φ * ofFieldOpList φs) + [anPart φ, 𝓝(ofFieldOpList φs)]ₛ := by
  rw [anPart_mul_normalOrder_ofFieldOpList_eq_superCommute]
  simp only [instCommGroup.eq_1, add_left_inj]
  rw [normalOrder_anPart_ofFieldOpList_swap]

/--
Within a proto-operator algebra we have that
`φ * 𝓝ᶠ(φ₀φ₁…φₙ) = 𝓝ᶠ(φφ₀φ₁…φₙ) + [anpart φ, 𝓝ᶠ(φ₀φ₁…φₙ)]ₛca`.
-/
lemma ofFieldOp_mul_normalOrder_ofFieldOpList_eq_superCommute (φ : 𝓕.FieldOp)
    (φs : List 𝓕.FieldOp) : ofFieldOp φ * 𝓝(ofFieldOpList φs) =
    𝓝(ofFieldOp φ * ofFieldOpList φs) + [anPart φ, 𝓝(ofFieldOpList φs)]ₛ := by
  conv_lhs => rw [ofFieldOp_eq_crPart_add_anPart]
  rw [add_mul, anPart_mul_normalOrder_ofFieldOpList_eq_superCommute_reorder, ← add_assoc,
    ← crPart_mul_normalOrder, ← map_add]
  conv_lhs =>
    lhs
    rw [← add_mul, ← ofFieldOp_eq_crPart_add_anPart]

/-- In the expansion of `ofFieldOpF φ * normalOrderF (ofFieldOpListF φs)` the element
  of `𝓞.A` associated with contracting `φ` with the (optional) `n`th element of `φs`. -/
noncomputable def contractStateAtIndex (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (n : Option (Fin φs.length)) : 𝓕.FieldOpAlgebra :=
  match n with
  | none => 1
  | some n => 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (φs.take n)) • [anPart φ, ofFieldOp φs[n]]ₛ

/--
For a field specification `𝓕`, the following relation holds in the algebra `𝓕.FieldOpAlgebra`,
`φ * 𝓝(φ₀φ₁…φₙ) = 𝓝(φφ₀φ₁…φₙ) + ∑ i, (𝓢(φ,φ₀φ₁…φᵢ₋₁) • [anPartF φ, φᵢ]ₛ) * 𝓝(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)`.

The proof of this ultimently depends on :
- `ofCrAnFieldOp_superCommute_normalOrder_ofCrAnFieldOpList_sum`
-/
lemma ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    ofFieldOp φ * 𝓝(ofFieldOpList φs) =
    ∑ n : Option (Fin φs.length), contractStateAtIndex φ φs n *
    𝓝(ofFieldOpList (optionEraseZ φs φ n)) := by
  rw [ofFieldOp_mul_normalOrder_ofFieldOpList_eq_superCommute]
  rw [anPart_superCommute_normalOrder_ofFieldOpList_sum]
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
lemma ofFieldOpList_normalOrder_insert (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (k : Fin φs.length.succ) : 𝓝(ofFieldOpList (φ :: φs)) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs.take k) • 𝓝(ofFieldOpList (φs.insertIdx k φ)) := by
  have hl : φs.insertIdx k φ = φs.take k ++ [φ] ++ φs.drop k := by
    rw [HepLean.List.insertIdx_eq_take_drop]
    simp
  rw [hl]
  rw [ofFieldOpList_append, ofFieldOpList_append]
  rw [ofFieldOpList_mul_ofFieldOpList_eq_superCommute, add_mul]
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one, ofList_singleton, Algebra.smul_mul_assoc,
    map_add, map_smul, normalOrder_superCommute_left_eq_zero, add_zero, smul_smul,
    exchangeSign_mul_self_swap, one_smul]
  rw [← ofFieldOpList_append, ← ofFieldOpList_append]
  simp

/-!

## The normal ordering of a product of two states

-/

@[simp]
lemma normalOrder_crPart_mul_crPart (φ φ' : 𝓕.FieldOp) :
    𝓝(crPart φ * crPart φ') = crPart φ * crPart φ' := by
  rw [crPart, crPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_crPartF_mul_crPartF]

@[simp]
lemma normalOrder_anPart_mul_anPart (φ φ' : 𝓕.FieldOp) :
    𝓝(anPart φ * anPart φ') = anPart φ * anPart φ' := by
  rw [anPart, anPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_anPartF_mul_anPartF]

@[simp]
lemma normalOrder_crPart_mul_anPart (φ φ' : 𝓕.FieldOp) :
    𝓝(crPart φ * anPart φ') = crPart φ * anPart φ' := by
  rw [crPart, anPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_crPartF_mul_anPartF]

@[simp]
lemma normalOrder_anPart_mul_crPart (φ φ' : 𝓕.FieldOp) :
    𝓝(anPart φ * crPart φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ := by
  rw [anPart, crPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_anPartF_mul_crPartF]
  simp

lemma normalOrder_ofFieldOp_mul_ofFieldOp (φ φ' : 𝓕.FieldOp) : 𝓝(ofFieldOp φ * ofFieldOp φ') =
    crPart φ * crPart φ' + 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • (crPart φ' * anPart φ) +
    crPart φ * anPart φ' + anPart φ * anPart φ' := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, normalOrder_eq_ι_normalOrderF,
    normalOrderF_ofFieldOpF_mul_ofFieldOpF]
  rfl

end FieldOpAlgebra
end FieldSpecification
