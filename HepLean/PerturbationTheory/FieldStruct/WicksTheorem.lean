/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Contractions
import HepLean.PerturbationTheory.FieldStruct.TimeOrder
import HepLean.Mathematics.List.InsertIdx
/-!

# Contractions


-/

namespace FieldStruct
variable {𝓕 : FieldStruct} {𝓞 : 𝓕.OperatorAlgebra}
open CrAnAlgebra
open StateAlgebra
open OperatorAlgebra
open HepLean.List
open ContractionsNat
open FieldStatistic

def timeContractionsofList (φs : List 𝓕.States) (c : ContractionsNat φs.length) :
    𝓞.A := 0

lemma timeContractionsofList_mem_center (φs : List 𝓕.States) (c : ContractionsNat φs.length) :
    timeContractionsofList φs c ∈ Subalgebra.center ℂ 𝓞.A := by
  sorry

lemma coeff_rewrite (φs : List 𝓕.States)  (k : Fin φs.length)
    (c : ContractionsNat (φs.eraseIdx k).length) :
    let c' : ContractionsNat φs.length := congr (by simp [eraseIdx_length]) (
          ((extractEquiv (finCongr (by simp [eraseIdx_length]) k)).symm ⟨c, none⟩))
    (List.take (c.uncontractedListOrderPos (finCongr (by simp [eraseIdx_length]) k))
    (List.map (φs.eraseIdx ↑k).get c.uncontractedList)) =
    (List.take (c'.uncontractedListOrderPos k.castSucc)
    (List.map φs.get c'.uncontractedList)) := by
  simp
  rw [← List.map_take, ← List.map_take]
  have h1 : (φs.eraseIdx ↑k).get = φs.get ∘ finCongr (by simp [eraseIdx_length])  ∘
      (finCongr (by simp [eraseIdx_length]) k).succAbove := by
    funext x
    simp [Fin.succAbove, Fin.lt_def, List.getElem_eraseIdx]
    split
    · simp
    · simp
  rw [h1]
  rw [← List.map_map]
  apply congrArg
  rw [take_uncontractedListOrderPos_eq_filter_sort]
  simp
  trans (Finset.sort (fun x1 x2 => x1 ≤ x2) (Finset.filter (fun x => ↑x < k.1)
    (c.uncontracted.map ((finCongr (by simp [eraseIdx_length]) k).succAboveEmb.trans
    (finCongr (by simp [eraseIdx_length])).toEmbedding))))
  · let l : List (Fin φs.length) := (Finset.sort (fun x1 x2 => x1 ≤ x2) (Finset.filter (fun x => x.1 < k.1) c.uncontracted)).map
       ((finCongr (by simp [eraseIdx_length])) ∘ (Fin.cast (by  simp [eraseIdx_length]) k).succAbove)
    have l_sorted : List.Sorted (fun x1 x2 => x1 ≤ x2) l := by
      apply fin_list_sorted_monotone_sorted
      exact Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) _
      refine StrictMono.comp (fun ⦃a b⦄ a => a) ?hf.hf
      exact Fin.strictMono_succAbove _
    have l_nodup : l.Nodup := by
      refine List.Nodup.map ?_ ?_
      · refine (Equiv.comp_injective _ (finCongr _)).mpr ?_
        exact Fin.succAbove_right_injective
      · exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) _
    have hl : l = (Finset.sort (fun x1 x2 => x1 ≤ x2) l.toFinset) := by
      symm
      rw [List.toFinset_sort]
      exact l_sorted
      exact l_nodup
    change l = _
    rw [hl]
    apply congrArg
    ext a
    simp [l]
    apply Iff.intro
    · intro ha
      obtain ⟨b, ⟨hb1, hb2⟩, hb3⟩ := ha
      apply And.intro
      · use b
      · rw [Fin.lt_def]
        simp [Fin.ext_iff, Fin.succAbove, Fin.lt_def, hb2] at hb3
        omega
    · intro ha
      obtain ⟨⟨b, hb1, hb2⟩, hb3⟩ := ha
      use b
      simp [hb1, hb2]
      simp [Fin.ext_iff, Fin.succAbove, Fin.lt_def, hb2] at hb2
      split at hb2
      · omega
      · simp at hb2
        omega
  · rw [take_uncontractedListOrderPos_eq_filter_sort]
    apply congrArg
    rw [congr_uncontracted, extractEquiv]
    simp
    rw [insert_none_uncontracted]
    simp
    rw [Finset.filter_insert]
    simp
    apply congrArg
    simp [Finset.map_map]



lemma crAnF_normalOrder_optionEraseZ_none  (φs : List 𝓕.States)  (k : Fin φs.length)
    (c : ContractionsNat (φs.eraseIdx k).length) :
    let c' : ContractionsNat φs.length := congr (by simp [eraseIdx_length])
          ((extractEquiv (finCongr (by simp [eraseIdx_length]) k)).symm ⟨c, none⟩)
    𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map (φs.eraseIdx k).get)
      (φs[k]) (uncontractedStatesEquiv (φs.eraseIdx k) c none)))) =
    𝓢(𝓕 |>ₛ φs[k], 𝓕 |>ₛ (List.take (c'.uncontractedListOrderPos k.castSucc)
    (List.map φs.get c'.uncontractedList))) •
    𝓞.crAnF (normalOrder (ofStateList (List.map φs.get c'.uncontractedList))) := by
  simp
  erw [← coeff_rewrite]
  simp [uncontractedStatesEquiv, optionEraseZ]
  rw [congr_uncontractedList]
  rw [uncontractedList_extractEquiv_symm_none]
  rw [crAnF_ofState_normalOrder_insert _ _ ⟨(c.uncontractedListOrderPos (finCongr (by simp [eraseIdx_length]) k)), by simp⟩]
  congr
  · simp
    erw [orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx]
    simp
    rw [insertIdx_map]
    congr 1
    simp
    intro a ha
    rw [List.getElem_eraseIdx]
    simp [Fin.succAbove, Fin.lt_def]
    split
    · simp
    · simp

lemma crAnF_normalOrder_optionEraseZ_some  (φs : List 𝓕.States)  (k : Fin φs.length)
    (c : ContractionsNat (φs.eraseIdx k).length) (i :  { x // x ∈ c.uncontracted }) :
    𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (List.map (φs.eraseIdx k).get c.uncontractedList)
      (φs[k]) ((ContractionsNat.uncontractedStatesEquiv (φs.eraseIdx k) c) (some i))))) =
    𝓞.crAnF (normalOrder (ofStateList
      (List.map φs.get (ContractionsNat.congr (by simp [eraseIdx_length])
      ((ContractionsNat.extractEquiv (finCongr (by simp [eraseIdx_length]) k)).symm
      ⟨c, (some i)⟩)).uncontractedList))) := by
  simp [optionEraseZ, uncontractedStatesEquiv]
  congr
  rw [congr_uncontractedList]
  rw [uncontractedList_extractEquiv_symm_some]
  simp
  congr
  funext x
  simp
  rw [List.getElem_eraseIdx]
  simp [ Fin.succAbove, Fin.lt_def]
  split
  · simp
  · simp

def insertTimeOrderCoeff (φs : List 𝓕.States)  (k : Fin φs.length)
    (c : ContractionsNat φs.length) (i :  Option { x // x ∈ c.uncontracted }) : ℂ :=
  match i with
  | none => 𝓢(𝓕 |>ₛ φs[k], 𝓕 |>ₛ (List.take (uncontractedInsertPos φs k c)
        (List.map (φs.eraseIdx ↑k).get c.uncontractedList)))
  | some i => 1

lemma crAnF_normalOrder_optionEraseZ  (φs : List 𝓕.States)  (k : Fin φs.length)
    (c : ContractionsNat (φs.eraseIdx k).length)
    (i : Option { x // x ∈ c.uncontracted }) :
    𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (List.map (φs.eraseIdx k).get c.uncontractedList)
      (φs[k]) ((ContractionsNat.uncontractedStatesEquiv (φs.eraseIdx k) c) i)))) =
    insertTimeOrderCoeff φs k c i •
    𝓞.crAnF (normalOrder (ofStateList
      (List.map φs.get (ContractionsNat.congr (by simp [eraseIdx_length])
          ((ContractionsNat.extractEquiv (finCongr (by simp [eraseIdx_length]) k)).symm ⟨c, i⟩)).uncontractedList))) := by
    sorry

theorem wicks_theorem_cons (φ : 𝓕.States) (φs : List 𝓕.States)
      (ih :  𝓞.crAnF (ofStateAlgebra (timeOrder (ofList (eraseMaxTimeField φ φs)))) =
      ∑ (c : ContractionsNat (eraseMaxTimeField φ φs).length),
      timeContractionsofList (eraseMaxTimeField φ φs) c
      * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map (eraseMaxTimeField φ φs).get)))):
      𝓞.crAnF (ofStateAlgebra (timeOrder (ofList (φ :: φs)))) = ∑ (c : ContractionsNat (φ :: φs).length),
      timeContractionsofList (φ :: φs) c
      * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map (φ :: φs).get))) := by
  conv_lhs =>
    rw [timeOrder_eq_maxTimeField_mul]
    simp only [Algebra.smul_mul_assoc, map_smul, ofStateAlgebra_ofState]
    rw [map_mul, ofStateAlgebra_ofState, map_mul, ih]
    rw [Finset.mul_sum]
    enter [2, 2, c]
    rw [← mul_assoc]
    rw [Subalgebra.mem_center_iff.mp (timeContractionsofList_mem_center _ _), mul_assoc]
    rw [← map_mul, crAnF_ofState_mul_normalOrder_ofStatesList_eq_sum,
      ContractionsNat.uncontractedStatesEquiv_list_sum, Finset.mul_sum]
  /-
  Every term has the following coefficents:
  - 𝓢(𝓕 |>ₛ (maxTimeField φ φs), 𝓕 |>ₛ (List.take (maxTimeFieldPos φ φs) (φ :: φs)))
  - (contractMemList (maxTimeField φ φs) (List.map (eraseMaxTimeField φ φs).get c.uncontractedList)
        ((uncontractedStatesEquiv (eraseMaxTimeField φ φs) c) i)
  Plus the one from normal ordering.
  If we let k := (maxTimeField φ φs)  and replace φ :: φs with φs these simplfy down to:
  - 𝓢(𝓕 |>ₛ φs[k], 𝓕 |>ₛ List.take k φs)
  - (contractMemList φs[k] (List.map (φs.eraseIdx k).get c.uncontractedList)
        ((uncontractedStatesEquiv (φs.eraseIdx k) c) i)
    which is
    - 1 if i = none
    and
    - 𝓢(𝓕 |>ₛ φs[k], 𝓕 |>ₛ ((List.map (φs.eraseIdx k).get c.uncontractedList).take
        ((uncontractedStatesEquiv (φs.eraseIdx k) c) i))) •
        ... if i is some
  The term ((List.map (φs.eraseIdx k).get c.uncontractedList).take
        ((uncontractedStatesEquiv (φs.eraseIdx k) c) i)) needs to be converted to c'
  Then from the normalization we get:
  - 𝓢(𝓕 |>ₛ φs[k], 𝓕 |>ₛ (List.take (c'.uncontractedListOrderPos k.castSucc)
    (List.map φs.get c'.uncontractedList))) if i = none
  - 1 if i is some

  -/
  conv_lhs =>
    enter [2]






  sorry
end FieldStruct
