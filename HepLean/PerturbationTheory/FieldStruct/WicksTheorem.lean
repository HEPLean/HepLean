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

lemma crAnF_normalOrder_optionEraseZ_none  (φs : List 𝓕.States)  (k : Fin φs.length)
    (c : ContractionsNat (φs.eraseIdx k).length) :
    𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map (φs.eraseIdx k).get)
      (φs[k]) (uncontractedStatesEquiv (φs.eraseIdx k) c none)))) =
    𝓢(𝓕 |>ₛ φs[k], 𝓕 |>ₛ (List.take (c.uncontractedListOrderPos (finCongr (by simp [eraseIdx_length]) k))
      (List.map (φs.eraseIdx ↑k).get c.uncontractedList))) •
    𝓞.crAnF (normalOrder (ofStateList
      (List.map φs.get (congr (by simp [eraseIdx_length])
          ((extractEquiv (finCongr (by simp [eraseIdx_length]) k)).symm ⟨c, none⟩)).uncontractedList))) := by
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
      ((ContractionsNat.extractEquiv (finCongr (by simp [eraseIdx_length]) k)).symm ⟨c, (some i)⟩)).uncontractedList))) := by
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
    (c : ContractionsNat (φs.eraseIdx k).length) (i :  Option { x // x ∈ c.uncontracted }) :
    ℂ :=
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
  conv_lhs =>
    enter [2]






  sorry
end FieldStruct
