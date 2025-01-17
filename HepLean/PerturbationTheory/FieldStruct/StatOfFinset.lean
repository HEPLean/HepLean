/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Contractions

/-!

# Sign associated with a contraction


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

open HepLean.List
open FieldStatistic
open ContractionsNat
/-!

## Field statistics associated with a finite set.

-/


def fieldStatOfFinset {n : ℕ} (f : Fin n → 𝓕.States) (a : Finset (Fin n)) : FieldStatistic :=
  𝓕 |>ₛ (a.sort (· ≤ ·)).map f

lemma fieldStatOfFinset_singleton {n : ℕ} (f : Fin n → 𝓕.States) (i : Fin n) :
    fieldStatOfFinset f {i} = 𝓕 |>ₛ f i := by
  simp [fieldStatOfFinset]

lemma fieldStatOfFinset_finset_map  {n m : ℕ} (i : Fin m → Fin n) (hi : Function.Injective i)
    (f : Fin n → 𝓕.States) (a : Finset (Fin m)) :
    fieldStatOfFinset (f ∘ i) a = fieldStatOfFinset f (a.map ⟨i, hi⟩) := by
  simp [fieldStatOfFinset]
  apply FieldStatistic.ofList_perm
  rw [← List.map_map]
  refine List.Perm.map f ?_
  apply List.perm_of_nodup_nodup_toFinset_eq
  · refine (List.nodup_map_iff_inj_on ?_).mpr ?_
    exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) a
    simp
    intro x hx y hy
    exact fun a => hi a
  · exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) (Finset.map { toFun := i, inj' := hi } a)
  · ext a
    simp

lemma fieldStatOfFinset_insert (φs : List 𝓕.States) (a : Finset (Fin φs.length))
    (i : Fin φs.length) (h : i ∉ a) :
    fieldStatOfFinset φs.get (Insert.insert i a) = (𝓕 |>ₛ φs[i]) * fieldStatOfFinset φs.get a := by
  simp [fieldStatOfFinset]
  rw [← ofList_cons_eq_mul]
  have h1 : (φs[↑i] :: List.map φs.get (Finset.sort (fun x1 x2 => x1 ≤ x2) a))
     = List.map φs.get (i :: Finset.sort (fun x1 x2 => x1 ≤ x2) a) := by
     simp
  erw [h1]
  apply ofList_perm
  refine List.Perm.map φs.get ?_
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) (Insert.insert i a)
  · simp
    exact h
  intro a
  simp

lemma fieldStatOfFinset_erase (φs : List 𝓕.States) (a : Finset (Fin φs.length))
    (i : Fin φs.length) (h : i ∈  a) :
    fieldStatOfFinset φs.get (a.erase i) = (𝓕 |>ₛ φs[i]) * fieldStatOfFinset φs.get a := by
  have ha : a = Insert.insert i (a.erase i) := by
    exact Eq.symm (Finset.insert_erase h)
  conv_rhs => rw [ha]
  rw [fieldStatOfFinset_insert]
  rw [← mul_assoc]
  simp
  simp

lemma fieldStatOfFinset_eq_prod (φs : List 𝓕.States) (a : Finset (Fin φs.length)) :
    fieldStatOfFinset φs.get a = ∏ (i : Fin φs.length), if i ∈ a then (𝓕 |>ₛ φs[i]) else 1 := by
  rw [fieldStatOfFinset]
  rw [ofList_map_eq_finset_prod]
  congr
  funext i
  simp
  exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) a

lemma fieldStatOfFinset_union (φs : List 𝓕.States) (a b : Finset (Fin φs.length)) :
    fieldStatOfFinset φs.get a * fieldStatOfFinset φs.get b =
    fieldStatOfFinset φs.get ((a ∪ b) \ (a ∩ b)):= by
  rw [fieldStatOfFinset_eq_prod, fieldStatOfFinset_eq_prod, fieldStatOfFinset_eq_prod]
  rw [← Finset.prod_mul_distrib]
  congr
  funext x
  simp
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]

lemma fieldStatOfFinset_union_disjoint (φs : List 𝓕.States) (a b : Finset (Fin φs.length))
    (h : Disjoint a b):
    fieldStatOfFinset φs.get a * fieldStatOfFinset φs.get b =
    fieldStatOfFinset φs.get ((a ∪ b)):= by
  rw [fieldStatOfFinset_union]
  rw [Finset.disjoint_iff_inter_eq_empty.mp h]
  simp

lemma fieldStatOfFinset_of_insertListLiftFinset (φ : 𝓕.States) (φs : List 𝓕.States) (i : Fin φs.length.succ)
    (a : Finset (Fin φs.length)) :
    fieldStatOfFinset (φs.insertIdx i φ).get (insertListLiftFinset φ i a) =
    fieldStatOfFinset φs.get a := by
  simp [fieldStatOfFinset]
  congr 1
  rw [get_eq_insertIdx_succAbove φ _ i]
  rw [← List.map_map, ← List.map_map]
  congr
  have h1 : (List.map (⇑(finCongr  (insertIdx_length_fin φ φs i).symm)) (List.map i.succAbove (Finset.sort (fun x1 x2 => x1 ≤ x2) a))).Sorted (· ≤ · ):= by
    simp
    refine
      fin_list_sorted_monotone_sorted (Finset.sort (fun x1 x2 => x1 ≤ x2) a) ?hl
        (⇑(finCongr (Eq.symm (insertIdx_length_fin φ φs i))) ∘ i.succAbove) ?hf
    exact Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) a
    refine StrictMono.comp (fun ⦃a b⦄ a => a) ?hf.hf
    exact Fin.strictMono_succAbove i
  have h2 : (List.map (⇑(finCongr  (insertIdx_length_fin φ φs i).symm)) (List.map i.succAbove (Finset.sort (fun x1 x2 => x1 ≤ x2) a))).Nodup := by
    simp
    refine List.Nodup.map ?_ ?_
    apply (Equiv.comp_injective _ (finCongr _)).mpr
    exact Fin.succAbove_right_injective
    exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) a
  have h3 : (List.map (⇑(finCongr  (insertIdx_length_fin φ φs i).symm)) (List.map i.succAbove (Finset.sort (fun x1 x2 => x1 ≤ x2) a))).toFinset
      =  (insertListLiftFinset φ i a)  := by
    ext b
    simp
    rcases insert_fin_eq_self φ i b with hk | hk
    · subst hk
      simp
      intro x hx
      refine Fin.ne_of_val_ne ?h.inl.h
      simp
      rw [@Fin.val_eq_val]
      exact Fin.succAbove_ne i x
    · obtain ⟨k, hk⟩ := hk
      subst hk
      simp
      rw [succAbove_mem_insertListLiftFinset]
      apply Iff.intro
      · intro h
        obtain ⟨x, hx⟩ := h
        simp [Fin.ext_iff] at hx
        rw [@Fin.val_eq_val] at hx
        rw [Function.Injective.eq_iff] at hx
        rw [← hx.2]
        exact hx.1
        exact Fin.succAbove_right_injective
      · intro h
        use k
  rw [← h3]
  symm
  rw [(List.toFinset_sort (· ≤ ·) h2).mpr h1]

lemma fieldStatOfFinset_eq_one_of_isGradedObeying (φs : List 𝓕.States)
    (a : Finset (Fin φs.length)) (c : ContractionsNat φs.length) (hg : IsGradedObeying φs c)
    (hnon : ∀ i, c.getDual? i = none → i ∉ a)
    (hsom : ∀ i, (h : (c.getDual? i).isSome) → i ∈ a → (c.getDual? i).get h ∈ a) :
    fieldStatOfFinset φs.get a = 1 := by
  rw [fieldStatOfFinset_eq_prod]
  let e2 : Fin φs.length ≃ {x // (c.getDual? x).isSome} ⊕ {x //  ¬ (c.getDual? x).isSome}  := by
    exact (Equiv.sumCompl fun a => (c.getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp
  conv_lhs =>
    enter [2, 2, x]
    simp [e2]
    rw [if_neg (hnon x.1 (by simpa using x.2))]
  simp [e2]
  rw [← c.sigmaConstrainedEquiv.prod_comp]
  erw [Finset.prod_sigma]
  apply Fintype.prod_eq_one _
  intro x
  rw [prod_finset_eq_mul_fst_snd]
  simp [sigmaConstrainedEquiv]
  split
  · split
    erw [hg x]
    simp
    rename_i h1 h2
    have hsom' := hsom (c.sndFieldOfContract x) (by simp) h1
    simp at hsom'
    exact False.elim (h2 hsom')
  · split
    rename_i h1 h2
    have hsom' := hsom (c.fstFieldOfContract x) (by simp) h2
    simp at hsom'
    exact False.elim (h1 hsom')
    rfl

end FieldStruct
