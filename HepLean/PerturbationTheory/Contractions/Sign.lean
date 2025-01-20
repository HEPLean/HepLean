/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.InsertList

/-!

# Sign associated with a contraction

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List
open FieldStatistic

def signFinset (c : ContractionsNat n) (i1 i2 : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i1 < i ∧ i < i2 ∧
  (c.getDual? i = none ∨ ∀ (h : (c.getDual? i).isSome), i1 < (c.getDual? i).get h))

lemma signFinset_insertList_none (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (i1 i2 : Fin φs.length) :
      (c.insertList φ φs i none).signFinset (finCongr (insertIdx_length_fin φ φs i).symm
      (i.succAbove i1)) (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove i2)) =
    if i.succAbove i1 < i ∧ i < i.succAbove i2 then
      Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
      (insertListLiftFinset φ i (c.signFinset i1 i2))
    else
      (insertListLiftFinset φ i (c.signFinset i1 i2)) := by
  ext k
  rcases insert_fin_eq_self φ i k with hk | hk
  · subst hk
    conv_lhs => simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter,
      Finset.mem_univ,
      insertList_none_getDual?_self, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff,
      or_self, and_true, true_and]
    by_cases h : i.succAbove i1 < i ∧ i < i.succAbove i2
    · simp [h, Fin.lt_def]
    · simp only [Nat.succ_eq_add_one, h, ↓reduceIte, self_not_mem_insertListLiftFinset, iff_false]
      rw [Fin.lt_def, Fin.lt_def] at h ⊢
      simp_all
  · obtain ⟨k, hk⟩ := hk
    subst hk
    have h1 : Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) ∈
      (if i.succAbove i1 < i ∧ i < i.succAbove i2 then
        Insert.insert ((finCongr (insertIdx_length_fin φ φs i).symm) i)
        (insertListLiftFinset φ i (c.signFinset i1 i2))
      else insertListLiftFinset φ i (c.signFinset i1 i2)) ↔
      Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) ∈
        insertListLiftFinset φ i (c.signFinset i1 i2) := by
      split
      · simp only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_insert, Fin.ext_iff,
        Fin.coe_cast, or_iff_right_iff_imp]
        intro h
        have h1 : i.succAbove k ≠ i := by
          exact Fin.succAbove_ne i k
        omega
      · simp
    rw [h1]
    rw [succAbove_mem_insertListLiftFinset]
    simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
      insertList_none_succAbove_getDual?_eq_none_iff, insertList_none_succAbove_getDual?_isSome_iff,
      insertList_none_getDual?_get_eq, true_and]
    rw [Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def]
    simp only [Fin.coe_cast, Fin.val_fin_lt]
    rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
    simp only [and_congr_right_iff]
    intro h1 h2
    conv_lhs =>
      rhs
      enter [h]
      rw [Fin.lt_def]
      simp only [Fin.coe_cast, Fin.val_fin_lt]
      rw [Fin.succAbove_lt_succAbove_iff]

lemma stat_ofFinset_of_insertListLiftFinset (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) :
    (𝓕 |>ₛ ⟨(φs.insertIdx i φ).get, insertListLiftFinset φ i a⟩) =
    𝓕 |>ₛ ⟨φs.get, a⟩ := by
  simp only [ofFinset, Nat.succ_eq_add_one]
  congr 1
  rw [get_eq_insertIdx_succAbove φ _ i]
  rw [← List.map_map, ← List.map_map]
  congr
  have h1 : (List.map (⇑(finCongr (insertIdx_length_fin φ φs i).symm))
      (List.map i.succAbove (Finset.sort (fun x1 x2 => x1 ≤ x2) a))).Sorted (· ≤ ·) := by
    simp only [Nat.succ_eq_add_one, List.map_map]
    refine
      fin_list_sorted_monotone_sorted (Finset.sort (fun x1 x2 => x1 ≤ x2) a) ?hl
        (⇑(finCongr (Eq.symm (insertIdx_length_fin φ φs i))) ∘ i.succAbove) ?hf
    exact Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) a
    refine StrictMono.comp (fun ⦃a b⦄ a => a) ?hf.hf
    exact Fin.strictMono_succAbove i
  have h2 : (List.map (⇑(finCongr (insertIdx_length_fin φ φs i).symm))
      (List.map i.succAbove (Finset.sort (fun x1 x2 => x1 ≤ x2) a))).Nodup := by
    simp only [Nat.succ_eq_add_one, List.map_map]
    refine List.Nodup.map ?_ ?_
    apply (Equiv.comp_injective _ (finCongr _)).mpr
    exact Fin.succAbove_right_injective
    exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) a
  have h3 : (List.map (⇑(finCongr (insertIdx_length_fin φ φs i).symm))
      (List.map i.succAbove (Finset.sort (fun x1 x2 => x1 ≤ x2) a))).toFinset
      = (insertListLiftFinset φ i a) := by
    ext b
    simp only [Nat.succ_eq_add_one, List.map_map, List.mem_toFinset, List.mem_map, Finset.mem_sort,
      Function.comp_apply, finCongr_apply]
    rcases insert_fin_eq_self φ i b with hk | hk
    · subst hk
      simp only [Nat.succ_eq_add_one, self_not_mem_insertListLiftFinset, iff_false, not_exists,
        not_and]
      intro x hx
      refine Fin.ne_of_val_ne ?h.inl.h
      simp only [Fin.coe_cast, ne_eq]
      rw [@Fin.val_eq_val]
      exact Fin.succAbove_ne i x
    · obtain ⟨k, hk⟩ := hk
      subst hk
      simp only [Nat.succ_eq_add_one]
      rw [succAbove_mem_insertListLiftFinset]
      apply Iff.intro
      · intro h
        obtain ⟨x, hx⟩ := h
        simp only [Fin.ext_iff, Fin.coe_cast] at hx
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

lemma stat_ofFinset_eq_one_of_isGradedObeying (φs : List 𝓕.States)
    (a : Finset (Fin φs.length)) (c : ContractionsNat φs.length) (hg : IsGradedObeying φs c)
    (hnon : ∀ i, c.getDual? i = none → i ∉ a)
    (hsom : ∀ i, (h : (c.getDual? i).isSome) → i ∈ a → (c.getDual? i).get h ∈ a) :
    (𝓕 |>ₛ ⟨φs.get, a⟩) = 1 := by
  rw [ofFinset_eq_prod]
  let e2 : Fin φs.length ≃ {x // (c.getDual? x).isSome} ⊕ {x // ¬ (c.getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (c.getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [Fin.getElem_fin, Fintype.prod_sum_type, instCommGroup]
  conv_lhs =>
    enter [2, 2, x]
    simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, e2]
    rw [if_neg (hnon x.1 (by simpa using x.2))]
  simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Finset.prod_const_one, mul_one, e2]
  rw [← c.sigmaContractedEquiv.prod_comp]
  erw [Finset.prod_sigma]
  apply Fintype.prod_eq_one _
  intro x
  rw [prod_finset_eq_mul_fst_snd]
  simp only [sigmaContractedEquiv, Equiv.coe_fn_mk, mul_ite, ite_mul, one_mul, mul_one]
  split
  · split
    erw [hg x]
    simp only [Fin.getElem_fin, mul_self]
    rename_i h1 h2
    have hsom' := hsom (c.sndFieldOfContract x) (by simp) h1
    simp only [sndFieldOfContract_getDual?, Option.get_some] at hsom'
    exact False.elim (h2 hsom')
  · split
    rename_i h1 h2
    have hsom' := hsom (c.fstFieldOfContract x) (by simp) h2
    simp only [fstFieldOfContract_getDual?, Option.get_some] at hsom'
    exact False.elim (h1 hsom')
    rfl

lemma signFinset_insertList_some (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (i1 i2 : Fin φs.length)
    (j : c.uncontracted) :
    (c.insertList φ φs i (some j)).signFinset (finCongr (insertIdx_length_fin φ φs i).symm
    (i.succAbove i1)) (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove i2)) =
    if i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) then
      Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
      (insertListLiftFinset φ i (c.signFinset i1 i2))
    else
      if i1 < j ∧ j < i2 ∧ ¬ i.succAbove i1 < i then
        (insertListLiftFinset φ i (c.signFinset i1 i2)).erase
        (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      else
        (insertListLiftFinset φ i (c.signFinset i1 i2)) := by
  ext k
  rcases insert_fin_eq_self φ i k with hk | hk
  · subst hk
    have h1 : Fin.cast (insertIdx_length_fin φ φs i).symm i ∈
      (if i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) then
      Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
      (insertListLiftFinset φ i (c.signFinset i1 i2))
      else
        if i1 < j ∧ j < i2 ∧ ¬ i.succAbove i1 < i then
          (insertListLiftFinset φ i (c.signFinset i1 i2)).erase
          (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
        else
          (insertListLiftFinset φ i (c.signFinset i1 i2))) ↔
          i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) := by
        split
        simp_all only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_insert,
          self_not_mem_insertListLiftFinset, or_false, and_self]
        rename_i h
        simp only [Nat.succ_eq_add_one, not_lt, finCongr_apply, h, iff_false]
        split
        simp only [Finset.mem_erase, ne_eq, self_not_mem_insertListLiftFinset, and_false,
          not_false_eq_true]
        simp
    rw [h1]
    simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
      insertList_some_getDual?_self_eq, reduceCtorEq, Option.isSome_some, Option.get_some,
      forall_const, false_or, true_and]
    rw [Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def]
    simp only [Fin.coe_cast, Fin.val_fin_lt, and_congr_right_iff]
    intro h1 h2
    exact Fin.succAbove_lt_succAbove_iff
  · obtain ⟨k, hk⟩ := hk
    subst hk
    by_cases hkj : k = j.1
    · subst hkj
      conv_lhs=> simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter,
        Finset.mem_univ, insertList_some_getDual?_some_eq, reduceCtorEq, Option.isSome_some,
        Option.get_some, forall_const, false_or, true_and, not_lt]
      rw [Fin.lt_def, Fin.lt_def]
      simp only [Fin.coe_cast, Fin.val_fin_lt, Nat.succ_eq_add_one, finCongr_apply, not_lt]
      conv_lhs =>
        enter [2, 2]
        rw [Fin.lt_def]
      simp only [Fin.coe_cast, Fin.val_fin_lt]
      split
      · rename_i h
        simp_all only [and_true, Finset.mem_insert]
        rw [succAbove_mem_insertListLiftFinset]
        simp only [Fin.ext_iff, Fin.coe_cast]
        have h1 : ¬ (i.succAbove ↑j) = i := by exact Fin.succAbove_ne i ↑j
        simp only [Fin.val_eq_val, h1, signFinset, Finset.mem_filter, Finset.mem_univ, true_and,
          false_or]
        rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
        simp only [and_congr_right_iff, iff_self_and]
        intro h1 h2
        apply Or.inl
        have hj:= j.2
        simpa [uncontracted, -Finset.coe_mem] using hj
      · rename_i h
        simp only [not_and, not_lt] at h
        rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
        split
        · rename_i h1
          simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false, not_and,
            not_lt]
          intro h1 h2
          omega
        · rename_i h1
          rw [succAbove_mem_insertListLiftFinset]
          simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
          intro h1 h2
          have hj:= j.2
          simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [hj, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self,
            iff_true, gt_iff_lt]
          omega
    · have h1 : Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) ∈
        (if i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) then
        Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
        (insertListLiftFinset φ i (c.signFinset i1 i2))
        else
        if i1 < j ∧ j < i2 ∧ ¬ i.succAbove i1 < i then
          (insertListLiftFinset φ i (c.signFinset i1 i2)).erase
          (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
        else
          (insertListLiftFinset φ i (c.signFinset i1 i2))) ↔
          Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) ∈
          (insertListLiftFinset φ i (c.signFinset i1 i2)) := by
        split
        · simp only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_insert, or_iff_right_iff_imp]
          intro h
          simp only [Fin.ext_iff, Fin.coe_cast] at h
          simp only [Fin.val_eq_val] at h
          have hn : ¬ i.succAbove k = i := by exact Fin.succAbove_ne i k
          exact False.elim (hn h)
        · split
          simp only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_erase, ne_eq,
            and_iff_right_iff_imp]
          intro h
          simp only [Fin.ext_iff, Fin.coe_cast]
          simp only [Fin.val_eq_val]
          rw [Function.Injective.eq_iff]
          exact hkj
          exact Fin.succAbove_right_injective
          · simp
      rw [h1]
      rw [succAbove_mem_insertListLiftFinset]
      simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def]
      simp only [Fin.coe_cast, Fin.val_fin_lt]
      rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
      simp only [and_congr_right_iff]
      intro h1 h2
      simp only [ne_eq, hkj, not_false_eq_true, insertList_some_succAbove_getDual?_eq_option,
        Nat.succ_eq_add_one, Option.map_eq_none', Option.isSome_map']
      conv_lhs =>
        rhs
        enter [h]
        rw [Fin.lt_def]
        simp only [Fin.coe_cast, Option.get_map, Function.comp_apply, Fin.val_fin_lt]
        rw [Fin.succAbove_lt_succAbove_iff]

def sign (φs : List 𝓕.States) (c : ContractionsNat φs.length) : ℂ :=
  ∏ (a : c.1), 𝓢(𝓕 |>ₛ φs[c.sndFieldOfContract a],
    𝓕 |>ₛ ⟨φs.get, c.signFinset (c.fstFieldOfContract a) (c.sndFieldOfContract a)⟩)

/-!

## Sign insert
-/

def signInsertNone (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) : ℂ :=
  ∏ (a : c.1),
    if i.succAbove (c.fstFieldOfContract a) < i ∧ i < i.succAbove (c.sndFieldOfContract a) then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[c.sndFieldOfContract a])
    else 1

lemma sign_insert_none (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) :
    (c.insertList φ φs i none).sign = (c.signInsertNone φ φs i) * c.sign := by
  rw [sign]
  rw [signInsertNone, sign, ← Finset.prod_mul_distrib]
  rw [insertList_none_prod_contractions]
  congr
  funext a
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one, insertList_sndFieldOfContract, finCongr_apply,
    Fin.getElem_fin, Fin.coe_cast, insertIdx_getElem_fin, insertList_fstFieldOfContract, ite_mul,
    one_mul]
  erw [signFinset_insertList_none]
  split
  · rw [ofFinset_insert]
    simp only [instCommGroup, Nat.succ_eq_add_one, finCongr_apply, Fin.getElem_fin, Fin.coe_cast,
      insertIdx_getElem_self, map_mul]
    rw [stat_ofFinset_of_insertListLiftFinset]
    simp only [pairedSign_symm, instCommGroup.eq_1]
    simp
  · rw [stat_ofFinset_of_insertListLiftFinset]

lemma signInsertNone_eq_mul_fst_snd (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) :
  c.signInsertNone φ φs i = ∏ (a : c.1),
    (if i.succAbove (c.fstFieldOfContract a) < i then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[c.sndFieldOfContract a])
    else 1) *
    (if i.succAbove (c.sndFieldOfContract a) < i then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[c.sndFieldOfContract a])
    else 1) := by
  rw [signInsertNone]
  congr
  funext a
  split
  · rename_i h
    simp only [instCommGroup.eq_1, Fin.getElem_fin, h.1, ↓reduceIte, mul_ite, pairedSign_mul_self,
      mul_one]
    rw [if_neg]
    omega
  · rename_i h
    simp only [Nat.succ_eq_add_one, not_and, not_lt] at h
    split <;> rename_i h1
    · simp_all only [forall_const, instCommGroup.eq_1, Fin.getElem_fin, mul_ite,
      pairedSign_mul_self, mul_one]
      rw [if_pos]
      have h1 :i.succAbove (c.sndFieldOfContract a) ≠ i :=
        Fin.succAbove_ne i (c.sndFieldOfContract a)
      omega
    · simp only [not_lt] at h1
      rw [if_neg]
      simp only [mul_one]
      have hn := fstFieldOfContract_lt_sndFieldOfContract c a
      have hx : i.succAbove (c.fstFieldOfContract a) < i.succAbove (c.sndFieldOfContract a) := by
        exact Fin.succAbove_lt_succAbove_iff.mpr hn
      omega

lemma signInsertNone_eq_prod_prod (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (hG : IsGradedObeying φs c) :
    c.signInsertNone φ φs i = ∏ (a : c.1), ∏ (x : a),
      (if i.succAbove x < i then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.1]) else 1) := by
  rw [signInsertNone_eq_mul_fst_snd]
  congr
  funext a
  rw [prod_finset_eq_mul_fst_snd]
  congr 1
  congr 1
  congr 1
  simp only [Fin.getElem_fin]
  erw [hG a]
  rfl

lemma signInsertNone_eq_prod_getDual?_Some (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (hG : IsGradedObeying φs c) :
    c.signInsertNone φ φs i = ∏ (x : Fin φs.length),
      if (c.getDual? x).isSome then
        (if i.succAbove x < i then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.1]) else 1)
      else 1 := by
  rw [signInsertNone_eq_prod_prod]
  trans ∏ (x : (a : c.1) × a), (if i.succAbove x.2 < i then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.2.1]) else 1)
  · rw [Finset.prod_sigma']
    rfl
  rw [← c.sigmaContractedEquiv.symm.prod_comp]
  let e2 : Fin φs.length ≃ {x // (c.getDual? x).isSome} ⊕ {x // ¬ (c.getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (c.getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [instCommGroup.eq_1, Fin.getElem_fin, Fintype.prod_sum_type]
  conv_rhs =>
    rhs
    enter [2, a]
    rw [if_neg (by simpa [e2] using a.2)]
  conv_rhs =>
    lhs
    enter [2, a]
    rw [if_pos (by simpa [e2] using a.2)]
  simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Finset.prod_const_one, mul_one, e2]
  rfl
  exact hG

lemma signInsertNone_eq_filter_map (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (hG : IsGradedObeying φs c) :
    c.signInsertNone φ φs i =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ((List.filter (fun x => (c.getDual? x).isSome ∧ i.succAbove x < i)
    (List.finRange φs.length)).map φs.get)) := by
  rw [signInsertNone_eq_prod_getDual?_Some]
  rw [FieldStatistic.ofList_map_eq_finset_prod]
  rw [map_prod]
  congr
  funext a
  simp only [instCommGroup.eq_1, Bool.decide_and, Bool.decide_eq_true, List.mem_filter,
    List.mem_finRange, Bool.and_eq_true, decide_eq_true_eq, true_and, Fin.getElem_fin]
  split
  · rename_i h
    simp only [h, true_and]
    split
    · rfl
    · simp only [map_one]
  · rename_i h
    simp [h]
  · refine List.Nodup.filter _ ?_
    exact List.nodup_finRange φs.length
  · exact hG

lemma signInsertNone_eq_filterset (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (hG : IsGradedObeying φs c) :
    c.signInsertNone φ φs i = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter
    (fun x => (c.getDual? x).isSome ∧ i.succAbove x < i)⟩) := by
  rw [ofFinset_eq_prod, signInsertNone_eq_prod_getDual?_Some, map_prod]
  congr
  funext a
  simp only [instCommGroup.eq_1, Finset.mem_filter, Finset.mem_univ, true_and, Fin.getElem_fin]
  split
  · rename_i h
    simp only [h, true_and]
    split
    · rfl
    · simp only [map_one]
  · rename_i h
    simp [h]
  · exact hG

/-!

## Sign insert some

-/

def signInsertSomeProd (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) (j : c.uncontracted) : ℂ :=
  ∏ (a : c.1),
    if i.succAbove (c.fstFieldOfContract a) < i ∧ i < i.succAbove (c.sndFieldOfContract a) ∧
      ((c.fstFieldOfContract a) < j) then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[c.sndFieldOfContract a])
    else
    if (c.fstFieldOfContract a) < j ∧ j < (c.sndFieldOfContract a) ∧
        ¬ i.succAbove (c.fstFieldOfContract a) < i then
      𝓢(𝓕 |>ₛ φs[j.1], 𝓕 |>ₛ φs[c.sndFieldOfContract a])
    else
      1

def signInsertSomeCoef (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) (j : c.uncontracted) : ℂ :=
  let a : (c.insertList φ φs i (some j)).1 :=
    congrLift (insertIdx_length_fin φ φs i).symm
    ⟨{i, i.succAbove j}, by simp [insert]⟩;
  𝓢(𝓕 |>ₛ (φs.insertIdx i φ)[(c.insertList φ φs i (some j)).sndFieldOfContract a],
    𝓕 |>ₛ ⟨(φs.insertIdx i φ).get, signFinset
    (c.insertList φ φs i (some j)) ((c.insertList φ φs i (some j)).fstFieldOfContract a)
    ((c.insertList φ φs i (some j)).sndFieldOfContract a)⟩)

def signInsertSome (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) : ℂ :=
  signInsertSomeCoef φ φs c i j * signInsertSomeProd φ φs c i j

lemma sign_insert_some (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) (j : c.uncontracted) :
    (c.insertList φ φs i (some j)).sign = (c.signInsertSome φ φs i j) * c.sign := by
  rw [sign]
  rw [signInsertSome, signInsertSomeProd, sign, mul_assoc, ← Finset.prod_mul_distrib]
  rw [insertList_some_prod_contractions]
  congr
  funext a
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one, insertList_sndFieldOfContract, finCongr_apply,
    Fin.getElem_fin, Fin.coe_cast, insertIdx_getElem_fin, insertList_fstFieldOfContract, not_lt,
    ite_mul, one_mul]
  erw [signFinset_insertList_some]
  split
  · rename_i h
    simp only [Nat.succ_eq_add_one, finCongr_apply]
    rw [ofFinset_insert]
    simp only [instCommGroup, Fin.getElem_fin, Fin.coe_cast, insertIdx_getElem_self, map_mul]
    rw [stat_ofFinset_of_insertListLiftFinset]
    simp only [pairedSign_symm, instCommGroup.eq_1]
    simp
  · rename_i h
    split
    · rename_i h1
      simp only [Nat.succ_eq_add_one, finCongr_apply, h1, true_and]
      rw [if_pos]
      rw [ofFinset_erase]
      simp only [instCommGroup, Fin.getElem_fin, Fin.coe_cast, insertIdx_getElem_fin, map_mul]
      rw [stat_ofFinset_of_insertListLiftFinset]
      simp only [pairedSign_symm, instCommGroup.eq_1]
      · rw [succAbove_mem_insertListLiftFinset]
        simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        simp_all only [Nat.succ_eq_add_one, and_true, false_and, not_false_eq_true, not_lt,
          true_and]
        apply Or.inl
        simpa [uncontracted, -Finset.coe_mem] using j.2
      · simp_all
    · rename_i h1
      rw [if_neg]
      rw [stat_ofFinset_of_insertListLiftFinset]
      simp_all

lemma signInsertSomeProd_eq_one_if (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1])) :
  c.signInsertSomeProd φ φs i j =
  ∏ (a : c.1),
    if (c.fstFieldOfContract a) < j
      ∧ (i.succAbove (c.fstFieldOfContract a) < i ∧ i < i.succAbove (c.sndFieldOfContract a)
      ∨ j < (c.sndFieldOfContract a) ∧ ¬ i.succAbove (c.fstFieldOfContract a) < i)
    then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[c.sndFieldOfContract a])
    else
      1 := by
  rw [signInsertSomeProd]
  congr
  funext a
  split
  · rename_i h
    simp only [instCommGroup.eq_1, Fin.getElem_fin, h, Nat.succ_eq_add_one, and_self,
      not_true_eq_false, and_false, or_false, ↓reduceIte]
  · rename_i h
    split
    · rename_i h1
      simp only [instCommGroup.eq_1, Fin.getElem_fin, h1, Nat.succ_eq_add_one, false_and,
        not_false_eq_true, and_self, or_true, ↓reduceIte]
      congr 1
      exact congrArg (⇑pairedSign) (id (Eq.symm hφj))
    · rename_i h1
      simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Fin.getElem_fin]
      rw [if_neg]
      simp_all only [Fin.getElem_fin, Nat.succ_eq_add_one, not_and, not_lt, not_le, not_or,
        implies_true, and_true]
      omega

lemma signInsertSomeProd_eq_prod_prod (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : IsGradedObeying φs c) :
  c.signInsertSomeProd φ φs i j =
  ∏ (a : c.1), ∏ (x : a.1), if x.1 < j
      ∧ (i.succAbove x.1 < i ∧ i < i.succAbove ((c.getDual? x.1).get (getDual?_isSome_of_mem c a x))
      ∨ j < ((c.getDual? x.1).get (getDual?_isSome_of_mem c a x)) ∧ ¬ i.succAbove x < i)
    then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.1])
    else
      1 := by
  rw [signInsertSomeProd_eq_one_if]
  congr
  funext a
  rw [prod_finset_eq_mul_fst_snd]
  nth_rewrite 3 [if_neg]
  · simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Fin.getElem_fin,
    fstFieldOfContract_getDual?, Option.get_some, mul_one]
    congr 1
    erw [hg a]
    simp
  · simp only [Nat.succ_eq_add_one, sndFieldOfContract_getDual?, Option.get_some, not_lt, not_and,
    not_or, not_le]
    intro h1
    have ha := fstFieldOfContract_lt_sndFieldOfContract c a
    apply And.intro
    · intro hi
      have hx : i.succAbove (c.fstFieldOfContract a) < i.succAbove (c.sndFieldOfContract a) := by
        exact Fin.succAbove_lt_succAbove_iff.mpr ha
      omega
    · omega
  simp [hφj]

lemma signInsertSomeProd_eq_prod_fin (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : IsGradedObeying φs c) :
  c.signInsertSomeProd φ φs i j =
    ∏ (x : Fin φs.length),
      if h : (c.getDual? x).isSome then
          if x < j ∧ (i.succAbove x < i ∧ i < i.succAbove ((c.getDual? x).get h)
            ∨ j < ((c.getDual? x).get h) ∧ ¬ i.succAbove x < i)
          then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.1])
          else 1
      else 1 := by
  rw [signInsertSomeProd_eq_prod_prod]
  rw [Finset.prod_sigma']
  erw [← c.sigmaContractedEquiv.symm.prod_comp]
  let e2 : Fin φs.length ≃ {x // (c.getDual? x).isSome} ⊕ {x // ¬ (c.getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (c.getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [instCommGroup.eq_1, Fin.getElem_fin, Fintype.prod_sum_type]
  conv_rhs =>
    rhs
    enter [2, a]
    rw [dif_neg (by simpa [e2] using a.2)]
  conv_rhs =>
    lhs
    enter [2, a]
    rw [dif_pos (by simpa [e2] using a.2)]
  simp only [Nat.succ_eq_add_one, not_lt, Equiv.symm_symm, Equiv.sumCompl_apply_inl,
    Finset.prod_const_one, mul_one, e2]
  rfl
  simp only [hφj, Fin.getElem_fin]
  exact hg

lemma signInsertSomeProd_eq_list (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : IsGradedObeying φs c) :
    c.signInsertSomeProd φ φs i j =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (List.filter (fun x => (c.getDual? x).isSome ∧ ∀ (h : (c.getDual? x).isSome),
      x < j ∧ (i.succAbove x < i ∧ i < i.succAbove ((c.getDual? x).get h)
      ∨ j < ((c.getDual? x).get h) ∧ ¬ i.succAbove x < i))
    (List.finRange φs.length)).map φs.get) := by
  rw [signInsertSomeProd_eq_prod_fin]
  rw [FieldStatistic.ofList_map_eq_finset_prod]
  rw [map_prod]
  congr
  funext x
  split
  · rename_i h
    simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Bool.decide_and,
      Bool.decide_eq_true, List.mem_filter, List.mem_finRange, h, forall_true_left, Bool.decide_or,
      Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, true_and,
      Fin.getElem_fin]
    split
    · rename_i h1
      simp [h1]
    · rename_i h1
      simp [h1]
  · rename_i h
    simp [h]
  refine
    List.Nodup.filter _ ?_
  exact List.nodup_finRange φs.length
  simp only [hφj, Fin.getElem_fin]
  exact hg

lemma signInsertSomeProd_eq_finset (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : IsGradedObeying φs c) :
    c.signInsertSomeProd φ φs i j =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => (c.getDual? x).isSome ∧
      ∀ (h : (c.getDual? x).isSome),
      x < j ∧ (i.succAbove x < i ∧ i < i.succAbove ((c.getDual? x).get h)
      ∨ j < ((c.getDual? x).get h) ∧ ¬ i.succAbove x < i)))⟩) := by
  rw [signInsertSomeProd_eq_prod_fin]
  rw [ofFinset_eq_prod]
  rw [map_prod]
  congr
  funext x
  split
  · rename_i h
    simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Finset.mem_filter, Finset.mem_univ,
      h, forall_true_left, true_and, Fin.getElem_fin]
    split
    · rename_i h1
      simp [h1]
    · rename_i h1
      simp [h1]
  · rename_i h
    simp [h]
  simp only [hφj, Fin.getElem_fin]
  exact hg

lemma signInsertSomeCoef_if (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1])) :
    c.signInsertSomeCoef φ φs i j =
    if i < i.succAbove j then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
      (signFinset (c.insertList φ φs i (some j)) (finCongr (insertIdx_length_fin φ φs i).symm i)
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)))⟩)
    else
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
      signFinset (c.insertList φ φs i (some j))
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (finCongr (insertIdx_length_fin φ φs i).symm i)⟩) := by
  simp only [signInsertSomeCoef, instCommGroup.eq_1, Nat.succ_eq_add_one,
    insertList_sndFieldOfContract_some_incl, finCongr_apply, Fin.getElem_fin,
    insertList_fstFieldOfContract_some_incl]
  split
  · simp [hφj]
  · simp [hφj]

lemma stat_signFinset_insert_some_self_fst
    (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) :
  (𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
    (signFinset (c.insertList φ φs i (some j)) (finCongr (insertIdx_length_fin φ φs i).symm i)
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)))⟩) =
  𝓕 |>ₛ ⟨φs.get,
    (Finset.univ.filter (fun x => i < i.succAbove x ∧ x < j ∧ ((c.getDual? x = none) ∨
      ∀ (h : (c.getDual? x).isSome), i < i.succAbove ((c.getDual? x).get h))))⟩ := by
  rw [get_eq_insertIdx_succAbove φ _ i]
  rw [ofFinset_finset_map]
  swap
  refine
    (Equiv.comp_injective i.succAbove (finCongr (Eq.symm (insertIdx_length_fin φ φs i)))).mpr ?hi.a
  exact Fin.succAbove_right_injective
  congr
  ext x
  simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map, Function.Embedding.coeFn_mk, Function.comp_apply]
  rcases insert_fin_eq_self φ i x with hx | hx
  · subst hx
    simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertList_some_getDual?_self_eq,
      reduceCtorEq, Option.isSome_some, Option.get_some, forall_const, false_or, and_self,
      false_and, false_iff, not_exists, not_and, and_imp]
    intro x hi hx
    intro h
    simp only [Fin.ext_iff, Fin.coe_cast]
    simp only [Fin.val_eq_val]
    exact Fin.succAbove_ne i x
  · obtain ⟨x, hx⟩ := hx
    subst hx
    by_cases h : x = j.1
    · subst h
      simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertList_some_getDual?_some_eq,
        reduceCtorEq, Option.isSome_some, Option.get_some, imp_false, not_true_eq_false, or_self,
        and_self, and_false, false_iff, not_exists, not_and, and_imp]
      intro x hi hx h0
      simp only [Fin.ext_iff, Fin.coe_cast]
      simp only [Fin.val_eq_val]
      rw [Function.Injective.eq_iff]
      omega
      exact Fin.succAbove_right_injective
    · simp only [Nat.succ_eq_add_one, ne_eq, h, not_false_eq_true,
      insertList_some_succAbove_getDual?_eq_option, Option.map_eq_none', Option.isSome_map']
      rw [Fin.lt_def, Fin.lt_def]
      simp only [Fin.coe_cast, Fin.val_fin_lt]
      apply Iff.intro
      · intro h
        use x
        simp only [h, true_and, and_true]
        simp only [Option.get_map, Function.comp_apply] at h
        apply And.intro (Fin.succAbove_lt_succAbove_iff.mp h.2.1)
        have h2 := h.2.2
        rcases h2 with h2 | h2
        · simp [h2]
        · apply Or.inr
          intro h
          have h2 := h2 h
          simpa using h2
      · intro h
        obtain ⟨y, hy1, hy2⟩ := h
        simp only [Fin.ext_iff, Fin.coe_cast] at hy2
        simp only [Fin.val_eq_val] at hy2
        rw [Function.Injective.eq_iff (by exact Fin.succAbove_right_injective)] at hy2
        subst hy2
        simp only [hy1, true_and]
        apply And.intro
        · rw [@Fin.succAbove_lt_succAbove_iff]
          omega
        · have hy2 := hy1.2.2
          rcases hy2 with hy2 | hy2
          · simp [hy2]
          · apply Or.inr
            intro h
            have hy2 := hy2 h
            simpa [Option.get_map] using hy2

lemma stat_signFinset_insert_some_self_snd
  (φ : 𝓕.States) (φs : List 𝓕.States) (c : ContractionsNat φs.length)
      (i : Fin φs.length.succ) (j : c.uncontracted) :
  (𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
    (signFinset (c.insertList φ φs i (some j))
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (finCongr (insertIdx_length_fin φ φs i).symm i))⟩) =
  𝓕 |>ₛ ⟨φs.get,
    (Finset.univ.filter (fun x => j < x ∧ i.succAbove x < i ∧ ((c.getDual? x = none) ∨
      ∀ (h : (c.getDual? x).isSome), j < ((c.getDual? x).get h))))⟩ := by
  rw [get_eq_insertIdx_succAbove φ _ i]
  rw [ofFinset_finset_map]
  swap
  refine
    (Equiv.comp_injective i.succAbove (finCongr (Eq.symm (insertIdx_length_fin φ φs i)))).mpr ?hi.a
  exact Fin.succAbove_right_injective
  congr
  ext x
  simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map, Function.Embedding.coeFn_mk, Function.comp_apply]
  rcases insert_fin_eq_self φ i x with hx | hx
  · subst hx
    simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertList_some_getDual?_self_eq,
      reduceCtorEq, Option.isSome_some, Option.get_some, imp_false, not_true_eq_false, or_self,
      and_self, and_false, false_iff, not_exists, not_and, and_imp]
    intro x hi hx
    intro h
    simp only [Fin.ext_iff, Fin.coe_cast]
    simp only [Fin.val_eq_val]
    exact Fin.succAbove_ne i x
  · obtain ⟨x, hx⟩ := hx
    subst hx
    by_cases h : x = j.1
    · subst h
      simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertList_some_getDual?_some_eq,
        reduceCtorEq, Option.isSome_some, Option.get_some, forall_const, false_or, and_self,
        false_and, false_iff, not_exists, not_and, and_imp]
      intro x hi hx h0
      simp only [Fin.ext_iff, Fin.coe_cast]
      simp only [Fin.val_eq_val]
      rw [Function.Injective.eq_iff]
      omega
      exact Fin.succAbove_right_injective
    · simp only [Nat.succ_eq_add_one, ne_eq, h, not_false_eq_true,
      insertList_some_succAbove_getDual?_eq_option, Option.map_eq_none', Option.isSome_map']
      rw [Fin.lt_def, Fin.lt_def]
      simp only [Fin.coe_cast, Fin.val_fin_lt]
      apply Iff.intro
      · intro h
        use x
        simp only [h, true_and, and_true]
        simp only [Option.get_map, Function.comp_apply] at h
        apply And.intro (Fin.succAbove_lt_succAbove_iff.mp h.1)
        have h2 := h.2.2
        rcases h2 with h2 | h2
        · simp [h2]
        · apply Or.inr
          intro h
          have h2 := h2 h
          rw [Fin.lt_def] at h2
          simp only [Fin.coe_cast, Fin.val_fin_lt] at h2
          exact Fin.succAbove_lt_succAbove_iff.mp h2
      · intro h
        obtain ⟨y, hy1, hy2⟩ := h
        simp only [Fin.ext_iff, Fin.coe_cast] at hy2
        simp only [Fin.val_eq_val] at hy2
        rw [Function.Injective.eq_iff (by exact Fin.succAbove_right_injective)] at hy2
        subst hy2
        simp only [hy1, true_and]
        apply And.intro
        · rw [@Fin.succAbove_lt_succAbove_iff]
          omega
        · have hy2 := hy1.2.2
          rcases hy2 with hy2 | hy2
          · simp [hy2]
          · apply Or.inr
            intro h
            have hy2 := hy2 h
            simp only [Fin.lt_def, Fin.coe_cast, gt_iff_lt]
            simp only [Option.get_map, Function.comp_apply, Fin.coe_cast, Fin.val_fin_lt]
            exact Fin.succAbove_lt_succAbove_iff.mpr hy2

lemma signInsertSomeCoef_eq_finset (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length)
    (i : Fin φs.length.succ) (j : c.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1])) :
    c.signInsertSomeCoef φ φs i j =
    if i < i.succAbove j then
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get,
    (Finset.univ.filter (fun x => i < i.succAbove x ∧ x < j ∧ ((c.getDual? x = none) ∨
      ∀ (h : (c.getDual? x).isSome), i < i.succAbove ((c.getDual? x).get h))))⟩) else
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get,
      (Finset.univ.filter (fun x => j < x ∧ i.succAbove x < i ∧ ((c.getDual? x = none) ∨
      ∀ (h : (c.getDual? x).isSome), j < ((c.getDual? x).get h))))⟩) := by
  rw [signInsertSomeCoef_if]
  rw [stat_signFinset_insert_some_self_snd]
  rw [stat_signFinset_insert_some_self_fst]
  simp [hφj]

lemma signInsertSome_mul_filter_contracted_of_lt (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (k : c.uncontracted)
    (hk : i.succAbove k < i)
    (hg : IsGradedObeying φs c ∧ 𝓕.statesStatistic φ = 𝓕.statesStatistic φs[k.1]) :
    signInsertSome φ φs c i k *
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, c.uncontracted.filter (fun x => x ≤ ↑k)⟩)
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter (fun x => i.succAbove x < i)⟩) := by
  rw [signInsertSome, signInsertSomeProd_eq_finset, signInsertSomeCoef_eq_finset]
  rw [if_neg (by omega), ← map_mul, ← map_mul]
  congr 1
  rw [mul_eq_iff_eq_mul, ofFinset_union_disjoint]
  swap
  · rw [Finset.disjoint_filter]
    intro j _ h
    simp only [Nat.succ_eq_add_one, not_lt, not_and, not_forall, not_or, not_le]
    intro h1
    use h1
    omega
  trans 𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x =>
      (↑k < x ∧ i.succAbove x < i ∧ (c.getDual? x = none ∨
      ∀ (h : (c.getDual? x).isSome = true), ↑k < (c.getDual? x).get h))
      ∨ ((c.getDual? x).isSome = true ∧
      ∀ (h : (c.getDual? x).isSome = true), x < ↑k ∧
      (i.succAbove x < i ∧ i < i.succAbove ((c.getDual? x).get h) ∨
      ↑k < (c.getDual? x).get h ∧ ¬i.succAbove x < i))) Finset.univ)⟩
  · congr
    ext j
    simp
  rw [ofFinset_union, ← mul_eq_one_iff, ofFinset_union]
  simp only [Nat.succ_eq_add_one, not_lt]
  apply stat_ofFinset_eq_one_of_isGradedObeying
  · exact hg.1
  /- the getDual? is none case-/
  · intro j hn
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hn, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, and_true, or_false,
      true_and, and_self, Finset.mem_inter, not_and, not_lt, Classical.not_imp, not_le, and_imp]
    intro h
    rcases h with h | h
    · simp only [h, or_true, isEmpty_Prop, not_le, IsEmpty.forall_iff, and_self]
    · simp only [h, true_and]
      refine And.intro ?_ (And.intro ?_ h.2)
      · by_contra hkj
        simp only [not_lt] at hkj
        have h2 := h.2 hkj
        apply Fin.ne_succAbove i j
        have hij : i.succAbove j ≤ i.succAbove k.1 :=
          Fin.succAbove_le_succAbove_iff.mpr hkj
        omega
      · have h1' := h.1
        rcases h1' with h1' | h1'
        · have hl := h.2 h1'
          have hij : i.succAbove j ≤ i.succAbove k.1 :=
          Fin.succAbove_le_succAbove_iff.mpr h1'
          by_contra hn
          apply Fin.ne_succAbove i j
          omega
        · exact h1'
  /- the getDual? is some case-/
  · intro j hj
    have hn : ¬ c.getDual? j = none := by exact Option.isSome_iff_ne_none.mp hj
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hn, hj, forall_true_left, false_or, true_and, and_false, false_and, Finset.mem_inter,
      not_false_eq_true, and_true, not_and, not_lt, getDual?_getDual?_get_get, reduceCtorEq,
      Option.isSome_some, Option.get_some, forall_const, and_imp]
    intro h1 h2
    have hijsucc : i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
    have hijsucc' : i.succAbove ((c.getDual? j).get hj) ≠ i := by exact Fin.succAbove_ne i _
    have hkneqj : ↑k ≠ j := by
      by_contra hkj
      have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
      simp only at hl
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    have hkneqgetdual : k.1 ≠ (c.getDual? j).get hj := by
      by_contra hkj
      have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
      simp only [getDual?_getDual?_get_get, Option.isSome_some] at hl
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    by_cases hik : ↑k < j
    · have hn : ¬ j < ↑k := by omega
      simp only [hik, true_and, hn, false_and, or_false, and_imp, and_true] at h1 h2 ⊢
      have hir : i.succAbove j < i := by
        rcases h1 with h1 | h1
        · simp [h1]
        · simp [h1]
      have hirn : ¬ i < i.succAbove j := by omega
      simp only [hir, true_and, or_true, forall_const] at h1 h2
      have hnkdual : ¬ ↑k < (c.getDual? j).get hj := by
        by_contra hn
        have h2 := h2 hn
        apply Fin.ne_succAbove i j
        omega
      simp only [hnkdual, IsEmpty.forall_iff, false_and, false_or, and_imp] at h2 ⊢
      have hnkdual : (c.getDual? j).get hj < ↑k := by omega
      have hi : i.succAbove ((c.getDual? j).get hj) < i.succAbove k := by
        rw [@Fin.succAbove_lt_succAbove_iff]
        omega
      omega
    · have ht : j < ↑k := by omega
      have ht' : i.succAbove j < i.succAbove k := by
        rw [@Fin.succAbove_lt_succAbove_iff]
        omega
      simp only [hik, false_and, ht, true_and, false_or, and_false, or_false, and_imp] at h1 h2 ⊢
      by_cases hik : i.succAbove j < i
      · simp_all only [Fin.getElem_fin, ne_eq, not_lt, true_and, or_true]
        have hn : ¬ i ≤ i.succAbove j := by omega
        simp_all only [and_false, or_false, imp_false, not_lt, Nat.succ_eq_add_one, not_le]
        apply And.intro
        · apply Or.inr
          omega
        · intro h1 h2 h3
          omega
      · simp_all only [Fin.getElem_fin, ne_eq, not_lt, false_and, false_or, or_false, and_self,
        or_true, imp_self]
        omega
  · exact hg.2
  · exact hg.2
  · exact hg.1

lemma signInsertSome_mul_filter_contracted_of_not_lt (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (k : c.uncontracted)
    (hk : ¬ i.succAbove k < i)
    (hg : IsGradedObeying φs c ∧ 𝓕.statesStatistic φ = 𝓕.statesStatistic φs[k.1]) :
    signInsertSome φ φs c i k *
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, c.uncontracted.filter (fun x => x < ↑k)⟩)
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter (fun x => i.succAbove x < i)⟩) := by
  have hik : i.succAbove ↑k ≠ i := by exact Fin.succAbove_ne i ↑k
  rw [signInsertSome, signInsertSomeProd_eq_finset, signInsertSomeCoef_eq_finset]
  rw [if_pos (by omega), ← map_mul, ← map_mul]
  congr 1
  rw [mul_eq_iff_eq_mul, ofFinset_union, ofFinset_union]
  apply (mul_eq_one_iff _ _).mp
  rw [ofFinset_union]
  simp only [Nat.succ_eq_add_one, not_lt]
  apply stat_ofFinset_eq_one_of_isGradedObeying
  · exact hg.1
  · intro j hj
    have hijsucc : i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hj, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, and_true, true_and,
      and_false, or_false, Finset.mem_inter, not_false_eq_true, and_self, not_and, not_lt,
      Classical.not_imp, not_le, and_imp]
    intro h
    have hij : i < i.succAbove j := by
      rcases h with h | h
      · exact h.1
      · rcases h.1 with h1 | h1
        · omega
        · have hik : i.succAbove k.1 ≤ i.succAbove j := by
            rw [Fin.succAbove_le_succAbove_iff]
            omega
          omega
    simp only [hij, true_and] at h ⊢
    omega
  · intro j hj
    have hn : ¬ c.getDual? j = none := by exact Option.isSome_iff_ne_none.mp hj
    have hijSuc : i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
    have hkneqj : ↑k ≠ j := by
      by_contra hkj
      have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
      simp only at hl
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    have hkneqgetdual : k.1 ≠ (c.getDual? j).get hj := by
      by_contra hkj
      have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
      simp only [getDual?_getDual?_get_get, Option.isSome_some] at hl
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hn, hj, forall_true_left, false_or, true_and, Finset.mem_inter, not_and, not_or, not_lt,
      not_le, and_imp, and_false, false_and, not_false_eq_true, and_true, getDual?_getDual?_get_get,
      reduceCtorEq, Option.isSome_some, Option.get_some, forall_const]
    by_cases hik : ↑k < j
    · have hikn : ¬ j < k.1 := by omega
      have hksucc : i.succAbove k.1 < i.succAbove j := by
        rw [Fin.succAbove_lt_succAbove_iff]
        omega
      have hkn : i < i.succAbove j := by omega
      have hl : ¬ i.succAbove j < i := by omega
      simp only [hkn, hikn, false_and, and_false, hl, false_or, or_self, IsEmpty.forall_iff,
        imp_false, not_lt, true_and, implies_true, imp_self, and_true, forall_const, hik,
        imp_forall_iff_forall]
    · have hikn : j < k.1 := by omega
      have hksucc : i.succAbove j < i.succAbove k.1 := by
        rw [Fin.succAbove_lt_succAbove_iff]
        omega
      simp only [hikn, true_and, forall_const, hik, false_and, or_false, IsEmpty.forall_iff,
        and_true]
      by_cases hij: i < i.succAbove j
      · simp only [hij, true_and, forall_const, and_true, imp_forall_iff_forall]
        have hijn : ¬ i.succAbove j < i := by omega
        simp only [hijn, false_and, false_or, IsEmpty.forall_iff, imp_false, not_lt, true_and,
          or_false, and_imp]
        have hijle : i ≤ i.succAbove j := by omega
        simp only [hijle, and_true, implies_true, forall_const]
        intro h1 h2
        apply And.intro
        · rcases h1 with h1 | h1
          · apply Or.inl
            omega
          · apply Or.inl
            have hi : i.succAbove k.1 < i.succAbove ((c.getDual? j).get hj) := by
              rw [Fin.succAbove_lt_succAbove_iff]
              omega
            apply And.intro
            · apply Or.inr
              apply And.intro
              · omega
              · omega
            · omega
        · intro h3 h4
          omega
      · simp only [hij, false_and, false_or, IsEmpty.forall_iff, and_true, forall_const, and_false,
        or_self, implies_true]
        have hijn : i.succAbove j < i := by omega
        have hijn' : ¬ i ≤ i.succAbove j := by omega
        simp only [hijn, true_and, hijn', and_false, or_false, or_true, imp_false, not_lt,
          forall_const]
        exact fun h => lt_of_le_of_ne h (Fin.succAbove_ne i ((c.getDual? j).get hj))
  · exact hg.2
  · exact hg.2
  · exact hg.1

end ContractionsNat

end FieldStruct
