/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
/-!
# Fin lemmas

The purpose of this file is to define some results Fin currently
in Mathlib.

At some point these should either be up-streamed to Mathlib or replaced with definitions already
in Mathlib.

-/
namespace HepLean.Fin

open Fin
variable {n : Nat}

/-- Given a `i` and `x` in `Fin n.succ.succ` returns an element of `Fin n.succ`
  subtracting 1 if `i.val ≤ x.val` else casting x. -/
def predAboveI (i x : Fin n.succ.succ) : Fin n.succ :=
  if h : x.val < i.val then
    ⟨x.val, by omega⟩
  else
    ⟨x.val - 1, by
      by_cases hx : x = 0
      · omega
      · omega⟩

lemma predAboveI_self (i : Fin n.succ.succ) : predAboveI i i = ⟨i.val - 1, by omega⟩ := by
  simp [predAboveI]

@[simp]
lemma predAboveI_succAbove (i : Fin n.succ.succ) (x : Fin n.succ) :
    predAboveI i (Fin.succAbove i x) = x := by
  simp only [Nat.succ_eq_add_one, predAboveI, Fin.succAbove, Fin.val_fin_lt, Fin.ext_iff]
  split_ifs
  · rfl
  · rename_i h1 h2
    simp only [Fin.lt_def, Fin.coe_castSucc, not_lt, Nat.succ_eq_add_one, Fin.val_succ] at h1 h2
    omega
  · rfl
lemma succsAbove_predAboveI {i x : Fin n.succ.succ} (h : i ≠ x) :
    Fin.succAbove i (predAboveI i x) = x := by
  simp only [Fin.succAbove, predAboveI, Nat.succ_eq_add_one, Fin.val_fin_lt, Fin.ext_iff]
  split_ifs
  · rfl
  · rename_i h1 h2
    rw [Fin.lt_def] at h1 h2
    simp only [Fin.succ_mk, Nat.succ_eq_add_one, add_right_eq_self, one_ne_zero]
    simp only [Fin.castSucc_mk, Fin.eta, Fin.val_fin_lt, not_lt] at h2
    rw [Fin.le_def] at h2
    omega
  · rename_i h1 h2
    simp only [not_lt] at h1
    rw [Fin.le_def] at h1
    rw [Fin.lt_def] at h2
    simp only [Fin.castSucc_mk] at h2
    omega
  · rename_i h1 h2
    simp only [Fin.succ_mk, Nat.succ_eq_add_one]
    simp only [not_lt] at h1
    rw [Fin.le_def] at h1
    omega

lemma predAboveI_eq_iff {i x : Fin n.succ.succ} (h : i ≠ x) (y : Fin n.succ) :
    y = predAboveI i x ↔ i.succAbove y = x := by
  apply Iff.intro
  · intro h
    subst h
    rw [succsAbove_predAboveI h]
  · intro h
    rw [← h]
    simp

lemma predAboveI_lt {i x : Fin n.succ.succ} (h : x.val < i.val) :
    predAboveI i x = ⟨x.val, by omega⟩ := by
  simp [predAboveI, h]

lemma predAboveI_ge {i x : Fin n.succ.succ} (h : i.val < x.val) :
    predAboveI i x = ⟨x.val - 1, by omega⟩ := by
  simp only [Nat.succ_eq_add_one, predAboveI, Fin.val_fin_lt, dite_eq_else, Fin.mk.injEq]
  omega

lemma succAbove_succAbove_predAboveI (i : Fin n.succ.succ) (j : Fin n.succ) (x : Fin n) :
    i.succAbove (j.succAbove x) =
    (i.succAbove j).succAbove ((predAboveI (i.succAbove j) i).succAbove x) := by
  by_cases h1 : j.castSucc < i
  · have hx := Fin.succAbove_of_castSucc_lt _ _ h1
    rw [hx]
    rw [predAboveI_ge h1]
    by_cases hx1 : x.castSucc < j
    · rw [Fin.succAbove_of_castSucc_lt _ _ hx1]
      rw [Fin.succAbove_of_castSucc_lt _ _]
      · nth_rewrite 2 [Fin.succAbove_of_castSucc_lt _ _]
        · rw [Fin.succAbove_of_castSucc_lt _ _]
          exact hx1
        · rw [Fin.lt_def] at h1 hx1 ⊢
          simp_all
          omega
      · exact Nat.lt_trans hx1 h1
    · simp only [not_lt] at hx1
      rw [Fin.le_def] at hx1
      rw [Fin.lt_def] at h1
      rw [Fin.succAbove_of_le_castSucc _ _ hx1]
      by_cases hx2 : x.succ.castSucc < i
      · rw [Fin.succAbove_of_castSucc_lt _ _ hx2]
        nth_rewrite 2 [Fin.succAbove_of_castSucc_lt _ _]
        · rw [Fin.succAbove_of_le_castSucc]
          · rfl
          · exact hx1
        · rw [Fin.lt_def] at hx2 ⊢
          simp_all
          omega
      · simp only [Nat.succ_eq_add_one, not_lt] at hx2
        rw [Fin.succAbove_of_le_castSucc _ _ hx2]
        nth_rewrite 2 [Fin.succAbove_of_le_castSucc]
        · rw [Fin.succAbove_of_le_castSucc]
          rw [Fin.le_def]
          exact Nat.le_succ_of_le hx1
        · rw [Fin.le_def] at hx2 ⊢
          simp_all
  · simp only [Nat.succ_eq_add_one, not_lt] at h1
    have hx := Fin.succAbove_of_le_castSucc _ _ h1
    rw [hx]
    rw [predAboveI_lt (Nat.lt_add_one_of_le h1)]
    by_cases hx1 : j ≤ x.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hx1]
      rw [Fin.succAbove_of_le_castSucc _ _]
      · nth_rewrite 2 [Fin.succAbove_of_le_castSucc _ _]
        · rw [Fin.succAbove_of_le_castSucc _ _]
          rw [Fin.le_def] at hx1 ⊢
          simp_all
        · rw [Fin.le_def] at h1 hx1 ⊢
          simp_all
          omega
      · rw [Fin.le_def] at hx1 h1 ⊢
        simp_all
        omega
    · simp only [Nat.succ_eq_add_one, not_le] at hx1
      rw [Fin.lt_def] at hx1
      rw [Fin.le_def] at h1
      rw [Fin.succAbove_of_castSucc_lt _ _ hx1]
      by_cases hx2 : x.castSucc.castSucc < i
      · rw [Fin.succAbove_of_castSucc_lt _ _ hx2]
        nth_rewrite 2 [Fin.succAbove_of_castSucc_lt _ _]
        · rw [Fin.succAbove_of_castSucc_lt _ _]
          rw [Fin.lt_def] at hx2 ⊢
          simp_all
          omega
        · rw [Fin.lt_def] at hx2 ⊢
          simp_all
      · simp only [not_lt] at hx2
        rw [Fin.succAbove_of_le_castSucc _ _ hx2]
        nth_rewrite 2 [Fin.succAbove_of_le_castSucc]
        · rw [Fin.succAbove_of_castSucc_lt]
          · rfl
          exact Fin.castSucc_lt_succ_iff.mpr hx1
        · rw [Fin.le_def] at hx2 ⊢
          simp_all

/-- The equivalence between `Fin n.succ` and `Fin 1 ⊕ Fin n` extracting the
  `i`th component. -/
def finExtractOne {n : ℕ} (i : Fin n.succ) : Fin n.succ ≃ Fin 1 ⊕ Fin n :=
  (finCongr (by omega : n.succ = i + 1 + (n - i))).trans <|
  finSumFinEquiv.symm.trans <|
  (Equiv.sumCongr (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin i) (Fin 1)))
    (Equiv.refl (Fin (n-i)))).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin i) (Fin (n - i))).trans <|
  Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv.trans (finCongr (by omega)))

lemma finExtractOne_apply_eq {n : ℕ} (i : Fin n.succ) :
    finExtractOne i i = Sum.inl 0 := by
  simp only [Nat.succ_eq_add_one, finExtractOne, Equiv.trans_apply, finCongr_apply,
    Equiv.sumCongr_apply, Equiv.coe_trans, Equiv.sumComm_apply, Equiv.coe_refl, Fin.isValue]
  have h1 :
      Fin.cast (finExtractOne.proof_1 i) i = Fin.castAdd ((n - ↑i)) ⟨i.1, lt_add_one i.1⟩ := by
    rfl
  rw [h1, finSumFinEquiv_symm_apply_castAdd]
  simp only [Nat.succ_eq_add_one, Sum.map_inl, Function.comp_apply, Fin.isValue]
  have h2 : @Fin.mk (↑i + 1) ↑i (lt_add_one i.1) = Fin.natAdd i.val 1 := rfl
  rw [h2, finSumFinEquiv_symm_apply_natAdd]
  rfl

lemma finExtractOne_symm_inr {n : ℕ} (i : Fin n.succ) :
    (finExtractOne i).symm ∘ Sum.inr = i.succAbove := by
  ext x
  simp only [Nat.succ_eq_add_one, finExtractOne, Function.comp_apply, Equiv.symm_trans_apply,
    finCongr_symm, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply,
    Equiv.coe_refl, Sum.map_inr, finCongr_apply, Fin.coe_cast]
  change (finSumFinEquiv
    (Sum.map (⇑(finSumFinEquiv.symm.trans (Equiv.sumComm (Fin ↑i) (Fin 1))).symm) id
    ((Equiv.sumAssoc (Fin 1) (Fin ↑i) (Fin (n - i))).symm
    (Sum.inr (finSumFinEquiv.symm (Fin.cast (finExtractOne.proof_2 i).symm x)))))).val = _
  by_cases hi : x.1 < i.1
  · have h1 : (finSumFinEquiv.symm (Fin.cast (finExtractOne.proof_2 i).symm x)) =
        Sum.inl ⟨x, hi⟩ := by
      rw [← finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h1]
    simp only [Nat.succ_eq_add_one, Equiv.sumAssoc_symm_apply_inr_inl, Sum.map_inl,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumComm_symm, Equiv.sumComm_apply,
      Sum.swap_inr, finSumFinEquiv_apply_left, Fin.castAdd_mk]
    rw [Fin.succAbove]
    split
    · rfl
    rename_i hn
    simp_all only [Nat.succ_eq_add_one, not_lt, Fin.le_def, Fin.coe_castSucc, Fin.val_succ,
      self_eq_add_right, one_ne_zero]
    omega
  · have h1 : (finSumFinEquiv.symm (Fin.cast (finExtractOne.proof_2 i).symm x)) =
        Sum.inr ⟨x - i, by omega⟩ := by
      rw [← finSumFinEquiv_symm_apply_natAdd]
      apply congrArg
      ext
      simp only [Nat.succ_eq_add_one, Fin.coe_cast, Fin.natAdd_mk]
      omega
    rw [h1, Fin.succAbove]
    split
    · rename_i hn
      simp_all [Fin.lt_def]
    simp only [Nat.succ_eq_add_one, Equiv.sumAssoc_symm_apply_inr_inr, Sum.map_inr, id_eq,
      finSumFinEquiv_apply_right, Fin.natAdd_mk, Fin.val_succ]
    omega

@[simp]
lemma finExtractOne_symm_inr_apply {n : ℕ} (i : Fin n.succ) (x : Fin n) :
    (finExtractOne i).symm (Sum.inr x) = i.succAbove x := calc
  _ = ((finExtractOne i).symm ∘ Sum.inr) x := rfl
  _ = i.succAbove x := by rw [finExtractOne_symm_inr]

@[simp]
lemma finExtractOne_symm_inl_apply {n : ℕ} (i : Fin n.succ) :
    (finExtractOne i).symm (Sum.inl 0) = i := by
  rfl

/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the map `Fin n.succ → Fin n.succ` obtained by dropping `i` and it's image. -/
def finExtractOnPermHom (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ) :
    Fin n.succ → Fin n.succ := fun x => predAboveI (σ i) (σ ((finExtractOne i).symm (Sum.inr x)))

lemma finExtractOnPermHom_inv (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ) :
    (finExtractOnPermHom (σ i) σ.symm) ∘ (finExtractOnPermHom i σ) = id := by
  funext x
  simp only [Nat.succ_eq_add_one, Function.comp_apply, finExtractOnPermHom, Equiv.symm_apply_apply,
    finExtractOne_symm_inr_apply, id_eq]
  by_cases h : σ (i.succAbove x) < σ i
  · rw [predAboveI_lt h, Fin.succAbove_of_castSucc_lt]
    · simp
    · simp_all [Fin.lt_def]
  have hσ : σ (i.succAbove x) ≠ σ i := by
    simp only [Nat.succ_eq_add_one, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact Fin.succAbove_ne i x
  have hn : σ i < σ (i.succAbove x) := by omega
  rw [predAboveI_ge hn]
  rw [Fin.succAbove_of_le_castSucc]
  · simp only [Nat.succ_eq_add_one, Fin.succ_mk]
    trans predAboveI i (σ.symm (σ (i.succAbove x)))
    · congr
      exact Nat.sub_add_cancel (Fin.lt_of_le_of_lt (Fin.zero_le (σ i)) hn)
    simp
  rw [Fin.le_def]
  simp only [Nat.succ_eq_add_one, Fin.castSucc_mk]
  omega

/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the equivalence `Fin n.succ ≃ Fin n.succ` obtained by dropping `i` and it's image. -/
def finExtractOnePerm (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ) :
    Fin n.succ ≃ Fin n.succ where
  toFun x := finExtractOnPermHom i σ x
  invFun x := finExtractOnPermHom (σ i) σ.symm x
  left_inv x := by
    simpa using congrFun (finExtractOnPermHom_inv i σ) x
  right_inv x := by
    simpa using congrFun (finExtractOnPermHom_inv (σ i) σ.symm) x

/-- The equivalence of types `Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n` extracting
  the `i` and `(i.succAbove j)`. -/
def finExtractTwo {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n :=
  (finExtractOne i).trans <|
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (finExtractOne j)).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin 1) (Fin n)).symm

@[simp]
lemma finExtractTwo_apply_fst {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    finExtractTwo i j i = Sum.inl (Sum.inl 0) := by
  simp only [Nat.succ_eq_add_one, finExtractTwo, Equiv.trans_apply, Equiv.sumCongr_apply,
    Equiv.coe_refl, Fin.isValue]
  simp [finExtractOne_apply_eq]

lemma finExtractTwo_symm_inr {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm ∘ Sum.inr = i.succAbove ∘ j.succAbove := by
  rw [finExtractTwo]
  ext1 x
  simp

@[simp]
lemma finExtractTwo_symm_inr_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) (x : Fin n) :
    (finExtractTwo i j).symm (Sum.inr x) = i.succAbove (j.succAbove x) := by
  rw [finExtractTwo]
  simp

@[simp]
lemma finExtractTwo_symm_inl_inr_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm (Sum.inl (Sum.inr 0)) = i.succAbove j := by
  rw [finExtractTwo]
  simp

@[simp]
lemma finExtractTwo_symm_inl_inl_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm (Sum.inl (Sum.inl 0)) = i := by rfl

@[simp]
lemma finExtractTwo_apply_snd {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    finExtractTwo i j (i.succAbove j) = Sum.inl (Sum.inr 0) := by
  rw [← Equiv.eq_symm_apply]
  simp

end HepLean.Fin
