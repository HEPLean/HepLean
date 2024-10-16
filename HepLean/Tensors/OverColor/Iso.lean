/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Functors
import HepLean.Tensors.OverColor.Lift
/-!

## Isomorphisms in the OverColor category

-/
namespace IndexNotation
namespace OverColor
open CategoryTheory
open MonoidalCategory

/-!

## Useful equivalences.

-/

/-- The isomorphism between `c : X → C` and `c ∘ e.symm` as objects in `OverColor C` for an
  equivalence `e`. -/
def equivToIso {c : X → C} (e : X ≃ Y) : mk c ≅ mk (c ∘ e.symm) :=
  Hom.toIso (Over.isoMk e.toIso ((Iso.eq_inv_comp e.toIso).mp rfl))

/-- Given a map `X ⊕ Y → C`, the isomorphism `mk c ≅ mk (c ∘ Sum.inl) ⊗ mk (c ∘ Sum.inr)`. -/
def mkSum (c : X ⊕ Y → C) : mk c ≅ mk (c ∘ Sum.inl) ⊗ mk (c ∘ Sum.inr) :=
  Hom.toIso (Over.isoMk (Equiv.refl _).toIso (by
    ext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl))

/-- The isomorphism between objects in `OverColor C` given equality of maps. -/
def mkIso {c1 c2 : X → C} (h : c1 = c2) : mk c1 ≅ mk c2 :=
  Hom.toIso (Over.isoMk (Equiv.refl _).toIso (by
    subst h
    rfl))

/-- The isomorphism splitting a `mk c` for `Fin 2 → C` into the tensor product of
  the `Fin 1 → C` maps defined by `c 0` and `c 1`. -/
def fin2Iso {c : Fin 2 → C} : mk c ≅ mk ![c 0] ⊗ mk ![c 1] :=by
  let e1 : Fin 2 ≃ Fin 1 ⊕ Fin 1 := (finSumFinEquiv (n := 1)).symm
  apply (equivToIso e1).trans
  apply (mkSum _).trans
  refine tensorIso (mkIso ?_) (mkIso ?_)
  · funext x
    fin_cases x
    rfl
  · funext x
    fin_cases x
    rfl

/-- The equivalence between `Fin n.succ` and `Fin 1 ⊕ Fin n` extracting the
  `i`th component. -/
def finExtractOne {n : ℕ} (i : Fin n.succ) : Fin n.succ ≃ Fin 1 ⊕ Fin n :=
  (finCongr (by omega : n.succ = i + 1 + (n - i))).trans <|
  finSumFinEquiv.symm.trans <|
  (Equiv.sumCongr (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin i) (Fin 1)))
    (Equiv.refl (Fin (n-i)))).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin i) (Fin (n - i))).trans <|
  Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv.trans (finCongr (by omega)))

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
      apply congrArg
      ext
      simp
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
  simp only [Nat.succ_eq_add_one, finExtractOne, Fin.isValue, Equiv.symm_trans_apply, finCongr_symm,
    Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.coe_refl,
    Sum.map_inl, id_eq, Equiv.sumAssoc_symm_apply_inl, Equiv.sumComm_symm, Equiv.sumComm_apply,
    Sum.swap_inl, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, finCongr_apply]
  ext
  rfl

/-- The equivalence of types `Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n` extracting
  the `i` and `(i.succAbove j)`. -/
def finExtractTwo {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n :=
  (finExtractOne i).trans <|
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (finExtractOne j)).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin 1) (Fin n)).symm

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
    (finExtractTwo i j).symm (Sum.inl (Sum.inl 0)) = i := by
  rw [finExtractTwo]
  simp

/-- The isomorphism between a `Fin 1 ⊕ Fin 1 → C` satisfying the condition
  `c (Sum.inr 0) = τ (c (Sum.inl 0))`
  and an object in the image of `contrPair`. -/
def contrPairFin1Fin1 (τ : C → C) (c : Fin 1 ⊕ Fin 1 → C)
    (h : c (Sum.inr 0) = τ (c (Sum.inl 0))) :
    OverColor.mk c ≅ (contrPair C τ).obj (OverColor.mk (fun (_ : Fin 1) => c (Sum.inl 0))) :=
  Hom.toIso (Over.isoMk (Equiv.refl _).toIso (by
    ext x
    match x with
    | Sum.inl x =>
      fin_cases x
      rfl
    | Sum.inr x =>
      fin_cases x
      change _ = c (Sum.inr 0)
      rw [h]
      rfl))

variable {k : Type} [CommRing k] {G : Type} [Group G]


/-- The Isomorphism between a `Fin n.succ.succ → C` and the product containing an object in the
  image of `contrPair` based on the given values. -/
def contrPairEquiv {n : ℕ} (τ : C → C) (c : Fin n.succ.succ → C) (i : Fin n.succ.succ)
    (j : Fin n.succ) (h : c (i.succAbove j) = τ (c i)) :
    OverColor.mk c ≅ ((contrPair C τ).obj (Over.mk (fun (_ : Fin 1) => c i))) ⊗
    (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (equivToIso (finExtractTwo i j)).trans <|
  (OverColor.mkSum (c ∘ ⇑(finExtractTwo i j).symm)).trans <|
  tensorIso
    (contrPairFin1Fin1 τ ((c ∘ ⇑(finExtractTwo i j).symm) ∘ Sum.inl) (by simpa using h)) <|
    mkIso (by ext x; simp)


/-- Given a function `c` from `Fin 1` to `C`, this function returns a morphism
  from `mk c` to `mk ![c 0]`. --/
def permFinOne (c : Fin 1 → C) : mk c ⟶ mk ![c 0] :=
  (mkIso (by
    funext x
    fin_cases x
    rfl)).hom

/-- This a function that takes a function `c` from `Fin 2` to  `C` and
returns a morphism from `mk c` to `mk ![c 0, c 1]`. --/
def permFinTwo (c : Fin 2 → C) : mk c ⟶ mk ![c 0, c 1] :=
  (mkIso (by
    funext x
    fin_cases x <;>
    rfl)).hom

/-- This is a function that takes a function `c` from `Fin 3` to `C` and returns a morphism
  from `mk c` to `mk ![c 0, c 1, c 2]`. --/
def permFinThree (c : Fin 3 → C) : mk c ⟶ mk ![c 0, c 1, c 2] :=
  (mkIso (by
    funext x
    fin_cases x <;>
    rfl)).hom


end OverColor
end IndexNotation
