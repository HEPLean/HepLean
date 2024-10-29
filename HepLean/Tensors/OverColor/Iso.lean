/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Functors
import HepLean.Tensors.OverColor.Lift
import HepLean.Mathematics.Fin
/-!

## Isomorphisms in the OverColor category

-/
namespace IndexNotation
namespace OverColor
open CategoryTheory
open MonoidalCategory
open HepLean.Fin
/-!

## Useful equivalences.

-/

/-- The isomorphism between `c : X → C` and `c ∘ e.symm` as objects in `OverColor C` for an
  equivalence `e`. -/
def equivToIso {c : X → C} (e : X ≃ Y) : mk c ≅ mk (c ∘ e.symm) :=
  Hom.toIso (Over.isoMk e.toIso ((Iso.eq_inv_comp e.toIso).mp rfl))

@[simp]
lemma equivToIso_homToEquiv {c : X → C} (e : X ≃ Y) :
    Hom.toEquiv (equivToIso (c := c) e).hom = e := by
  rfl

/-- The homomorphism between `c : X → C` and `c ∘ e.symm` as objects in `OverColor C` for an
  equivalence `e`. -/
def equivToHom {c : X → C} (e : X ≃ Y) : mk c ⟶ mk (c ∘ e.symm) :=
  (equivToIso e).hom

/-- Given a map `X ⊕ Y → C`, the isomorphism `mk c ≅ mk (c ∘ Sum.inl) ⊗ mk (c ∘ Sum.inr)`. -/
def mkSum (c : X ⊕ Y → C) : mk c ≅ mk (c ∘ Sum.inl) ⊗ mk (c ∘ Sum.inr) :=
  Hom.toIso (Over.isoMk (Equiv.refl _).toIso (by
    ext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl))

@[simp]
lemma mkSum_homToEquiv {c : X ⊕ Y → C}:
    Hom.toEquiv (mkSum c).hom = (Equiv.refl _) := by
  rfl

@[simp]
lemma mkSum_inv_homToEquiv {c : X ⊕ Y → C}:
    Hom.toEquiv (mkSum c).inv = (Equiv.refl _) := by
  rfl

/-- The isomorphism between objects in `OverColor C` given equality of maps. -/
def mkIso {c1 c2 : X → C} (h : c1 = c2) : mk c1 ≅ mk c2 :=
  Hom.toIso (Over.isoMk (Equiv.refl _).toIso (by
    subst h
    rfl))

lemma mkIso_refl_hom {c : X → C} : (mkIso (by rfl : c =c)).hom = 𝟙 _ := by
  rw [mkIso]
  rfl

@[simp]
lemma equivToIso_mkIso_hom {c1 c2 : X → C} (h : c1 = c2) :
    Hom.toEquiv (mkIso h).hom = Equiv.refl _ := by
  rfl

@[simp]
lemma equivToIso_mkIso_inv {c1 c2 : X → C} (h : c1 = c2) :
    Hom.toEquiv (mkIso h).inv = Equiv.refl _ := by
  rfl

/-- The homorophism from `mk c` to `mk c1` obtaied by an equivalence and
  an equality lemma. -/
def equivToHomEq {c : X → C} {c1 : Y → C} (e : X ≃ Y)
    (h : ∀ x, c1 x = (c ∘ e.symm) x := by decide) : mk c ⟶ mk c1 :=
  (equivToHom e).trans (mkIso (funext fun x => (h x).symm)).hom

/-- The isomorphism splitting a `mk c` for `Fin 2 → C` into the tensor product of
  the `Fin 1 → C` maps defined by `c 0` and `c 1`. -/
def fin2Iso {c : Fin 2 → C} : mk c ≅ mk ![c 0] ⊗ mk ![c 1] := by
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

/-- The isomorphism splitting a `mk c` for `c : Fin 3 → C` into the tensor product of
  a `Fin 1 → C` map `![c 0]` and a `Fin 2 → C` map `![c 1, c 2]`. -/
def fin3Iso {c : Fin 3 → C} : mk c ≅ mk ![c 0] ⊗ mk ![c 1, c 2] := by
  let e1 : Fin 3 ≃ Fin 1 ⊕ Fin 2 := (finSumFinEquiv (n := 2)).symm
  apply (equivToIso e1).trans
  apply (mkSum _).trans
  refine tensorIso (mkIso ?_) (mkIso ?_)
  · funext x
    fin_cases x
    rfl
  · funext x
    fin_cases x
    rfl
    rfl

/-- The isomorphism splitting a `mk ![c1, c2, c3]` into the tensor product of
  a `Fin 1 → C` map `fun _ => c1` and a `Fin 2 → C` map `![c 1, c 2]`. -/
def fin3Iso' {c1 c2 c3 : C} : mk ![c1, c2, c3] ≅ mk (fun (_ : Fin 1) => c1) ⊗ mk ![c2, c3] := by
  let e1 : Fin 3 ≃ Fin 1 ⊕ Fin 2 := (finSumFinEquiv (n := 2)).symm
  apply (equivToIso e1).trans
  apply (mkSum _).trans
  refine tensorIso (mkIso ?_) (mkIso ?_)
  · funext x
    fin_cases x
    rfl
  · funext x
    fin_cases x
    rfl
    rfl

/-- Removes a given `i : Fin n.succ.succ` from a morphism in `OverColor C`. -/
def extractOne {n : ℕ} (i : Fin n.succ.succ)
    {c1 c2 : Fin n.succ.succ → C} (σ : mk c1 ⟶ mk c2) :
    mk (c1 ∘ Fin.succAbove ((Hom.toEquiv σ).symm i)) ⟶ mk (c2 ∘ Fin.succAbove i) :=
  equivToHomEq ((finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ))) (by
    intro x
    simp_all only [Nat.succ_eq_add_one, Function.comp_apply]
    have h1 := Hom.toEquiv_comp_inv_apply σ (i.succAbove x)
    simp only [Nat.succ_eq_add_one, Functor.const_obj_obj, mk_hom] at h1
    rw [← h1]
    apply congrArg
    simp only [finExtractOnePerm, Nat.succ_eq_add_one, finExtractOnPermHom,
      finExtractOne_symm_inr_apply, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
    erw [Equiv.apply_symm_apply]
    rw [succsAbove_predAboveI]
    · rfl
    simp only [Nat.succ_eq_add_one, ne_eq]
    erw [Equiv.apply_eq_iff_eq]
    exact (Fin.succAbove_ne i x).symm)

@[simp]
lemma extractOne_homToEquiv {n : ℕ} (i : Fin n.succ.succ)
    {c1 c2 : Fin n.succ.succ → C} (σ : mk c1 ⟶ mk c2) : Hom.toEquiv (extractOne i σ) =
    (finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)) := by
  rfl

/-- Removes a given `i : Fin n.succ.succ` and `j : Fin n.succ` from a morphism in `OverColor C`. -/
def extractTwo {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ)
    {c1 c2 : Fin n.succ.succ → C} (σ : mk c1 ⟶ mk c2) :
    mk (c1 ∘ Fin.succAbove ((Hom.toEquiv σ).symm i) ∘
      Fin.succAbove (((Hom.toEquiv (extractOne i σ))).symm j)) ⟶
    mk (c2 ∘ Fin.succAbove i ∘ Fin.succAbove j) :=
  match n with
  | 0 => equivToHomEq (Equiv.refl _) (by simp)
  | Nat.succ n =>
    equivToHomEq (Equiv.refl _) (by simp) ≫ extractOne j (extractOne i σ) ≫
    equivToHomEq (Equiv.refl _) (by simp)

/-- Removes a given `i : Fin n.succ.succ` and `j : Fin n.succ` from a morphism in `OverColor C`.
  This is from and to different (by equivalent) objects to `extractTwo`. -/
def extractTwoAux {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ)
    {c c1 : Fin n.succ.succ → C} (σ : mk c ⟶ mk c1) :
    mk ((c ∘ ⇑(finExtractTwo ((Hom.toEquiv σ).symm i)
    ((Hom.toEquiv (extractOne i σ)).symm j)).symm) ∘ Sum.inr) ⟶
    mk ((c1 ∘ ⇑(finExtractTwo i j).symm) ∘ Sum.inr) :=
  equivToHomEq (Equiv.refl _) (by simp) ≫ extractTwo i j σ ≫ equivToHomEq (Equiv.refl _) (by simp)

/-- Given a morphism ` mk c ⟶ mk c1` the corresponding morphism on the `Fin 1 ⊕ Fin 1` maps
  obtained by extracting `i` and `j`. -/
def extractTwoAux' {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ)
    {c c1 : Fin n.succ.succ → C} (σ : mk c ⟶ mk c1) :
  mk ((c ∘ ⇑(finExtractTwo ((Hom.toEquiv σ).symm i)
  ((Hom.toEquiv (extractOne i σ)).symm j)).symm) ∘ Sum.inl) ⟶
  mk ((c1 ∘ ⇑(finExtractTwo i j).symm) ∘ Sum.inl) :=
  equivToHomEq (Equiv.refl _) (by
    intro x
    simp only [Nat.succ_eq_add_one, Function.comp_apply, extractOne_homToEquiv, Equiv.refl_symm,
      Equiv.coe_refl, id_eq]
    match x with
    | Sum.inl 0=>
      simp only [Fin.isValue, finExtractTwo_symm_inl_inl_apply]
      have h1 := Hom.toEquiv_comp_inv_apply σ i
      simpa using h1.symm
    | Sum.inr 0 =>
      simp only [Fin.isValue, finExtractTwo_symm_inl_inr_apply]
      have h1 := Hom.toEquiv_comp_inv_apply σ (i.succAbove j)
      simp only [Nat.succ_eq_add_one, Functor.const_obj_obj, mk_hom] at h1
      rw [← h1]
      congr
      simp only [Nat.succ_eq_add_one, finExtractOnePerm, finExtractOnPermHom,
        finExtractOne_symm_inr_apply, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
      erw [Equiv.apply_symm_apply]
      rw [succsAbove_predAboveI]
      rfl
      simp only [Nat.succ_eq_add_one, ne_eq]
      erw [Equiv.apply_eq_iff_eq]
      exact (Fin.succAbove_ne i j).symm)

lemma extractTwo_finExtractTwo_succ {n : ℕ} (i : Fin n.succ.succ.succ) (j : Fin n.succ.succ)
    {c c1 : Fin n.succ.succ.succ → C} (σ : mk c ⟶ mk c1) :
    σ ≫ (equivToIso (HepLean.Fin.finExtractTwo i j)).hom ≫
    (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom =
    (equivToIso (HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j))).hom
    ≫ (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j)).symm)).hom
    ≫ ((extractTwoAux' i j σ) ⊗ (extractTwoAux i j σ)) := by
  apply IndexNotation.OverColor.Hom.ext
  ext x
  simp only [Nat.succ_eq_add_one, instMonoidalCategoryStruct_tensorObj_left, CategoryStruct.comp,
    equivToIso, Hom.toIso, mkSum, Iso.trans_hom, Over.isoMk_hom_left, Equiv.toIso_hom,
    Discrete.mk_as, instMonoidalCategoryStruct_tensorObj_right_as, CostructuredArrow.right_eq_id,
    ULift.rec.constant, Function.comp_apply, extractOne_homToEquiv, extractTwoAux', extractTwoAux,
    instMonoidalCategoryStruct_tensorHom_hom_left]
  change ((finExtractTwo i j) ((Hom.toEquiv σ) x)) = Sum.map id
    ((finExtractOnePerm ((finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)
    (finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ))))
    (((finExtractTwo ((Hom.toEquiv σ).symm i)
    ((finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)) x))
  simp only [Nat.succ_eq_add_one]
  obtain ⟨k, hk⟩ := (finExtractTwo ((Hom.toEquiv σ).symm i)
      ((finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)).symm.surjective x
  subst hk
  simp only [Nat.succ_eq_add_one, Equiv.apply_symm_apply]
  match k with
  | Sum.inl (Sum.inl 0) =>
    simp
  | Sum.inl (Sum.inr 0) =>
    simp only [Fin.isValue, finExtractTwo_symm_inl_inr_apply, Sum.map_inl, id_eq]
    have h1 : ((Hom.toEquiv σ) (Fin.succAbove
        ((Hom.toEquiv σ).symm i)
        ((finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j))) =
        i.succAbove j := by
      simp only [Nat.succ_eq_add_one, finExtractOnePerm, finExtractOnPermHom,
        finExtractOne_symm_inr_apply, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
      erw [Equiv.apply_symm_apply]
      rw [succsAbove_predAboveI]
      exact Equiv.apply_symm_apply (Hom.toEquiv σ) (i.succAbove j)
      simp only [Nat.succ_eq_add_one, ne_eq]
      erw [Equiv.apply_eq_iff_eq]
      exact (Fin.succAbove_ne i j).symm
    rw [h1]
    erw [Equiv.apply_eq_iff_eq_symm_apply]
    simp
  | Sum.inr x =>
    simp only [finExtractTwo_symm_inr_apply, Sum.map_inr]
    erw [Equiv.apply_eq_iff_eq_symm_apply]
    simp only [finExtractTwo_symm_inr_apply]
    simp only [finExtractOnePerm, Nat.succ_eq_add_one, finExtractOnPermHom,
      finExtractOne_symm_inr_apply, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
    erw [Equiv.apply_symm_apply]
    have h1 : (predAboveI i ((Hom.toEquiv σ)
        (Fin.succAbove ((Hom.toEquiv σ).symm i)
        (predAboveI ((Hom.toEquiv σ).symm i) ((Hom.toEquiv σ).symm (i.succAbove j)))))) = j := by
      rw [succsAbove_predAboveI]
      · erw [Equiv.apply_symm_apply]
        simp
      · simp only [Nat.succ_eq_add_one, ne_eq]
        erw [Equiv.apply_eq_iff_eq]
        exact (Fin.succAbove_ne i j).symm
    erw [h1]
    let y := (Hom.toEquiv σ) (Fin.succAbove ((Hom.toEquiv σ).symm i)
      ((predAboveI ((Hom.toEquiv σ).symm i) ((Hom.toEquiv σ).symm (i.succAbove j))).succAbove x))
    change y = i.succAbove (j.succAbove (predAboveI j (predAboveI i y)))
    have hy : i ≠ y := by
      simp only [Nat.succ_eq_add_one, ne_eq, y]
      erw [← Equiv.symm_apply_eq]
      exact (Fin.succAbove_ne _ _).symm
    rw [succsAbove_predAboveI, succsAbove_predAboveI]
    exact hy
    simp only [Nat.succ_eq_add_one, ne_eq]
    rw [predAboveI_eq_iff]
    simp only [Nat.succ_eq_add_one, y]
    erw [← Equiv.symm_apply_eq]
    have h0 : (Hom.toEquiv σ).symm (i.succAbove j) =
      Fin.succAbove ((Hom.toEquiv σ).symm i)
        (predAboveI ((Hom.toEquiv σ).symm i) ((Hom.toEquiv σ).symm (i.succAbove j))) := by
      rw [succsAbove_predAboveI]
      simp only [Nat.succ_eq_add_one, ne_eq]
      erw [Equiv.apply_eq_iff_eq]
      exact (Fin.succAbove_ne i j).symm
    by_contra hn
    have hn' := hn.symm.trans h0
    erw [Fin.succAbove_right_injective.eq_iff] at hn'
    exact Fin.succAbove_ne
      (predAboveI ((Hom.toEquiv σ).symm i) ((Hom.toEquiv σ).symm (i.succAbove j))) x hn'
    exact hy

lemma extractTwo_finExtractTwo {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ)
    {c c1 : Fin n.succ.succ → C} (σ : mk c ⟶ mk c1) :
    σ ≫ (equivToIso (HepLean.Fin.finExtractTwo i j)).hom ≫
    (mkSum (c1 ∘ ⇑(HepLean.Fin.finExtractTwo i j).symm)).hom =
    (equivToIso (HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j))).hom
    ≫ (mkSum (c ∘ ⇑(HepLean.Fin.finExtractTwo ((Hom.toEquiv σ).symm i)
    (((Hom.toEquiv (extractOne i σ))).symm j)).symm)).hom
    ≫ ((extractTwoAux' i j σ) ⊗ (extractTwoAux i j σ)) := by
  match n with
  | 0 =>
    apply IndexNotation.OverColor.Hom.ext
    ext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, instMonoidalCategoryStruct_tensorObj_left,
      CategoryStruct.comp, equivToIso, Hom.toIso, mkSum, Iso.trans_hom, Over.isoMk_hom_left,
      Equiv.toIso_hom, Discrete.mk_as, instMonoidalCategoryStruct_tensorObj_right_as,
      CostructuredArrow.right_eq_id, ULift.rec.constant, Function.comp_apply, extractOne_homToEquiv,
      extractTwoAux', extractTwoAux, instMonoidalCategoryStruct_tensorHom_hom_left]
    change ((finExtractTwo i j) (σ.hom.left x)) = Sum.map (Equiv.refl _) (Equiv.refl _) _
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equiv.coe_refl, Sum.map_id_id, id_eq]
    change (finExtractTwo i j) ((Hom.toEquiv σ) x) = ((finExtractTwo ((Hom.toEquiv σ).symm i)
      ((finExtractOnePerm ((Hom.toEquiv σ).symm i) (Hom.toEquiv σ)).symm j)) x)
    obtain ⟨k, hk⟩ := (Hom.toEquiv σ).symm.surjective x
    subst hk
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equiv.apply_symm_apply]
    have hk : k = i ∨ k = i.succAbove j := by
      match i, j, k with
      | (0 : Fin 2), (0 : Fin 1), (0 : Fin 2) => exact Or.intro_left (0 = Fin.succAbove 0 0) rfl
      | (0 : Fin 2), (0 : Fin 1), (1 : Fin 2) => exact Or.inr rfl
      | (1 : Fin 2), (0 : Fin 1), (0 : Fin 2) => exact Or.inr rfl
      | (1 : Fin 2), (0 : Fin 1), (1 : Fin 2) => exact Or.intro_left (1 = Fin.succAbove 1 0) rfl
    rcases hk with hk | hk
    subst hk
    simp only [finExtractTwo_apply_fst, Fin.isValue]
    subst hk
    simp only [finExtractTwo_apply_snd, Fin.isValue]
    rw [← Equiv.symm_apply_eq]
    simp only [finExtractOnePerm, Nat.succ_eq_add_one, Nat.reduceAdd, finExtractOnPermHom,
      finExtractOne_symm_inr_apply, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk, Fin.isValue,
      finExtractTwo_symm_inl_inr_apply]
    erw [Equiv.apply_symm_apply]
    rw [succsAbove_predAboveI]
    rfl
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ne_eq]
    erw [Equiv.apply_eq_iff_eq]
    exact (Fin.succAbove_ne i j).symm
  | Nat.succ n => exact extractTwo_finExtractTwo_succ i j σ

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

/-- This a function that takes a function `c` from `Fin 2` to `C` and
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
