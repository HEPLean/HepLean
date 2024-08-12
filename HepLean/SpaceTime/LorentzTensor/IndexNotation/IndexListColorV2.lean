/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.DualIndex
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Index lists with color conditions

Here we consider `IndexListColor` which is a subtype of all lists of indices
on those where the elements to be contracted have consistent colors with respect to
a Tensor Color structure.

-/

namespace IndexNotation

def IndexListColor (𝓒 : TensorColor) [IndexNotation 𝓒.Color] : Type :=
  {l // (l : IndexList 𝓒.Color).HasSingColorDualsInSelf}

namespace IndexListColor

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l : IndexListColor 𝓒)

def length : ℕ := l.1.length

def HasNoDualsSelf : Prop := l.1.HasNoDualsSelf

def getDual? (i : Fin l.length) : Option (Fin l.length) :=
  if h : l.1.HasSingColorDualInSelf i then
    some h.get
  else none

def withDualFinset : Finset (Fin l.length) := Finset.filter l.1.HasSingColorDualInSelf Finset.univ

lemma withDualFinset_prop {l : IndexListColor 𝓒} (i : l.withDualFinset) :
    l.1.HasSingColorDualInSelf i.1 := by
  simpa [withDualFinset] using i.2

def withDualFinsetLT : Finset l.withDualFinset :=
  Finset.filter (fun i => i.1 < (withDualFinset_prop i).get) Finset.univ

def withDualFinsetGT : Finset l.withDualFinset :=
  Finset.filter (fun i => (withDualFinset_prop i).get < i.1) Finset.univ

def withDualFinsetLTGTEquiv : l.withDualFinsetLT ≃ l.withDualFinsetGT where
  toFun x := ⟨⟨(withDualFinset_prop x.1).get,
    by simpa [withDualFinset] using (withDualFinset_prop x.1).get_hasSingColorDualInSelf⟩, by
    simpa [withDualFinsetGT, withDualFinsetLT] using x.2⟩
  invFun x := ⟨⟨(withDualFinset_prop x.1).get,
    by simpa [withDualFinset] using (withDualFinset_prop x.1).get_hasSingColorDualInSelf⟩, by
    simpa [withDualFinsetGT, withDualFinsetLT] using x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [length, IndexList.HasSingColorDualInSelf.get_get]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [length, IndexList.HasSingColorDualInSelf.get_get]

lemma withDualFinsetLT_disjoint_withDualFinsetGT :
    Disjoint l.withDualFinsetLT l.withDualFinsetGT := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  by_contra hn
  subst hn
  simp [withDualFinsetLT, withDualFinsetGT] at ha hb
  omega

lemma mem_withDualFinsetLT_union_withDualFinsetGT (x : l.withDualFinset) :
    x ∈ l.withDualFinsetLT ∪ l.withDualFinsetGT := by
  simpa [withDualFinsetLT, withDualFinsetGT] using (withDualFinset_prop x).areDualInSelf_get.1

def withDualEquiv : l.withDualFinsetLT ⊕ l.withDualFinsetLT ≃ l.withDualFinset :=
  (Equiv.sumCongr (Equiv.refl _) l.withDualFinsetLTGTEquiv).trans <|
  (Equiv.Finset.union _ _ l.withDualFinsetLT_disjoint_withDualFinsetGT).trans <|
  Equiv.subtypeUnivEquiv l.mem_withDualFinsetLT_union_withDualFinsetGT

def withoutDualFinset : Finset (Fin l.length) :=
  Finset.filter (fun i => ¬ l.1.HasDualInSelf i) Finset.univ

lemma mem_withoutDualFinset_iff_not_hasSingColorDualInSelf (i : Fin l.length) :
    i ∈ l.withoutDualFinset ↔ ¬ l.1.HasSingColorDualInSelf i := by
  simp [withoutDualFinset]
  exact l.2.not_hasDualInSelf_iff_not_hasSingColorDualInSelf i

lemma mem_withoutDualFinset_of_hasNoDualsSelf (h : l.HasNoDualsSelf) (i : Fin l.length) :
    i ∈ l.withoutDualFinset := by
  simpa [withoutDualFinset] using h i

lemma withoutDualFinset_of_hasNoDualsSelf (h : l.HasNoDualsSelf) :
    l.withoutDualFinset = Finset.univ := by
  rw [@Finset.eq_univ_iff_forall]
  exact l.mem_withoutDualFinset_of_hasNoDualsSelf h

lemma withDualFinset_disjoint_withoutDualFinset :
    Disjoint l.withDualFinset l.withoutDualFinset := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  by_contra hn
  subst hn
  rw [mem_withoutDualFinset_iff_not_hasSingColorDualInSelf] at hb
  simp [withDualFinset, withoutDualFinset] at ha hb
  exact hb ha

lemma mem_withDualFinset_union_withoutDualFinset (x : Fin l.length) :
    x ∈ l.withDualFinset ∪ l.withoutDualFinset := by
  simp [withDualFinset]
  rw [mem_withoutDualFinset_iff_not_hasSingColorDualInSelf]
  exact Decidable.em (l.1.HasSingColorDualInSelf x)

def dualEquiv : l.withDualFinset ⊕ l.withoutDualFinset ≃ Fin l.length :=
  (Equiv.Finset.union _ _ l.withDualFinset_disjoint_withoutDualFinset).trans <|
  Equiv.subtypeUnivEquiv l.mem_withDualFinset_union_withoutDualFinset

def withoutDualEquiv : Fin l.withoutDualFinset.card ≃ l.withoutDualFinset  :=
  (Finset.orderIsoOfFin _ rfl).toEquiv


def withoutDualIndexList : IndexList 𝓒.Color :=
  (Fin.list l.withoutDualFinset.card).map (fun i => l.1.get (l.withoutDualEquiv i).1)

@[simp]
lemma withoutDualIndexList_idMap (i :  Fin (List.length l.withoutDualIndexList)) :
    l.withoutDualIndexList.idMap i =
    l.1.idMap (l.withoutDualEquiv (Fin.cast (by simp [withoutDualIndexList]) i)).1 := by
  simp [withoutDualIndexList, IndexList.idMap]
  rfl

lemma withoutDualIndexList_hasNoDualsSelf : l.withoutDualIndexList.HasNoDualsSelf := by
  intro i
  simp [IndexList.HasDualInSelf, IndexList.AreDualInSelf]
  intro x hx
  have h1 : l.withoutDualEquiv (Fin.cast (by simp [withoutDualIndexList]) i) ≠
      l.withoutDualEquiv (Fin.cast (by simp [withoutDualIndexList]) x)  := by
    simp
    rw [Fin.ext_iff] at hx ⊢
    simpa using hx
  have hx' := (l.withoutDualEquiv (Fin.cast (by simp [withoutDualIndexList]) i)).2
  simp [withoutDualFinset, IndexList.HasDualInSelf, IndexList.AreDualInSelf] at hx'
  refine hx' (l.withoutDualEquiv (Fin.cast (by simp [withoutDualIndexList]) x)).1 ?_
  simp only [length]
  rw [← Subtype.eq_iff]
  exact h1

lemma withoutDualIndexList_of_hasNoDualsSelf (h : l.1.HasNoDualsSelf ) :
    l.withoutDualIndexList = l.1 := by
  simp  [withoutDualIndexList, List.get_eq_getElem]
  apply List.ext_get
  · simp only [List.length_map, Fin.length_list]
    rw [l.withoutDualFinset_of_hasNoDualsSelf h]
    simp only [Finset.card_univ, Fintype.card_fin]
    rfl
  intro n h1 h2
  simp
  congr
  simp [withoutDualEquiv]
  have h1 : l.withoutDualFinset.orderEmbOfFin rfl =
      (Fin.castOrderIso (by
        rw [l.withoutDualFinset_of_hasNoDualsSelf h]
        simp only [Finset.card_univ, Fintype.card_fin])).toOrderEmbedding := by
    symm
    refine Finset.orderEmbOfFin_unique' (Eq.refl l.withoutDualFinset.card)
      (fun x => mem_withoutDualFinset_of_hasNoDualsSelf l h _)
  rw [h1]
  rfl

def contr : IndexListColor 𝓒 :=
  ⟨l.withoutDualIndexList, l.withoutDualIndexList_hasNoDualsSelf.toHasSingColorDualsInSelf⟩

lemma contr_length : l.contr.1.length = l.withoutDualFinset.card := by
  simp [contr, withoutDualIndexList]

@[simp]
lemma contr_id (i : Fin l.contr.length) : l.contr.1.idMap i =
    l.1.idMap (l.withoutDualEquiv (Fin.cast l.contr_length i)).1  := by
  simp [contr]

lemma contr_hasNoDualsSelf : l.contr.1.HasNoDualsSelf :=
  l.withoutDualIndexList_hasNoDualsSelf

lemma contr_of_hasNoDualsSelf (h : l.1.HasNoDualsSelf) :
    l.contr = l := by
  apply Subtype.ext
  exact l.withoutDualIndexList_of_hasNoDualsSelf h

@[simp]
lemma contr_contr : l.contr.contr = l.contr :=
  l.contr.contr_of_hasNoDualsSelf l.contr_hasNoDualsSelf

/-!

# Relations on IndexListColor

-/
/-
  l.getDual? ∘ Option.guard l.HasDualInSelf =
  l.getDual?
-/
def Relabel (l1 l2 : IndexListColor 𝓒) : Prop :=
  l1.length = l2.length ∧
  ∀ (h : l1.length = l2.length),
    l1.getDual? = Option.map (Fin.cast h.symm) ∘ l2.getDual? ∘ Fin.cast h ∧
    l1.1.colorMap = l2.1.colorMap ∘ Fin.cast h

/-! TODO: Rewrite in terms of HasSingDualInOther. -/
def PermAfterContr (l1 l2 : IndexListColor 𝓒) : Prop :=
  List.Perm (l1.contr.1.map Index.id) (l2.contr.1.map Index.id)
  ∧ ∀ (i : Fin l1.contr.1.length) (j : Fin l2.contr.1.length),
      l1.contr.1.idMap i = l2.contr.1.idMap j →
      l1.contr.1.colorMap i = l2.contr.1.colorMap j

def AppendHasSingColorDualsInSelf (l1 l2 : IndexListColor 𝓒) : Prop :=
  (l1.contr.1 ++ l2.contr.1).HasSingColorDualsInSelf


end IndexListColor

/-- A proposition which is true if an index has at most one dual. -/
def HasSubSingeDualSelf (i : Fin l.length) : Prop :=
  ∀ (h : l.HasDualSelf i) j, l.AreDualSelf i j → j = l.getDualSelf i h

lemma HasSubSingeDualSelf.eq_dual_iff  {l : IndexList X} {i : Fin l.length}
    (h : l.HasSubSingeDualSelf i) (hi : l.HasDualSelf i) (j : Fin l.length) :
    j = l.getDualSelf i hi ↔ l.AreDualSelf i j := by
  have h1 := h hi j
  apply Iff.intro
  intro h
  subst h
  exact l.areDualSelf_of_getDualSelf i hi
  exact h1

@[simp]
lemma getDualSelf_append_inl {l l2 : IndexList X} (i : Fin l.length)
    (h : (l ++ l2).HasSubSingeDualSelf (appendEquiv (Sum.inl i))) (hi : l.HasDualSelf i) :
    (l ++ l2).getDualSelf (appendEquiv (Sum.inl i)) ((hasDualSelf_append_inl l l2 i).mpr (Or.inl hi)) =
    appendEquiv (Sum.inl (l.getDualSelf i hi)) := by
  symm
  rw [HasSubSingeDualSelf.eq_dual_iff h]
  simp
  exact areDualSelf_of_getDualSelf l i hi

lemma HasSubSingeDualSelf.of_append_inl_of_hasDualSelf {l l2 : IndexList X} (i : Fin l.length)
    (h : (l ++ l2).HasSubSingeDualSelf (appendEquiv (Sum.inl i))) (hi : l.HasDualSelf i) :
    l.HasSubSingeDualSelf i := by
  intro hj j
  have h1 := h ((hasDualSelf_append_inl l l2 i).mpr (Or.inl hi)) (appendEquiv (Sum.inl j))
  intro hij
  simp at h1
  have h2 := h1 hij
  apply Sum.inl_injective
  apply appendEquiv.injective
  rw [h2, l.getDualSelf_append_inl _ h]


lemma HasSubSingeDualSelf.not_hasDualOther_of_append_inl_of_hasDualSelf
    {l l2 : IndexList X} (i : Fin l.length)
    (h : (l ++ l2).HasSubSingeDualSelf (appendEquiv (Sum.inl i))) (hi : l.HasDualSelf i) :
    ¬ l.HasDualOther l2 i := by
  simp [HasDualOther]
  intro j
  simp [AreDualOther]
  simp [HasSubSingeDualSelf] at h
  have h' := h ((hasDualSelf_append_inl l l2 i).mpr (Or.inl hi)) (appendEquiv (Sum.inr j))
  simp [AreDualSelf] at h'
  by_contra hn
  have h'' := h' hn
  rw [l.getDualSelf_append_inl _ h hi] at h''
  simp at h''


lemma HasSubSingeDualSelf.of_append_inr_of_hasDualSelf {l l2 : IndexList X} (i : Fin l2.length)
    (h : (l ++ l2).HasSubSingeDualSelf (appendEquiv (Sum.inr i))) (hi : l2.HasDualSelf i) :
    l2.HasSubSingeDualSelf i := by
  intro hj j
  have h1 := h ((hasDualSelf_append_inr l i).mpr (Or.inl hi)) (appendEquiv (Sum.inr j))
  intro hij
  simp at h1
  have h2 := h1 hij
  apply Sum.inr_injective
  apply appendEquiv.injective
  rw [h2]
  symm
  rw [eq_dual_iff h]
  simp only [AreDualSelf.append_inr_inr]
  exact areDualSelf_of_getDualSelf l2 i hj


lemma HasSubSingeDualSelf.append_inl (i : Fin l.length) :
    (l ++ l2).HasSubSingeDualSelf (appendEquiv (Sum.inl i)) ↔
     (l.HasSubSingeDualSelf i ∧ ¬ l.HasDualOther l2 i) ∨
     (¬ l.HasDualSelf i ∧ l.HasSubSingeDualOther l2 i) := by
  apply Iff.intro
  · intro h
    by_cases h1 : (l ++ l2).HasDualSelf (appendEquiv (Sum.inl i))
    rw [hasDualSelf_append_inl] at h1
    cases h1 <;> rename_i h1
    · exact  Or.inl ⟨of_append_inl_of_hasDualSelf i h h1,
        (not_hasDualOther_of_append_inl_of_hasDualSelf i h h1)⟩
    · sorry


def HasSubSingeDuals : Prop := ∀ i, l.HasSubSingeDual i

def HasNoDual (i : Fin l.length) : Prop := ¬ l.HasDual i

def HasNoDuals : Prop := ∀ i, l.HasNoDual i


lemma hasSubSingeDuals_of_hasNoDuals (h : l.HasNoDuals) : l.HasSubSingeDuals := by
  intro i h1 j h2
  exfalso
  apply h i
  simp only [HasDual]
  exact ⟨j, h2⟩

/-- The proposition on a element (or really index of element) of a index list
  `s` which is ture iff does not share an id with any other element.
  This tells us that it should not be contracted with any other element. -/
def NoContr (i : Fin l.length) : Prop :=
  ∀ j, i ≠ j → l.idMap i ≠ l.idMap j

instance (i : Fin l.length) : Decidable (l.NoContr i) :=
  Fintype.decidableForallFintype

/-- The finset of indices of an index list corresponding to elements which do not contract. -/
def noContrFinset : Finset (Fin l.length) :=
  Finset.univ.filter l.NoContr

/-- An eqiuvalence between the subtype of indices of a index list `l` which do not contract and
  `Fin l.noContrFinset.card`. -/
def noContrSubtypeEquiv : {i : Fin l.length // l.NoContr i} ≃ Fin l.noContrFinset.card :=
  (Equiv.subtypeEquivRight (fun x => by simp [noContrFinset])).trans
  (Finset.orderIsoOfFin l.noContrFinset rfl).toEquiv.symm

@[simp]
lemma idMap_noContrSubtypeEquiv_neq (i j : Fin l.noContrFinset.card) (h : i ≠ j) :
    l.idMap (l.noContrSubtypeEquiv.symm i).1 ≠ l.idMap (l.noContrSubtypeEquiv.symm j).1 := by
  have hi := ((l.noContrSubtypeEquiv).symm i).2
  simp [NoContr] at hi
  have hj := hi ((l.noContrSubtypeEquiv).symm j)
  apply hj
  rw [@SetCoe.ext_iff]
  erw [Equiv.apply_eq_iff_eq]
  exact h

/-- The subtype of indices `l` which do contract. -/
def contrSubtype : Type := {i : Fin l.length // ¬ l.NoContr i}

instance : Fintype l.contrSubtype :=
  Subtype.fintype fun x => ¬ l.NoContr x

instance : DecidableEq l.contrSubtype :=
  Subtype.instDecidableEq

/-!

## Getting the index which contracts with a given index

-/

lemma getDual_id (i : l.contrSubtype) : l.idMap i.1 = l.idMap (l.getDual i).1 := by
  simp [getDual]
  have h1 := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  simp only [AreDual, ne_eq, and_imp] at h1
  exact h1.1.2

lemma getDual_neq_self (i : l.contrSubtype) : i ≠ l.getDual i := by
  have h1 := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  exact ne_of_apply_ne Subtype.val h1.1.1

lemma getDual_getDualProp (i : l.contrSubtype) : l.AreDual i.1 (l.getDual i).1 := by
  simp [getDual]
  have h1 := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  simp only [AreDual, ne_eq, and_imp] at h1
  exact h1.1

/-!

## Index lists with no contracting indices

-/

/-- The proposition on a `IndexList` for it to have no contracting
  indices. -/
def HasNoContr : Prop := ∀ i, l.NoContr i

lemma contrSubtype_is_empty_of_hasNoContr (h : l.HasNoContr) : IsEmpty l.contrSubtype := by
  rw [_root_.isEmpty_iff]
  intro a
  exact h a.1 a.1 (fun _ => a.2 (h a.1)) rfl

lemma hasNoContr_id_inj (h : l.HasNoContr) : Function.Injective l.idMap := fun i j => by
  simpa using (h i j).mt

lemma hasNoContr_color_eq_of_id_eq (h : l.HasNoContr) (i j : Fin l.length) :
    l.idMap i = l.idMap j → l.colorMap i = l.colorMap j := by
  intro h1
  apply l.hasNoContr_id_inj h at h1
  rw [h1]

@[simp]
lemma hasNoContr_noContrFinset_card (h : l.HasNoContr) :
    l.noContrFinset.card = List.length l := by
  simp only [noContrFinset]
  rw [Finset.filter_true_of_mem]
  simp only [Finset.card_univ, Fintype.card_fin]
  intro x _
  exact h x

/-!

## The contracted index list

-/

/-- The index list of those indices of `l` which do not contract. -/
def contr : IndexList X :=
  IndexList.fromFinMap (fun i => l.get (l.noContrSubtypeEquiv.symm i))

@[simp]
lemma contr_numIndices : l.contr.numIndices = l.noContrFinset.card := by
  simp [contr]

@[simp]
lemma contr_idMap_apply (i : Fin l.contr.numIndices) :
    l.contr.idMap i =
    l.idMap (l.noContrSubtypeEquiv.symm (Fin.cast (by simp) i)).1 := by
  simp [contr, IndexList.fromFinMap, IndexList.idMap]
  rfl

lemma contr_hasNoContr : HasNoContr l.contr := by
  intro i
  simp [NoContr]
  intro j h
  refine l.idMap_noContrSubtypeEquiv_neq _ _ ?_
  rw [@Fin.ne_iff_vne]
  simp only [Fin.coe_cast, ne_eq]
  exact Fin.val_ne_of_ne h

/-- Contracting indices on a index list that has no contractions does nothing. -/
@[simp]
lemma contr_of_hasNoContr (h : HasNoContr l) : l.contr = l := by
  simp only [contr, List.get_eq_getElem]
  have hn : (@Finset.univ (Fin (List.length l)) (Fin.fintype (List.length l))).card =
      (Finset.filter l.NoContr Finset.univ).card := by
    rw [Finset.filter_true_of_mem (fun a _ => h a)]
  have hx : (Finset.filter l.NoContr Finset.univ).card = (List.length l) := by
    rw [← hn]
    exact Finset.card_fin (List.length l)
  apply List.ext_get
  simpa [fromFinMap, noContrFinset] using hx
  intro n h1 h2
  simp only [noContrFinset, noContrSubtypeEquiv, OrderIso.toEquiv_symm, Equiv.symm_trans_apply,
    RelIso.coe_fn_toEquiv, Equiv.subtypeEquivRight_symm_apply_coe, fromFinMap, List.get_eq_getElem,
    OrderIso.symm_symm, Finset.coe_orderIsoOfFin_apply, List.getElem_map, Fin.getElem_list,
    Fin.cast_mk]
  simp only [Finset.filter_true_of_mem (fun a _ => h a)]
  congr
  rw [(Finset.orderEmbOfFin_unique' _
    (fun x => Finset.mem_univ ((Fin.castOrderIso hx).toOrderEmbedding x))).symm]
  rfl

/-- Applying contrIndexlist is equivalent to applying it once. -/
@[simp]
lemma contr_contr : l.contr.contr = l.contr :=
  l.contr.contr_of_hasNoContr (l.contr_hasNoContr)

/-!

## Pairs of contracting indices

-/

/-- The set of contracting ordered pairs of indices. -/
def contrPairSet : Set (l.contrSubtype × l.contrSubtype) :=
  {p | p.1.1 < p.2.1 ∧ l.idMap p.1.1 = l.idMap p.2.1}

instance : DecidablePred fun x => x ∈ l.contrPairSet := fun _ =>
  And.decidable

instance : Fintype l.contrPairSet := setFintype _

lemma contrPairSet_isEmpty_of_hasNoContr (h : l.HasNoContr) :
    IsEmpty l.contrPairSet := by
  simp only [contrPairSet, Subtype.coe_lt_coe, Set.coe_setOf, isEmpty_subtype, not_and, Prod.forall]
  refine fun a b h' => h a.1 b.1 (Fin.ne_of_lt h')

lemma getDual_lt_self_mem_contrPairSet {i : l.contrSubtype}
    (h : (l.getDual i).1 < i.1) : (l.getDual i, i) ∈ l.contrPairSet :=
  And.intro h (l.getDual_id i).symm

lemma getDual_not_lt_self_mem_contrPairSet {i : l.contrSubtype}
    (h : ¬ (l.getDual i).1 < i.1) : (i, l.getDual i) ∈ l.contrPairSet := by
  apply And.intro
  have h1 := l.getDual_neq_self i
  simp only [Subtype.coe_lt_coe, gt_iff_lt]
  simp at h
  exact lt_of_le_of_ne h h1
  simp only
  exact l.getDual_id i

/-- The list of elements of `l` which contract together. -/
def contrPairList : List (Fin l.length × Fin l.length) :=
  (List.product (Fin.list l.length) (Fin.list l.length)).filterMap fun (i, j) => if
  l.AreDual i j then some (i, j) else none
end IndexNotation
