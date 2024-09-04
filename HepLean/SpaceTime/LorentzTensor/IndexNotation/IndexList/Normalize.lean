/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.CountId
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Basic
/-!

# Normalizing an index list.

The normalization of an index list, is the corresponding index list
where all `id` are set to `0, 1, 2, ...` determined by
the order of indices without duals, followed by the order of indices with duals.

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-! TODO: Replace with Mathlib lemma. -/
lemma dedup_map_of_injective' {α : Type} [DecidableEq α] (f : α → ℕ)
    (l : List α) (hf : ∀ I ∈ l, ∀ J ∈ l, f I = f J ↔ I = J) :
    (l.map f).dedup = l.dedup.map f := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    simp only [List.map_cons]
    by_cases h : I ∈ l
    · rw [List.dedup_cons_of_mem h, List.dedup_cons_of_mem (List.mem_map_of_mem f h), ih]
      intro I' hI' J hJ
      have hI'2 : I' ∈ I :: l := List.mem_cons_of_mem I hI'
      have hJ2 : J ∈ I :: l := List.mem_cons_of_mem I hJ
      exact hf I' hI'2 J hJ2
    · rw [List.dedup_cons_of_not_mem h, List.dedup_cons_of_not_mem, ih, List.map_cons]
      · intro I' hI' J hJ
        have hI'2 : I' ∈ I :: l := List.mem_cons_of_mem I hI'
        have hJ2 : J ∈ I :: l := List.mem_cons_of_mem I hJ
        exact hf I' hI'2 J hJ2
      · simp_all only [List.mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp,
        true_and, List.mem_map, not_exists, not_and, List.forall_mem_ne', not_false_eq_true]

/-! TODO: Replace with Mathlib lemma. -/
lemma indexOf_map {α : Type} [DecidableEq α]
    (f : α → ℕ) (l : List α) (n : α) (hf : ∀ I ∈ l, ∀ J, f I = f J ↔ I = J) :
    l.indexOf n = (l.map f).indexOf (f n) := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    have ih' : (∀ I ∈ l, ∀ J, f I = f J ↔ I = J) := by
      intro I' hI' J'
      exact hf I' (List.mem_cons_of_mem I hI') J'
    simp only [List.map_cons]
    rw [← lawful_beq_subsingleton instBEqOfDecidableEq instBEqNat]
    by_cases h : I = n
    · rw [l.indexOf_cons_eq h, List.indexOf_cons_eq]
      exact congrArg f h
    · rw [l.indexOf_cons_ne h, List.indexOf_cons_ne]
      · rw [lawful_beq_subsingleton instBEqOfDecidableEq instBEqNat, ih ih']
      · exact (hf I (List.mem_cons_self I l) n).ne.mpr h

lemma indexOf_map_fin {α : Type} {m : ℕ} [DecidableEq α]
    (f : α → (Fin m)) (l : List α) (n : α) (hf : ∀ I ∈ l, ∀ J, f I = f J ↔ I = J) :
    l.indexOf n = (l.map f).indexOf (f n) := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    have ih' : (∀ I ∈ l, ∀ J, f I = f J ↔ I = J) := by
      intro I' hI' J'
      exact hf I' (List.mem_cons_of_mem I hI') J'
    simp only [List.map_cons]
    by_cases h : I = n
    · rw [l.indexOf_cons_eq h, List.indexOf_cons_eq]
      exact congrArg f h
    · rw [l.indexOf_cons_ne h, List.indexOf_cons_ne]
      · exact congrArg Nat.succ (ih ih')
      · exact (hf I (List.mem_cons_self I l) n).ne.mpr h

lemma indexOf_map' {α : Type} [DecidableEq α]
    (f : α → ℕ) (g : α → α) (l : List α) (n : α)
    (hf : ∀ I ∈ l, ∀ J, f I = f J ↔ g I = g J)
    (hg : ∀ I ∈ l, g I = I)
    (hs : ∀ I, f I = f (g I)) :
    l.indexOf (g n) = (l.map f).indexOf (f n) := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    have ih' : (∀ I ∈ l, ∀ J, f I = f J ↔ g I = g J) := by
      intro I' hI' J'
      exact hf I' (List.mem_cons_of_mem I hI') J'
    simp only [List.map_cons]
    rw [← lawful_beq_subsingleton instBEqOfDecidableEq instBEqNat]
    by_cases h : I = g n
    · rw [l.indexOf_cons_eq h, List.indexOf_cons_eq]
      rw [h, ← hs]
    · rw [l.indexOf_cons_ne h, List.indexOf_cons_ne]
      · rw [lawful_beq_subsingleton instBEqOfDecidableEq instBEqNat, ih ih']
        intro I hI
        apply hg
        exact List.mem_cons_of_mem _ hI
      · have hi'n := hf I (List.mem_cons_self I l) n
        refine (Iff.ne (id (Iff.symm hi'n))).mp ?_
        rw [hg]
        · exact h
        · exact List.mem_cons_self I l

lemma filter_dedup {α : Type} [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.filter p).dedup = (l.dedup.filter p) := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    by_cases h : p I
    · by_cases hd : I ∈ l
      · rw [List.filter_cons_of_pos (by simpa using h), List.dedup_cons_of_mem hd,
          List.dedup_cons_of_mem, ih]
        simp [hd, h]
      · rw [List.filter_cons_of_pos (by simpa using h), List.dedup_cons_of_not_mem hd,
          List.dedup_cons_of_not_mem, ih, List.filter_cons_of_pos]
        · exact decide_eq_true h
        · simp [hd]
    · by_cases hd : I ∈ l
      · rw [List.filter_cons_of_neg (by simpa using h), List.dedup_cons_of_mem hd, ih]
      · rw [List.filter_cons_of_neg (by simpa using h), List.dedup_cons_of_not_mem hd, ih]
        rw [List.filter_cons_of_neg]
        simpa using h

lemma findIdx?_map {α β : Type} (p : α → Bool)
    (f : β → α) (l : List β) :
    List.findIdx? p (List.map f l) = List.findIdx? (p ∘ f) l := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    simp only [List.map_cons, List.findIdx?_cons, zero_add, List.findIdx?_succ, Function.comp_apply]
    exact congrArg (ite (p (f I) = true) (some 0)) (congrArg (Option.map fun i => i + 1) ih)

lemma findIdx?_on_finRange {n : ℕ} (p : Fin n.succ → Prop) [DecidablePred p]
    (hp : ¬ p 0) :
    List.findIdx? p (List.finRange n.succ) =
    Option.map (fun i => i + 1) (List.findIdx? (p ∘ Fin.succ) (List.finRange n)) := by
  rw [List.finRange_succ_eq_map]
  simp only [Nat.succ_eq_add_one, hp, Nat.reduceAdd, List.finRange_zero, List.map_nil,
    List.concat_eq_append, List.nil_append, List.findIdx?_cons, decide_eq_true_eq, zero_add,
    List.findIdx?_succ, List.findIdx?_nil, Option.map_none', ite_eq_right_iff, imp_false]
  simp only [↓reduceIte]
  rw [findIdx?_map]

lemma findIdx?_on_finRange_eq_findIdx {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    List.findIdx? p (List.finRange n) = Option.map Fin.val (Fin.find p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : p 0
    · trans some 0
      · rw [List.finRange_succ_eq_map]
        simp only [Nat.succ_eq_add_one, List.findIdx?_cons, h, decide_True, ↓reduceIte]
      · symm
        simp only [Option.map_eq_some']
        use 0
        simp only [Fin.val_zero, and_true]
        rw [@Fin.find_eq_some_iff]
        simp [h]
    · rw [findIdx?_on_finRange _ h]
      erw [ih (p ∘ Fin.succ)]
      simp only [Option.map_map]
      have h1 : Option.map Fin.succ (Fin.find (p ∘ Fin.succ)) =
          Fin.find p := by
        by_cases hs : (Fin.find p).isSome
        · rw [@Option.isSome_iff_exists] at hs
          obtain ⟨i, hi⟩ := hs
          rw [hi]
          have hn : i ≠ 0 := by
            rw [@Fin.find_eq_some_iff] at hi
            by_contra hn
            simp_all
          simp only [Nat.succ_eq_add_one, Option.map_eq_some']
          use i.pred hn
          simp only [Fin.succ_pred, and_true]
          rw [@Fin.find_eq_some_iff] at hi ⊢
          simp_all only [Function.comp_apply, Fin.succ_pred, true_and]
          exact fun j hj => (Fin.pred_le_iff hn).mpr (hi.2 j.succ hj)
        · simp at hs
          rw [hs]
          simp only [Nat.succ_eq_add_one, Option.map_eq_none']
          rw [@Fin.find_eq_none_iff] at hs ⊢
          exact fun i => hs i.succ
      rw [← h1]
      exact Eq.symm (Option.map_map Fin.val Fin.succ (Fin.find (p ∘ Fin.succ)))

/-!

## idList

-/

/--
  The list of elements of `Fin l.length` `i` is in `idListFin` if
  `l.idMap i` appears for the first time in the `i`th spot.

  For example, for the list `['ᵘ¹', 'ᵘ²', 'ᵤ₁']` the `idListFin` is `[0, 1]`.
-/
def idListFin : List (Fin l.length) := ((List.finRange l.length).filter
  (fun i => (List.finRange l.length).findIdx? (fun j => l.idMap i = l.idMap j) = i))

omit [IndexNotation X] [Fintype X]

omit [DecidableEq X] in
lemma idListFin_getDualInOther? : l.idListFin =
    (List.finRange l.length).filter (fun i => l.getDualInOther? l i = i) := by
  rw [idListFin]
  apply List.filter_congr
  intro x _
  simp only [decide_eq_decide]
  rw [findIdx?_on_finRange_eq_findIdx]
  change Option.map Fin.val (l.getDualInOther? l x) = Option.map Fin.val (some x) ↔ _
  exact Function.Injective.eq_iff (Option.map_injective (@Fin.val_injective l.length))

/-- The list of ids keeping only the first appearance of each id. -/
def idList : List ℕ := List.map l.idMap l.idListFin

omit [DecidableEq X] in
lemma idList_getDualInOther? : l.idList =
    List.map l.idMap ((List.finRange l.length).filter (fun i => l.getDualInOther? l i = i)) := by
  rw [idList, idListFin_getDualInOther?]

lemma mem_idList_of_mem {I : Index X} (hI : I ∈ l.val) : I.id ∈ l.idList := by
  simp [idList_getDualInOther?]
  have hI : l.val.indexOf I < l.val.length := List.indexOf_lt_length.mpr hI
  have hI' : I = l.val.get ⟨l.val.indexOf I, hI⟩ := Eq.symm (List.indexOf_get hI)
  rw [hI']
  use (l.getDualInOther? l ⟨l.val.indexOf I, hI⟩).get (
    getDualInOther?_self_isSome l ⟨List.indexOf I l.val, hI⟩)
  apply And.intro
  · exact getDualInOther?_getDualInOther?_get_self l ⟨List.indexOf I l.val, hI⟩
  · simp only [getDualInOther?_id, List.get_eq_getElem, List.getElem_indexOf]
    exact Eq.symm ((fun {a b} => Nat.succ_inj'.mp) (congrArg Nat.succ (congrArg Index.id hI')))

lemma idMap_mem_idList (i : Fin l.length) : l.idMap i ∈ l.idList := by
  have h : l.val.get i ∈ l.val := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem l.val (↑i) i.isLt
  exact l.mem_idList_of_mem h

@[simp]
lemma idList_indexOf_mem {I J : Index X} (hI : I ∈ l.val) (hJ : J ∈ l.val) :
    l.idList.indexOf I.id = l.idList.indexOf J.id ↔ I.id = J.id := by
  rw [← lawful_beq_subsingleton instBEqOfDecidableEq instBEqNat]
  exact List.indexOf_inj (l.mem_idList_of_mem hI) (l.mem_idList_of_mem hJ)

omit [DecidableEq X] in
lemma idList_indexOf_get (i : Fin l.length) :
    l.idList.indexOf (l.idMap i) = l.idListFin.indexOf ((l.getDualInOther? l i).get
      (getDualInOther?_self_isSome l i)) := by
  rw [idList]
  simp [idListFin_getDualInOther?]
  rw [← indexOf_map' l.idMap (fun i => (l.getDualInOther? l i).get
      (getDualInOther?_self_isSome l i))]
  · intro i _ j
    refine Iff.intro (fun h => ?_) (fun h => ?_)
    · simp [getDualInOther?, AreDualInOther, h]
    · trans l.idMap ((l.getDualInOther? l i).get
        (getDualInOther?_self_isSome l i))
      · exact Eq.symm (getDualInOther?_id l l i (getDualInOther?_self_isSome l i))
      · trans l.idMap ((l.getDualInOther? l j).get
          (getDualInOther?_self_isSome l j))
        · exact congrArg l.idMap h
        · exact getDualInOther?_id l l j (getDualInOther?_self_isSome l j)
  · intro i hi
    simp at hi
    exact Option.get_of_mem (getDualInOther?_self_isSome l i) hi
  · exact fun i => Eq.symm (getDualInOther?_id l l i (getDualInOther?_self_isSome l i))

/-!

## GetDualCast

-/

/-- Two `IndexList`s are related by `GetDualCast` if they are the same length,
  and have the same dual structure.

  For example, `['ᵘ¹', 'ᵘ²', 'ᵤ₁']` and `['ᵤ₄', 'ᵘ⁵', 'ᵤ₄']` are related by `GetDualCast`,
  but `['ᵘ¹', 'ᵘ²', 'ᵤ₁']` and `['ᵘ¹', 'ᵘ²', 'ᵤ₃']` are not. -/
def GetDualCast : Prop := l.length = l2.length ∧ ∀ (h : l.length = l2.length),
  l.getDual? = Option.map (Fin.cast h.symm) ∘ l2.getDual? ∘ Fin.cast h

namespace GetDualCast

variable {l l2 l3 : IndexList X}

omit [DecidableEq X] in
lemma symm (h : GetDualCast l l2) : GetDualCast l2 l := by
  apply And.intro h.1.symm
  intro h'
  rw [h.2 h.1]
  funext i
  simp only [Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self, Option.map_map]
  have h1 (h : l.length = l2.length) : Fin.cast h ∘ Fin.cast h.symm = id := rfl
  rw [h1]
  simp

omit [DecidableEq X] in
lemma getDual?_isSome_iff (h : GetDualCast l l2) (i : Fin l.length) :
    (l.getDual? i).isSome ↔ (l2.getDual? (Fin.cast h.1 i)).isSome := by
  simp [h.2 h.1]

omit [DecidableEq X]
lemma getDual?_get (h : GetDualCast l l2) (i : Fin l.length) (h1 : (l.getDual? i).isSome) :
    (l.getDual? i).get h1 = Fin.cast h.1.symm ((l2.getDual? (Fin.cast h.1 i)).get
    ((getDual?_isSome_iff h i).mp h1)) := by
  apply Option.some_inj.mp
  simp only [Option.some_get]
  rw [← Option.map_some']
  simp only [Option.some_get]
  simp only [h.2 h.1, Function.comp_apply, Option.map_eq_some']

lemma areDualInSelf_of (h : GetDualCast l l2) (i j : Fin l.length) (hA : l.AreDualInSelf i j) :
    l2.AreDualInSelf (Fin.cast h.1 i) (Fin.cast h.1 j) := by
  have hn : (l.getDual? j).isSome := by
    rw [getDual?_isSome_iff_exists]
    exact ⟨i, hA.symm⟩
  have hni : (l.getDual? i).isSome := by
    rw [getDual?_isSome_iff_exists]
    exact ⟨j, hA⟩
  rcases l.getDual?_of_areDualInSelf hA with h1 | h1 | h1
  · have h1' : (l.getDual? j).get hn = i := Option.get_of_mem hn h1
    rw [h.getDual?_get] at h1'
    rw [← h1']
    simp
  · have h1' : (l.getDual? i).get hni = j := Option.get_of_mem hni h1
    rw [h.getDual?_get] at h1'
    rw [← h1']
    simp
  · have h1' : (l.getDual? j).get hn = (l.getDual? i).get hni := by
      apply Option.some_inj.mp
      simp [h1]
    rw [h.getDual?_get, h.getDual?_get] at h1'
    have h1 : ((l2.getDual? (Fin.cast h.1 j)).get ((getDual?_isSome_iff h j).mp hn))
        = ((l2.getDual? (Fin.cast h.1 i)).get ((getDual?_isSome_iff h i).mp hni)) := by
      simpa [Fin.ext_iff] using h1'
    simp [AreDualInSelf]
    apply And.intro
    · simp [AreDualInSelf] at hA
      simpa [Fin.ext_iff] using hA.1
    trans l2.idMap ((l2.getDual? (Fin.cast h.1 j)).get ((getDual?_isSome_iff h j).mp hn))
    · trans l2.idMap ((l2.getDual? (Fin.cast h.1 i)).get ((getDual?_isSome_iff h i).mp hni))
      · exact Eq.symm (getDual?_get_id l2 (Fin.cast h.left i) ((getDual?_isSome_iff h i).mp hni))
      · exact congrArg l2.idMap (id (Eq.symm h1))
    · exact getDual?_get_id l2 (Fin.cast h.left j) ((getDual?_isSome_iff h j).mp hn)

lemma areDualInSelf_iff (h : GetDualCast l l2) (i j : Fin l.length) : l.AreDualInSelf i j ↔
    l2.AreDualInSelf (Fin.cast h.1 i) (Fin.cast h.1 j) := by
  apply Iff.intro
  · exact areDualInSelf_of h i j
  · intro h'
    rw [← show Fin.cast h.1.symm (Fin.cast h.1 i) = i by rfl]
    rw [← show Fin.cast h.1.symm (Fin.cast h.1 j) = j by rfl]
    exact areDualInSelf_of h.symm _ _ h'

lemma idMap_eq_of (h : GetDualCast l l2) (i j : Fin l.length) (hm : l.idMap i = l.idMap j) :
    l2.idMap (Fin.cast h.1 i) = l2.idMap (Fin.cast h.1 j) := by
  by_cases h1 : i = j
  · exact congrArg l2.idMap (congrArg (Fin.cast h.left) h1)
  have h1' : l.AreDualInSelf i j := by
    simp [AreDualInSelf]
    exact ⟨h1, hm⟩
  rw [h.areDualInSelf_iff] at h1'
  simpa using h1'.2

lemma idMap_eq_iff (h : GetDualCast l l2) (i j : Fin l.length) :
    l.idMap i = l.idMap j ↔ l2.idMap (Fin.cast h.1 i) = l2.idMap (Fin.cast h.1 j) := by
  apply Iff.intro
  · exact idMap_eq_of h i j
  · intro h'
    rw [← show Fin.cast h.1.symm (Fin.cast h.1 i) = i by rfl]
    rw [← show Fin.cast h.1.symm (Fin.cast h.1 j) = j by rfl]
    exact idMap_eq_of h.symm _ _ h'

lemma iff_idMap_eq : GetDualCast l l2 ↔
    l.length = l2.length ∧ ∀ (h : l.length = l2.length) i j,
    l.idMap i = l.idMap j ↔ l2.idMap (Fin.cast h i) = l2.idMap (Fin.cast h j) := by
  refine Iff.intro (fun h => And.intro h.1 (fun _ i j => idMap_eq_iff h i j))
    (fun h => And.intro h.1 (fun h' => ?_))
  funext i
  simp only [Function.comp_apply]
  by_cases h1 : (l.getDual? i).isSome
  · have h1' : (l2.getDual? (Fin.cast h.1 i)).isSome := by
      simp [getDual?, Fin.isSome_find_iff] at h1 ⊢
      obtain ⟨j, hj⟩ := h1
      use (Fin.cast h.1 j)
      simp [AreDualInSelf] at hj ⊢
      rw [← h.2]
      simpa [Fin.ext_iff] using hj
    have h2 := Option.eq_some_of_isSome h1'
    rw [Option.eq_some_of_isSome h1', Option.map_some']
    nth_rewrite 1 [getDual?] at h2 ⊢
    rw [Fin.find_eq_some_iff] at h2 ⊢
    apply And.intro
    · apply And.intro
      · simp [AreDualInSelf] at h2
        simpa [Fin.ext_iff] using h2.1
      · rw [h.2 h.1]
        simp
    · intro j hj
      apply h2.2 (Fin.cast h.1 j)
      simp [AreDualInSelf] at hj ⊢
      apply And.intro
      · simpa [Fin.ext_iff] using hj.1
      · rw [← h.2]
        simpa using hj.2
  · simp at h1
    rw [h1]
    symm
    refine Option.map_eq_none'.mpr ?_
    rw [getDual?, Fin.find_eq_none_iff] at h1 ⊢
    simp [AreDualInSelf]
    intro j hij
    have h1j := h1 (Fin.cast h.1.symm j)
    simp [AreDualInSelf] at h1j
    rw [h.2 h.1] at h1j
    apply h1j
    exact ne_of_apply_ne (Fin.cast h') hij

lemma refl (l : IndexList X) : GetDualCast l l := by
  rw [iff_idMap_eq]
  simp

@[trans]
lemma trans (h : GetDualCast l l2) (h' : GetDualCast l2 l3) : GetDualCast l l3 := by
  rw [iff_idMap_eq] at h h' ⊢
  refine And.intro (h.1.trans h'.1) (fun hn i j => ?_)
  rw [h.2 h.1, h'.2 h'.1]
  rfl

lemma getDualInOther?_get (h : GetDualCast l l2) (i : Fin l.length) :
    (l.getDualInOther? l i).get (getDualInOther?_self_isSome l i) = (Fin.cast h.1.symm)
    ((l2.getDualInOther? l2 (Fin.cast h.1 i)).get
      (getDualInOther?_self_isSome l2 (Fin.cast h.left i))) := by
  apply Option.some_inj.mp
  simp only [Option.some_get]
  erw [Fin.find_eq_some_iff]
  have h1 := Option.eq_some_of_isSome (getDualInOther?_self_isSome l2 (Fin.cast h.left i))
  erw [Fin.find_eq_some_iff] at h1
  apply And.intro
  · simp [AreDualInOther]
    rw [idMap_eq_iff h]
    simp
  · intro j hj
    apply h1.2 (Fin.cast h.1 j)
    simp [AreDualInOther]
    exact (idMap_eq_iff h i j).mp hj

lemma countId_cast (h : GetDualCast l l2) (i : Fin l.length) :
    l.countId (l.val.get i) = l2.countId (l2.val.get (Fin.cast h.1 i)) := by
  rw [countId_get, countId_get]
  simp only [add_left_inj]
  have h1 : List.finRange l2.length = List.map (Fin.cast h.1) (List.finRange l.length) := by
    rw [List.ext_get_iff]
    simp [h.1]
  rw [h1]
  rw [List.countP_map]
  apply List.countP_congr
  intro j _
  simp only [decide_eq_true_eq, Function.comp_apply]
  exact areDualInSelf_iff h i j

lemma idListFin_cast (h : GetDualCast l l2) :
    List.map (Fin.cast h.1) l.idListFin = l2.idListFin := by
  rw [idListFin_getDualInOther?]
  have h1 : List.finRange l.length = List.map (Fin.cast h.1.symm) (List.finRange l2.length) := by
    rw [List.ext_get_iff]
    simp [h.1]
  rw [h1]
  rw [List.filter_map]
  have h1 : Fin.cast h.1 ∘ Fin.cast h.1.symm = id := rfl
  simp [h1]
  rw [idListFin_getDualInOther?]
  apply List.filter_congr
  intro i _
  simp [getDualInOther?, Fin.find_eq_some_iff, AreDualInOther]
  refine Iff.intro (fun h' j hj => ?_) (fun h' j hj => ?_)
  · simpa using h' (Fin.cast h.1.symm j) (by rw [h.idMap_eq_iff]; exact hj)
  · simpa using h' (Fin.cast h.1 j) (by rw [h.symm.idMap_eq_iff]; exact hj)

lemma idList_indexOf (h : GetDualCast l l2) (i : Fin l.length) :
    l2.idList.indexOf (l2.idMap (Fin.cast h.1 i)) = l.idList.indexOf (l.idMap i) := by
  rw [idList_indexOf_get, idList_indexOf_get, ← idListFin_cast h, getDualInOther?_get h.symm]
  simp only [Fin.cast_trans, Fin.cast_eq_self]
  rw [indexOf_map_fin (Fin.cast h.1)]
  exact fun _ _ _ => eq_iff_eq_of_cmp_eq_cmp rfl

end GetDualCast

/-!

## Normalized index list

-/

/--
  Given an index list `l`, the corresponding index list where id's are set to
  sequentially lowest values.

  E.g. on `['ᵘ¹', 'ᵘ³', 'ᵤ₁']` this gives `['ᵘ⁰', 'ᵘ¹', 'ᵤ₀']`.

-/
def normalize : IndexList X where
  val := List.ofFn (fun i => ⟨l.colorMap i, l.idList.indexOf (l.idMap i)⟩)

omit [DecidableEq X] in
lemma normalize_eq_map :
    l.normalize.val = List.map (fun I => ⟨I.toColor, l.idList.indexOf I.id⟩) l.val := by
  have hl : l.val = List.map l.val.get (List.finRange l.length) := by
    simp [length]
  rw [hl]
  simp [normalize]
  exact List.ofFn_eq_map

omit [DecidableEq X] in
@[simp]
lemma normalize_length : l.normalize.length = l.length := by
  simp [normalize, idList, length]

omit [DecidableEq X] in
@[simp]
lemma normalize_val_length : l.normalize.val.length = l.val.length := by
  simp [normalize, idList, length]

omit [DecidableEq X] in
@[simp]
lemma normalize_colorMap : l.normalize.colorMap = l.colorMap ∘ Fin.cast l.normalize_length := by
  funext x
  simp [colorMap, normalize, Index.toColor]

omit [DecidableEq X] in
lemma colorMap_normalize :
    l.colorMap = l.normalize.colorMap ∘ Fin.cast l.normalize_length.symm := by
  funext x
  simp [colorMap, normalize, Index.toColor]

@[simp]
lemma normalize_countId (i : Fin l.normalize.length) :
    l.normalize.countId l.normalize.val[Fin.val i] =
    l.countId (l.val.get ⟨i, by simpa using i.2⟩) := by
  rw [countId, countId]
  simp [l.normalize_eq_map, Index.id]
  apply List.countP_congr
  intro J hJ
  simp only [Function.comp_apply, decide_eq_true_eq]
  trans List.indexOf (l.val.get ⟨i, by simpa using i.2⟩).id l.idList = List.indexOf J.id l.idList
  · rfl
  · simp
    rw [idList_indexOf_mem]
    · rfl
    · exact List.getElem_mem l.val _ _
    · exact hJ

@[simp]
lemma normalize_countId' (i : Fin l.length) (hi : i.1 < l.normalize.length) :
    l.normalize.countId (l.normalize.val[Fin.val i]) = l.countId (l.val.get i) := by
  rw [countId, countId]
  simp [l.normalize_eq_map, Index.id]
  apply List.countP_congr
  intro J hJ
  simp only [Function.comp_apply, decide_eq_true_eq]
  trans List.indexOf (l.val.get i).id l.idList = List.indexOf J.id l.idList
  · rfl
  · simp
    rw [idList_indexOf_mem]
    · rfl
    · exact List.getElem_mem l.val _ _
    · exact hJ

@[simp]
lemma normalize_countId_mem (I : Index X) (h : I ∈ l.val) :
    l.normalize.countId (I.toColor, List.indexOf I.id l.idList) = l.countId I := by
  have h1 : l.val.indexOf I < l.val.length := List.indexOf_lt_length.mpr h
  have h2 : I = l.val.get ⟨l.val.indexOf I, h1⟩ := Eq.symm (List.indexOf_get h1)
  have h3 : (I.toColor, List.indexOf I.id l.idList) = l.normalize.val.get
      ⟨l.val.indexOf I, by simpa using h1⟩ := by
    simp only [List.get_eq_getElem, l.normalize_eq_map, List.getElem_map, List.getElem_indexOf]
  rw [h3]
  simp only [List.get_eq_getElem]
  trans l.countId (l.val.get ⟨l.val.indexOf I, h1⟩)
  · rw [← normalize_countId']
  · exact congrArg l.countId (id (Eq.symm h2))

lemma normalize_filter_countId_eq_one :
    List.map Index.id (l.normalize.val.filter (fun I => l.normalize.countId I = 1))
    = List.map l.idList.indexOf (List.map Index.id (l.val.filter (fun I => l.countId I = 1))) := by
  nth_rewrite 1 [l.normalize_eq_map]
  rw [List.filter_map]
  simp only [List.map_map]
  congr 1
  apply List.filter_congr
  intro I hI
  simp only [Function.comp_apply, decide_eq_decide]
  rw [normalize_countId_mem]
  exact hI

omit [DecidableEq X] in
@[simp]
lemma normalize_idMap_apply (i : Fin l.normalize.length) :
    l.normalize.idMap i = l.idList.indexOf (l.val.get ⟨i, by simpa using i.2⟩).id := by
  simp [idMap, normalize, Index.id]

@[simp]
lemma normalize_getDualCast_self : GetDualCast l.normalize l := by
  rw [GetDualCast.iff_idMap_eq]
  apply And.intro l.normalize_length
  intro h i j
  simp only [normalize_idMap_apply, List.get_eq_getElem]
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  · refine (List.indexOf_inj (idMap_mem_idList l (Fin.cast h i))
      (idMap_mem_idList l (Fin.cast h j))).mp ?_
    rw [lawful_beq_subsingleton instBEqOfDecidableEq instBEqNat]
    exact h'
  · exact congrFun (congrArg List.indexOf h') l.idList

@[simp]
lemma self_getDualCast_normalize : GetDualCast l l.normalize := by
  exact GetDualCast.symm l.normalize_getDualCast_self

lemma normalize_filter_countId_not_eq_one :
    List.map Index.id (l.normalize.val.filter (fun I => ¬ l.normalize.countId I = 1))
    = List.map l.idList.indexOf
    (List.map Index.id (l.val.filter (fun I => ¬ l.countId I = 1))) := by
  nth_rewrite 1 [l.normalize_eq_map]
  rw [List.filter_map]
  simp only [decide_not, List.map_map]
  congr 1
  apply List.filter_congr
  intro I hI
  simp only [Function.comp_apply, decide_eq_decide]
  rw [normalize_countId_mem]
  exact hI

namespace GetDualCast

variable {l l2 l3 : IndexList X}

lemma to_normalize (h : GetDualCast l l2) : GetDualCast l.normalize l2.normalize := by
  apply l.normalize_getDualCast_self.trans
  apply h.trans
  exact l2.self_getDualCast_normalize

lemma normalize_idMap_eq (h : GetDualCast l l2) :
    l.normalize.idMap = l2.normalize.idMap ∘ Fin.cast h.to_normalize.1 := by
  funext i
  simp only [normalize_idMap_apply, List.get_eq_getElem, Function.comp_apply, Fin.coe_cast]
  change List.indexOf (l.idMap (Fin.cast l.normalize_length i)) l.idList = _
  rw [← idList_indexOf h]
  rfl

lemma iff_normalize : GetDualCast l l2 ↔
    l.normalize.length = l2.normalize.length ∧ ∀ (h : l.normalize.length = l2.normalize.length),
    l.normalize.idMap = l2.normalize.idMap ∘ Fin.cast h := by
  refine Iff.intro (fun h => And.intro h.to_normalize.1 (fun _ => normalize_idMap_eq h))
    (fun h => l.self_getDualCast_normalize.trans
      (trans (iff_idMap_eq.mpr (And.intro h.1 (fun h' i j => ?_))) l2.normalize_getDualCast_self))
  rw [h.2 h.1]
  rfl

end GetDualCast

@[simp]
lemma normalize_normalize : l.normalize.normalize = l.normalize := by
  refine ext_colorMap_idMap (normalize_length l.normalize) ?hi (normalize_colorMap l.normalize)
  exact (l.normalize_getDualCast_self).normalize_idMap_eq

/-!

## Equality of normalized forms

-/

omit [DecidableEq X] in
lemma normalize_length_eq_of_eq_length (h : l.length = l2.length) :
    l.normalize.length = l2.normalize.length := by
  rw [normalize_length, normalize_length, h]

omit [DecidableEq X] in
lemma normalize_colorMap_eq_of_eq_colorMap (h : l.length = l2.length)
    (hc : l.colorMap = l2.colorMap ∘ Fin.cast h) :
    l.normalize.colorMap = l2.normalize.colorMap ∘
    Fin.cast (normalize_length_eq_of_eq_length l l2 h) := by
  simp [hc]
  rfl

/-!

## Reindexing

-/

/--
  Two `ColorIndexList` are said to be reindexes of one another if they:
    1. have the same length.
    2. every corresponding index has the same color, and duals which correspond.

  Note: This does not allow for reordering of indices.
-/
def Reindexing : Prop := l.length = l2.length ∧
  ∀ (h : l.length = l2.length), l.colorMap = l2.colorMap ∘ Fin.cast h ∧
    l.getDual? = Option.map (Fin.cast h.symm) ∘ l2.getDual? ∘ Fin.cast h

namespace Reindexing

variable {l l2 l3 : IndexList X}

omit [DecidableEq X] in
lemma iff_getDualCast : Reindexing l l2 ↔ GetDualCast l l2
    ∧ ∀ (h : l.length = l2.length), l.colorMap = l2.colorMap ∘ Fin.cast h := by
  refine Iff.intro (fun h => ⟨⟨h.1, fun h' => (h.2 h').2⟩, fun h' => (h.2 h').1⟩) (fun h => ?_)
  refine And.intro h.1.1 (fun h' => And.intro (h.2 h') (h.1.2 h'))

lemma iff_normalize : Reindexing l l2 ↔ l.normalize = l2.normalize := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [iff_getDualCast, GetDualCast.iff_normalize] at h
    refine ext_colorMap_idMap h.1.1 (h.1.2 (h.1.1)) ?refine_1.hc
    · refine normalize_colorMap_eq_of_eq_colorMap _ _ ?_ ?_
      · simpa using h.1.1
      · apply h.2
  · rw [iff_getDualCast, GetDualCast.iff_normalize, h]
    simp only [normalize_length, Fin.cast_refl, Function.comp_id, imp_self, and_self, true_and]
    rw [colorMap_normalize, colorMap_cast h]
    intro h'
    funext i
    simp

lemma refl (l : IndexList X) : Reindexing l l :=
  iff_normalize.mpr rfl

@[symm]
lemma symm (h : Reindexing l l2) : Reindexing l2 l := by
  rw [iff_normalize] at h ⊢
  exact h.symm

@[trans]
lemma trans (h : Reindexing l l2) (h' : Reindexing l2 l3) : Reindexing l l3 := by
  rw [iff_normalize] at h h' ⊢
  exact h.trans h'

end Reindexing

@[simp]
lemma normalize_reindexing_self : Reindexing l.normalize l := by
  rw [Reindexing.iff_normalize]
  exact l.normalize_normalize

@[simp]
lemma self_reindexing_normalize : Reindexing l l.normalize := by
  refine Reindexing.symm (normalize_reindexing_self l)

end IndexList

end IndexNotation
