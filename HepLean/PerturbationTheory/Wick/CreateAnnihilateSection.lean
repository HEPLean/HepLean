/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Signs.StaticWickCoef
/-!

# Create and annihilate sections (of bundles)

-/

namespace Wick
open HepLean.List
open FieldStatistic

/-- The sections of `Σ i, f i` over a list `φs : List 𝓕`.
  In terms of physics, given some fields `φ₁...φₙ`, the different ways one can associate
  each field as a `creation` or an `annihilation` operator. E.g. the number of terms
  `φ₁⁰φ₂¹...φₙ⁰` `φ₁¹φ₂¹...φₙ⁰` etc. If some fields are exclusively creation or annihilation
  operators at this point (e.g. asymptotic states) this is accounted for. -/
def CreateAnnihilateSect {𝓕 : Type} (f : 𝓕 → Type) (φs : List 𝓕) : Type :=
  Π i, f (φs.get i)

namespace CreateAnnihilateSect

section basic_defs

variable {𝓕 : Type} {f : 𝓕 → Type} [∀ i, Fintype (f i)] {φs : List 𝓕}
  (a : CreateAnnihilateSect f φs)

/-- The type `CreateAnnihilateSect f φs` is finite. -/
instance fintype : Fintype (CreateAnnihilateSect f φs) := Pi.instFintype

/-- The section got by dropping the first element of `φs` if it exists. -/
def tail : {φs : List 𝓕} → (a : CreateAnnihilateSect f φs) → CreateAnnihilateSect f φs.tail
  | [], a => a
  | _ :: _, a => fun i => a (Fin.succ i)

/-- For a list of fields `i :: l` the value of the section at the head `i`. -/
def head {φ : 𝓕} (a : CreateAnnihilateSect f (φ :: φs)) : f φ := a ⟨0, Nat.zero_lt_succ φs.length⟩

end basic_defs

section toList_basic

variable {𝓕 : Type} {f : 𝓕 → Type} (q : 𝓕 → FieldStatistic)
  {φs : List 𝓕} (a : CreateAnnihilateSect f φs)

/-- The list `List (Σ i, f i)` defined by `a`. -/
def toList : {l : List 𝓕} → (a : CreateAnnihilateSect f l) → List (Σ i, f i)
  | [], _ => []
  | i :: _, a => ⟨i, a.head⟩ :: toList a.tail

@[simp]
lemma toList_length : (toList a).length = φs.length := by
  induction φs with
  | nil => rfl
  | cons i l ih =>
    simp only [toList, List.length_cons, Fin.zero_eta]
    rw [ih]

lemma toList_tail : {l : List 𝓕} → (a : CreateAnnihilateSect f l) → toList a.tail = (toList a).tail
  | [], _ => rfl
  | i :: l, a => by
    simp [toList]

lemma toList_cons {i : 𝓕} (a : CreateAnnihilateSect f (i :: φs)) :
    (toList a) = ⟨i, a.head⟩ :: toList a.tail := by
  rfl

lemma toList_get (a : CreateAnnihilateSect f φs) :
    (toList a).get = (fun i => ⟨φs.get i, a i⟩) ∘ Fin.cast (by simp) := by
  induction φs with
  | nil =>
    funext i
    exact Fin.elim0 i
  | cons i l ih =>
    simp only [toList_cons, List.get_eq_getElem, Fin.zero_eta, List.getElem_cons_succ,
      Function.comp_apply, Fin.cast_mk]
    funext x
    match x with
    | ⟨0, h⟩ => rfl
    | ⟨x + 1, h⟩ =>
      simp only [List.get_eq_getElem, Prod.mk.eta, List.getElem_cons_succ, Function.comp_apply]
      change (toList a.tail).get _ = _
      rw [ih]
      simp [tail]

@[simp]
lemma toList_grade :
    FieldStatistic.ofList (fun i => q i.fst) a.toList = fermionic ↔
    FieldStatistic.ofList q φs = fermionic := by
  induction φs with
  | nil =>
    simp [toList]
  | cons i r ih =>
    simp only [ofList, Fin.isValue, ite_eq_right_iff, zero_ne_one, imp_false]
    have ih' := ih (fun i => a i.succ)
    have h1 : ofList (fun i => q i.fst) a.tail.toList = ofList q r := by
      by_cases h : ofList q r = fermionic
      · simp_all
      · have h0 : ofList q r = bosonic := (neq_fermionic_iff_eq_bosonic (ofList q r)).mp h
        rw [h0] at ih'
        simp only [reduceCtorEq, iff_false, neq_fermionic_iff_eq_bosonic] at ih'
        have h0' : ofList (fun i => q i.fst) a.tail.toList = bosonic := ih'
        rw [h0, h0']
    rw [h1]

@[simp]
lemma toList_grade_take (q : 𝓕 → FieldStatistic) :
    (r : List 𝓕) → (a : CreateAnnihilateSect f r) → (n : ℕ) →
    ofList (fun i => q i.fst) (List.take n a.toList) = ofList q (List.take n r)
  | [], _, _ => by
    simp [toList]
  | i :: r, a, 0 => by
    simp
  | i :: r, a, Nat.succ n => by
    simp only [ofList, Fin.isValue]
    rw [toList_grade_take q r a.tail n]

end toList_basic

section toList_erase

variable {𝓕 : Type} {f : 𝓕 → Type} {l : List 𝓕}

/-- The equivalence between `CreateAnnihilateSect f l` and
  `f (l.get n) × CreateAnnihilateSect f (l.eraseIdx n)` obtained by extracting the `n`th field
  from `l`. -/
def extractEquiv (n : Fin l.length) : CreateAnnihilateSect f l ≃
    f (l.get n) × CreateAnnihilateSect f (l.eraseIdx n) := by
  match l with
  | [] => exact Fin.elim0 n
  | l0 :: l =>
    let e1 : CreateAnnihilateSect f ((l0 :: l).eraseIdx n) ≃
        Π i, f ((l0 :: l).get (n.succAbove i)) :=
      Equiv.piCongr (Fin.castOrderIso (by rw [eraseIdx_cons_length])).toEquiv
      fun x => Equiv.cast (congrArg f (by
      rw [HepLean.List.eraseIdx_get]
      simp only [List.length_cons, Function.comp_apply, List.get_eq_getElem, Fin.coe_cast,
        RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply]
      congr 1
      simp only [Fin.succAbove]
      split
      next h =>
        simp_all only [Fin.coe_castSucc]
        split
        next h_1 => simp_all only [Fin.coe_castSucc, Fin.coe_cast]
        next h_1 =>
          simp_all only [not_lt, Fin.val_succ, Fin.coe_cast, self_eq_add_right, one_ne_zero]
          simp only [Fin.le_def, List.length_cons, Fin.coe_castSucc, Fin.coe_cast] at h_1
          simp only [Fin.lt_def, Fin.coe_castSucc, Fin.coe_cast] at h
          omega
      next h =>
        simp_all only [not_lt, Fin.val_succ]
        split
        next h_1 =>
          simp_all only [Fin.coe_castSucc, Fin.coe_cast, add_right_eq_self, one_ne_zero]
          simp only [Fin.lt_def, Fin.coe_castSucc, Fin.coe_cast] at h_1
          simp only [Fin.le_def, Fin.coe_cast, Fin.coe_castSucc] at h
          omega
        next h_1 => simp_all only [not_lt, Fin.val_succ, Fin.coe_cast]))
    exact (Fin.insertNthEquiv _ _).symm.trans (Equiv.prodCongr (Equiv.refl _) e1.symm)

lemma extractEquiv_symm_toList_get_same (n : Fin l.length) (a0 : f (l.get n))
    (a : CreateAnnihilateSect f (l.eraseIdx n)) :
    ((extractEquiv n).symm (a0, a)).toList[n] = ⟨l[n], a0⟩ := by
  match l with
  | [] => exact Fin.elim0 n
  | l0 :: l =>
    trans (((CreateAnnihilateSect.extractEquiv n).symm (a0, a)).toList).get (Fin.cast (by simp) n)
    · simp only [List.length_cons, List.get_eq_getElem, Fin.coe_cast]
      rfl
    rw [CreateAnnihilateSect.toList_get]
    simp only [List.get_eq_getElem, List.length_cons, extractEquiv, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
      Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self, Sigma.mk.inj_iff, heq_eq_eq]
    apply And.intro
    · rfl
    erw [Fin.insertNthEquiv_apply]
    simp only [Fin.insertNth_apply_same]

/-- The section obtained by dropping the `n`th field. -/
def eraseIdx (a : CreateAnnihilateSect f l) (n : Fin l.length) :
    CreateAnnihilateSect f (l.eraseIdx n) :=
  (extractEquiv n a).2

@[simp]
lemma eraseIdx_zero_tail {i : 𝓕} (a : CreateAnnihilateSect f (i :: l)) :
    (eraseIdx a (@OfNat.ofNat (Fin (l.length + 1)) 0 Fin.instOfNat : Fin (l.length + 1))) =
    a.tail := by
  simp only [List.length_cons, Fin.val_zero, List.eraseIdx_cons_zero, eraseIdx, List.get_eq_getElem,
    List.getElem_cons_zero, extractEquiv, Fin.zero_succAbove, Fin.val_succ, List.getElem_cons_succ,
    Fin.insertNthEquiv_zero, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.cast_eq_self,
    Equiv.cast_refl, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_snd]
  rfl

lemma eraseIdx_succ_head {i : 𝓕} (n : ℕ) (hn : n + 1 < (i :: l).length)
    (a : CreateAnnihilateSect f (i :: l)) : (eraseIdx a ⟨n + 1, hn⟩).head = a.head := by
  rw [eraseIdx, extractEquiv]
  simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ, List.eraseIdx_cons_succ,
    RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_snd]
  conv_lhs =>
    enter [1, 2, 1]
    erw [Fin.insertNthEquiv_symm_apply]
  simp only [head, Equiv.piCongr, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Equiv.piCongrRight,
    Equiv.cast_symm, Equiv.piCongrLeft, OrderIso.toEquiv_symm, OrderIso.symm_symm,
    Equiv.piCongrLeft', List.length_cons, Fin.zero_eta, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Pi.map_apply, Fin.cast_zero, Fin.val_zero,
    List.getElem_cons_zero, Equiv.cast_apply]
  simp only [Fin.succAbove, Fin.castSucc_zero', Fin.removeNth]
  refine cast_eq_iff_heq.mpr ?_
  congr
  simp [Fin.ext_iff]

lemma eraseIdx_succ_tail {i : 𝓕} (n : ℕ) (hn : n + 1 < (i :: l).length)
    (a : CreateAnnihilateSect f (i :: l)) :
    (eraseIdx a ⟨n + 1, hn⟩).tail = eraseIdx a.tail ⟨n, Nat.succ_lt_succ_iff.mp hn⟩ := by
  match l with
  | [] =>
    simp at hn
  | r0 :: r =>
  rw [eraseIdx, extractEquiv]
  simp only [List.length_cons, List.eraseIdx_cons_succ, List.tail_cons, List.get_eq_getElem,
    List.getElem_cons_succ, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_snd, Nat.succ_eq_add_one]
  conv_lhs =>
    enter [1, 2, 1]
    erw [Fin.insertNthEquiv_symm_apply]
  rw [eraseIdx]
  conv_rhs =>
    rhs
    rw [extractEquiv]
    simp only [List.get_eq_getElem, List.length_cons, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_snd]
    erw [Fin.insertNthEquiv_symm_apply]
  simp only [tail, List.tail_cons, Equiv.piCongr, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
    Equiv.piCongrRight, Equiv.cast_symm, Equiv.piCongrLeft, OrderIso.toEquiv_symm,
    OrderIso.symm_symm, Equiv.piCongrLeft', Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Pi.map_apply, Fin.cast_succ_eq, Fin.val_succ,
    List.getElem_cons_succ, Equiv.cast_apply, List.get_eq_getElem, List.length_cons, Fin.succ_mk,
    Prod.map_apply, id_eq]
  funext i
  simp only [Pi.map_apply, Equiv.cast_apply]
  have hcast {α β : Type} (h : α = β) (a : α) (b : β) : cast h a = b ↔ a = cast (Eq.symm h) b := by
    cases h
    simp
  rw [hcast]
  simp only [cast_cast]
  refine eq_cast_iff_heq.mpr ?_
  simp only [Fin.succAbove, Fin.removeNth]
  congr
  simp only [List.length_cons, Fin.ext_iff, Fin.val_succ]
  split
  next h =>
    simp_all only [Fin.coe_castSucc, Fin.val_succ, Fin.coe_cast, add_left_inj]
    split
    next h_1 => simp_all only [Fin.coe_castSucc, Fin.coe_cast]
    next h_1 =>
      simp_all only [not_lt, Fin.val_succ, Fin.coe_cast, self_eq_add_right, one_ne_zero]
      simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ, Fin.coe_cast, add_lt_add_iff_right]
        at h
      simp only [Fin.le_def, Fin.coe_castSucc, Fin.coe_cast] at h_1
      omega
  next h =>
    simp_all only [not_lt, Fin.val_succ, Fin.coe_cast, add_left_inj]
    split
    next h_1 =>
      simp_all only [Fin.coe_castSucc, Fin.coe_cast, add_right_eq_self, one_ne_zero]
      simp only [Fin.le_def, Fin.coe_castSucc, Fin.val_succ, Fin.coe_cast, add_le_add_iff_right]
        at h
      simp only [Fin.lt_def, Fin.coe_castSucc, Fin.coe_cast] at h_1
      omega
    next h_1 => simp_all only [not_lt, Fin.val_succ, Fin.coe_cast]

lemma eraseIdx_toList : {l : List 𝓕} → {n : Fin l.length} → (a : CreateAnnihilateSect f l) →
    (eraseIdx a n).toList = a.toList.eraseIdx n
  | [], n, _ => Fin.elim0 n
  | r0 :: r, ⟨0, h⟩, a => by
    simp [toList_tail]
  | r0 :: r, ⟨n + 1, h⟩, a => by
    simp only [toList, List.length_cons, List.tail_cons, List.eraseIdx_cons_succ, List.cons.injEq,
      Sigma.mk.inj_iff, heq_eq_eq, true_and]
    apply And.intro
    · rw [eraseIdx_succ_head]
    · conv_rhs => rw [← eraseIdx_toList (l := r) (n := ⟨n, Nat.succ_lt_succ_iff.mp h⟩) a.tail]
      rw [eraseIdx_succ_tail]

lemma extractEquiv_symm_eraseIdx {I : Type} {f : I → Type}
    {l : List I} (n : Fin l.length) (a0 : f l[↑n]) (a : CreateAnnihilateSect f (l.eraseIdx n)) :
    ((extractEquiv n).symm (a0, a)).eraseIdx n = a := by
  match l with
  | [] => exact Fin.elim0 n
  | l0 :: l =>
    rw [eraseIdx, extractEquiv]
    simp

end toList_erase

section toList_sign_conditions

variable {𝓕 : Type} {f : 𝓕 → Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]
  {l : List 𝓕} (a : CreateAnnihilateSect f l)

lemma toList_koszulSignInsert (x : (i : 𝓕) × f i) :
    koszulSignInsert (fun i => q i.fst) (fun i j => le i.fst j.fst) x a.toList =
    koszulSignInsert q le x.1 l := by
  induction l with
  | nil => simp [koszulSignInsert]
  | cons b l ih =>
    simp only [koszulSignInsert, List.tail_cons, Fin.isValue]
    rw [ih]

lemma toList_koszulSign :
    koszulSign (fun i => q i.fst) (fun i j => le i.fst j.fst) a.toList =
    koszulSign q le l := by
  induction l with
  | nil => simp [koszulSign]
  | cons i l ih =>
    simp only [koszulSign, List.tail_cons]
    rw [ih]
    congr 1
    rw [toList_koszulSignInsert]

lemma insertionSortEquiv_toList :
    insertionSortEquiv (fun i j => le i.fst j.fst) a.toList =
    (Fin.castOrderIso (by simp)).toEquiv.trans ((insertionSortEquiv le l).trans
    (Fin.castOrderIso (by simp)).toEquiv) := by
  induction l with
  | nil =>
    simp [liftM, HepLean.List.insertionSortEquiv]
  | cons i l ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, List.insertionSort]
    conv_lhs => simp [HepLean.List.insertionSortEquiv]
    erw [orderedInsertEquiv_sigma]
    rw [ih]
    simp only [HepLean.Fin.equivCons_trans, Nat.succ_eq_add_one,
      HepLean.Fin.equivCons_castOrderIso, List.length_cons, Nat.add_zero, Nat.zero_eq,
      Fin.zero_eta]
    ext x
    conv_rhs => simp [HepLean.List.insertionSortEquiv]
    simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.cast_trans,
      Fin.coe_cast]
    have h2' (i : Σ i, f i) (l' : List (Σ i, f i)) :
      List.map (fun i => i.1) (List.orderedInsert (fun i j => le i.fst j.fst) i l') =
      List.orderedInsert le i.1 (List.map (fun i => i.1) l') := by
      induction l' with
      | nil =>
        simp [HepLean.List.orderedInsertEquiv]
      | cons j l' ih' =>
        by_cases hij : (fun i j => le i.fst j.fst) i j
        · rw [List.orderedInsert_of_le]
          · erw [List.orderedInsert_of_le]
            · simp
            · exact hij
          · exact hij
        · simp only [List.orderedInsert, hij, ↓reduceIte, List.unzip_snd, List.map_cons]
          simp only [↓reduceIte, List.cons.injEq, true_and]
          simpa using ih'
    have h2 (l' : List (Σ i, f i)) :
        List.map (fun i => i.1) (List.insertionSort (fun i j => le i.fst j.fst) l') =
        List.insertionSort le (List.map (fun i => i.1) l') := by
      induction l' with
      | nil =>
        simp [HepLean.List.orderedInsertEquiv]
      | cons i l' ih' =>
        simp only [List.insertionSort, List.unzip_snd]
        simp only [List.unzip_snd] at h2'
        rw [h2']
        congr
    rw [HepLean.List.orderedInsertEquiv_congr _ _ _ (h2 _)]
    simp only [List.length_cons, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.coe_cast]
    have h3 : (List.insertionSort le (List.map (fun i => i.1) a.tail.toList)) =
      List.insertionSort le l := by
      congr
      have h3' (l : List 𝓕) (a : CreateAnnihilateSect f l) :
        List.map (fun i => i.1) a.toList = l := by
        induction l with
        | nil => rfl
        | cons i l ih' =>
          simp only [toList, List.length_cons, Fin.zero_eta, Prod.mk.eta,
            List.unzip_snd, List.map_cons, List.cons.injEq, true_and]
          simpa using ih' _
      rw [h3']
      rfl
    rw [HepLean.List.orderedInsertEquiv_congr _ _ _ h3]
    simp only [List.length_cons, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, Fin.coe_cast]
    rfl

/-- Given a section for `l` the corresponding section
  for `List.insertionSort le1 l`. -/
def sort :
    CreateAnnihilateSect f (List.insertionSort le l) :=
  Equiv.piCongr (HepLean.List.insertionSortEquiv le l) (fun i => (Equiv.cast (by
      congr 1
      rw [← HepLean.List.insertionSortEquiv_get]
      simp))) a

lemma sort_toList :
    (a.sort le).toList = List.insertionSort (fun i j => le i.fst j.fst) a.toList := by
  let l1 := List.insertionSort (fun i j => le i.fst j.fst) a.toList
  let l2 := (a.sort le).toList
  symm
  change l1 = l2
  have hlen : l1.length = l2.length := by
    simp [l1, l2]
  have hget : l1.get = l2.get ∘ Fin.cast hlen := by
    rw [← HepLean.List.insertionSortEquiv_get]
    rw [toList_get, toList_get]
    funext i
    rw [insertionSortEquiv_toList]
    simp only [Function.comp_apply, Equiv.symm_trans_apply,
      OrderIso.toEquiv_symm, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, id_eq, eq_mpr_eq_cast, Fin.coe_cast, Sigma.mk.inj_iff]
    apply And.intro
    · have h1 := congrFun (HepLean.List.insertionSortEquiv_get (r := le) l) (Fin.cast (by simp) i)
      rw [← h1]
      simp
    · simp only [List.get_eq_getElem, sort, Equiv.piCongr, Equiv.trans_apply, Fin.coe_cast,
      Equiv.piCongrLeft_apply, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.cast_apply,
      heq_eqRec_iff_heq]
      exact (cast_heq _ _).symm
  apply List.ext_get hlen
  rw [hget]
  simp

end toList_sign_conditions
end CreateAnnihilateSect

end Wick
