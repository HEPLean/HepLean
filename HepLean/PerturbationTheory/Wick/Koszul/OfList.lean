/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Koszul.Grade
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick
open HepLean.List

noncomputable section

def ofList {I : Type} (l : List I) (x : ℂ) : FreeAlgebra ℂ I :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)

lemma ofList_pair {I : Type} (l r : List I) (x y : ℂ) :
    ofList (l ++ r) (x * y) = ofList l x * ofList r y := by
  simp only [ofList, ← map_mul, MonoidAlgebra.single_mul_single, EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma ofList_triple {I : Type} (la lb lc : List I) (xa xb xc : ℂ) :
    ofList (la ++ lb ++ lc) (xa * xb * xc) = ofList la xa * ofList lb xb * ofList lc xc := by
  rw [ofList_pair, ofList_pair]

lemma ofList_triple_assoc {I : Type} (la lb lc : List I) (xa xb xc : ℂ) :
    ofList (la ++ (lb ++ lc)) (xa * (xb * xc)) = ofList la xa * ofList lb xb * ofList lc xc := by
  rw [ofList_pair, ofList_pair]
  exact Eq.symm (mul_assoc (ofList la xa) (ofList lb xb) (ofList lc xc))

lemma ofList_cons_eq_ofList {I : Type} (l : List I) (i : I) (x : ℂ) :
    ofList (i :: l) x = ofList [i] 1 * ofList l x := by
  simp only [ofList, ← map_mul, MonoidAlgebra.single_mul_single, one_mul,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma ofList_singleton {I : Type} (i : I) :
    ofList [i] 1 = FreeAlgebra.ι ℂ i := by
  simp only [ofList, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    MonoidAlgebra.single, AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
  rfl

lemma ofList_eq_smul_one {I : Type} (l : List I) (x : ℂ) :
    ofList l x = x • ofList l 1 := by
  simp only [ofList]
  rw [← map_smul]
  simp

lemma ofList_empty {I : Type} : ofList [] 1 = (1 : FreeAlgebra ℂ I) := by
  simp only [ofList, EmbeddingLike.map_eq_one_iff]
  rfl

lemma ofList_empty' {I : Type} : ofList [] x = x • (1 : FreeAlgebra ℂ I) := by
  rw [ofList_eq_smul_one, ofList_empty]


lemma koszulOrder_ofList {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (l : List I) (x : ℂ) :
    koszulOrder r q (ofList l x) = (koszulSign r q l) • ofList (List.insertionSort r l) x := by
  rw [ofList]
  rw [koszulOrder_single]
  change ofList (List.insertionSort r l) _ = _
  rw [ofList_eq_smul_one]
  conv_rhs => rw [ofList_eq_smul_one]
  rw [smul_smul]

lemma ofList_insertionSort_eq_koszulOrder {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (l : List I) (x : ℂ) :
    ofList (List.insertionSort r l) x = (koszulSign r q l) • koszulOrder r q (ofList l x) := by
  rw [koszulOrder_ofList]
  rw [smul_smul]
  rw [koszulSign_mul_self]
  simp

def freeAlgebraMap {I : Type} (f : I → Type) [∀ i, Fintype (f i)] :
    FreeAlgebra ℂ I →ₐ[ℂ] FreeAlgebra ℂ (Σ i, f i) :=
  FreeAlgebra.lift ℂ fun i => ∑ (j : f i), FreeAlgebra.ι ℂ ⟨i, j⟩

lemma freeAlgebraMap_ι {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I)  :
    freeAlgebraMap f (FreeAlgebra.ι ℂ i) = ∑ (b : f i), FreeAlgebra.ι ℂ ⟨i, b⟩ := by
  simp [freeAlgebraMap]

def ofListM {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (l : List I) (x : ℂ) :
    FreeAlgebra ℂ (Σ i, f i) :=
  freeAlgebraMap f (ofList l x)

lemma ofListM_empty  {I : Type} (f : I → Type) [∀ i, Fintype (f i)] :
  ofListM f [] 1 = 1 := by
  simp only [ofListM, EmbeddingLike.map_eq_one_iff]
  rw [ofList_empty]
  exact map_one (freeAlgebraMap f)

lemma ofListM_empty_smul  {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (x : ℂ) :
  ofListM f [] x = x • 1 := by
  simp only [ofListM, EmbeddingLike.map_eq_one_iff]
  rw [ofList_eq_smul_one]
  rw [ofList_empty]
  simp

lemma ofListM_cons {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (r : List I)  (x : ℂ) :
    ofListM f (i :: r) x = (∑ j : f i, FreeAlgebra.ι ℂ ⟨i, j⟩) * (ofListM f r x) := by
  rw [ofListM, ofList_cons_eq_ofList, ofList_singleton, map_mul]
  conv_lhs => lhs; rw [freeAlgebraMap]
  rw [ofListM]
  simp

lemma ofListM_singleton {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (x : ℂ) :
    ofListM f [i] x = ∑ j : f i, x • FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListM]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [freeAlgebraMap_ι]
  rw [Finset.smul_sum]

lemma ofListM_singleton_one {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I)  :
    ofListM f [i] 1 = ∑ j : f i,  FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListM]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [freeAlgebraMap_ι]
  rw [Finset.smul_sum]
  simp

lemma ofListM_cons_eq_ofListM {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (r : List I)  (x : ℂ) :
    ofListM f (i :: r) x = ofListM f [i] 1 * ofListM f r x  := by
  rw [ofListM_cons, ofListM_singleton]
  simp only [one_smul]

def CreatAnnilateSect {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (l : List I)  : Type :=
  Π i, f (l.get i)

namespace CreatAnnilateSect

variable {I : Type} {f : I → Type} [∀ i, Fintype (f i)] {l : List I} (a : CreatAnnilateSect f l)

instance fintype : Fintype (CreatAnnilateSect f l) := Pi.fintype

def tail :  {l : List I} → (a : CreatAnnilateSect f l) → CreatAnnilateSect f l.tail
  | [], a => a
  | _ :: _, a =>  fun i => a (Fin.succ i)

def head {i : I} (a : CreatAnnilateSect f (i :: l)) : f i := a ⟨0, Nat.zero_lt_succ l.length⟩

def toList : {l : List I} → (a : CreatAnnilateSect f l) →  List (Σ i, f i)
  | [], _ => []
  | i :: _, a => ⟨i, a.head⟩ :: toList a.tail

@[simp]
lemma toList_length : (toList a).length = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [toList, List.length_cons, Fin.zero_eta]
    rw [ih]

lemma toList_tail :  {l : List I} → (a : CreatAnnilateSect f l) → toList a.tail = (toList a).tail
  | [], _ => rfl
  | i :: l, a => by
    simp [toList]

lemma toList_cons  {i : I} (a : CreatAnnilateSect f (i :: l)) :
    (toList a) = ⟨i, a.head⟩ :: toList a.tail := by
  rfl

lemma toList_get (a : CreatAnnilateSect f l) :
    (toList a).get = (fun i => ⟨l.get i, a i⟩) ∘ Fin.cast (by simp) := by
  induction l with
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
lemma toList_grade (q : I → Fin 2)   :
    grade (fun i => q i.fst) a.toList = 1 ↔ grade q l = 1 := by
  induction l with
  | nil =>
    simp [toList]
  | cons i r ih =>
    simp only [grade, Fin.isValue, ite_eq_right_iff, zero_ne_one, imp_false]
    have ih' := ih (fun i => a i.succ)
    have h1 : grade (fun i => q i.fst) a.tail.toList = grade q r  := by
      by_cases h : grade q r = 1
      · simp_all
      · have h0 : grade q r = 0 := by
          omega
        rw [h0] at ih'
        simp only [Fin.isValue, zero_ne_one, iff_false] at ih'
        have h0' : grade (fun i => q i.fst) a.tail.toList  = 0 := by
          simp [tail]
          omega
        rw [h0, h0']
    rw [h1]


@[simp]
lemma toList_grade_take {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) : (r : List I) →  (a : CreatAnnilateSect f r) → (n : ℕ) →
    grade (fun i => q i.fst) (List.take n a.toList) = grade q (List.take n r)
  | [], _, _ => by
    simp [toList]
  | i :: r, a, 0 => by
    simp
  | i :: r, a, Nat.succ n => by
    simp only [grade, Fin.isValue]
    rw [toList_grade_take q r a.tail n]


def extractEquiv  {I : Type} {f : I → Type} [(i : I) → Fintype (f i)] {l : List I} (n : Fin l.length) : CreatAnnilateSect f l ≃
    f (l.get n) × CreatAnnilateSect f (l.eraseIdx n) := by
  match l with
  | [] => exact Fin.elim0 n
  | l0 :: l =>
    let e1 : CreatAnnilateSect f ((l0 :: l).eraseIdx n) ≃ Π i, f ((l0 :: l).get (n.succAbove i)) :=
      Equiv.piCongr (Fin.castOrderIso (by rw [eraseIdx_cons_length])).toEquiv
      fun x => Equiv.cast (congrArg f (by
      rw [HepLean.List.eraseIdx_get]
      simp
      congr 1
      simp [Fin.succAbove]
      split
      next h =>
        simp_all only [Fin.coe_castSucc]
        split
        next h_1 => simp_all only [Fin.coe_castSucc, Fin.coe_cast]
        next h_1 =>
          simp_all only [not_lt, Fin.val_succ, Fin.coe_cast, self_eq_add_right, one_ne_zero]
          simp [Fin.le_def] at h_1
          simp [Fin.lt_def] at h
          omega
      next h =>
        simp_all only [not_lt, Fin.val_succ]
        split
        next h_1 =>
          simp_all only [Fin.coe_castSucc, Fin.coe_cast, add_right_eq_self, one_ne_zero]
          simp [Fin.lt_def] at h_1
          simp [Fin.le_def] at h
          omega
        next h_1 => simp_all only [not_lt, Fin.val_succ, Fin.coe_cast]))
    exact (Fin.insertNthEquiv _ _).symm.trans (Equiv.prodCongr (Equiv.refl _) e1.symm)

lemma extractEquiv_symm_toList_get_same  {I : Type} {f : I → Type} [(i : I) → Fintype (f i)]
    {l : List I} (n : Fin l.length) (a0 : f (l.get n)) (a : CreatAnnilateSect f (l.eraseIdx n)) :
    ((extractEquiv n).symm (a0, a)).toList[n] = ⟨l[n], a0⟩ := by
  match l with
  | [] => exact Fin.elim0 n
  | l0 :: l =>
    trans  (((CreatAnnilateSect.extractEquiv n).symm (a0, a)).toList).get (Fin.cast (by simp) n)
    · simp only [List.length_cons, List.get_eq_getElem, Fin.coe_cast]
      rfl
    rw [CreatAnnilateSect.toList_get]
    simp only [List.get_eq_getElem, List.length_cons, extractEquiv, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
      Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self, Sigma.mk.inj_iff, heq_eq_eq]
    apply And.intro
    · rfl
    erw [Fin.insertNthEquiv_apply]
    simp only [Fin.insertNth_apply_same]

def eraseIdx (n : Fin l.length) :  CreatAnnilateSect f (l.eraseIdx n) :=
  (extractEquiv n a).2

@[simp]
lemma eraseIdx_zero_tail {i : I} {l : List I}  (a : CreatAnnilateSect f (i :: l)) :
    (eraseIdx a (@OfNat.ofNat (Fin (l.length + 1)) 0 Fin.instOfNat : Fin (l.length + 1))) =
    a.tail := by
  simp [eraseIdx, extractEquiv]
  rfl

lemma eraseIdx_succ_head {i : I} {l : List I} (n : ℕ) (hn : n + 1 < (i :: l).length) (a : CreatAnnilateSect f (i :: l)) :
    (eraseIdx a ⟨n + 1, hn⟩).head = a.head := by
  rw [eraseIdx, extractEquiv]
  simp
  conv_lhs =>
    rhs
    rhs
    rhs
    erw [Fin.insertNthEquiv_symm_apply]
  simp [head, Equiv.piCongr, Equiv.piCongrRight, Equiv.piCongrLeft, Equiv.piCongrLeft']
  simp [Fin.removeNth, Fin.succAbove]
  refine cast_eq_iff_heq.mpr ?_
  congr
  simp [Fin.ext_iff]

lemma eraseIdx_succ_tail {i : I} {l : List I} (n : ℕ) (hn : n + 1 < (i :: l).length) (a : CreatAnnilateSect f (i :: l)) :
    (eraseIdx a ⟨n + 1, hn⟩).tail = eraseIdx a.tail ⟨n , Nat.succ_lt_succ_iff.mp hn⟩ := by
  match l with
  | [] =>
    simp at hn
  | r0 :: r =>
  rw [eraseIdx, extractEquiv]
  simp
  conv_lhs =>
    rhs
    rhs
    rhs
    erw [Fin.insertNthEquiv_symm_apply]
  rw [eraseIdx]
  conv_rhs =>
    rhs
    rw [extractEquiv]
    simp
    erw [Fin.insertNthEquiv_symm_apply]
  simp [tail, Equiv.piCongr, Equiv.piCongrRight, Equiv.piCongrLeft, Equiv.piCongrLeft']
  funext i
  simp
  have hcast {α β : Type} (h : α = β) (a : α) (b : β) : cast h a = b ↔ a = cast (Eq.symm h) b := by
    cases h
    simp
  rw [hcast]
  simp
  refine eq_cast_iff_heq.mpr ?_
  simp [Fin.removeNth, Fin.succAbove]
  congr
  simp [Fin.ext_iff]
  split
  next h =>
    simp_all only [Fin.coe_castSucc, Fin.val_succ, Fin.coe_cast, add_left_inj]
    split
    next h_1 => simp_all only [Fin.coe_castSucc, Fin.coe_cast]
    next h_1 =>
      simp_all only [not_lt, Fin.val_succ, Fin.coe_cast, self_eq_add_right, one_ne_zero]
      simp [Fin.lt_def] at h
      simp [Fin.le_def] at h_1
      omega
  next h =>
    simp_all only [not_lt, Fin.val_succ, Fin.coe_cast, add_left_inj]
    split
    next h_1 =>
      simp_all only [Fin.coe_castSucc, Fin.coe_cast, add_right_eq_self, one_ne_zero]
      simp [Fin.le_def] at h
      simp [Fin.lt_def] at h_1
      omega
    next h_1 => simp_all only [not_lt, Fin.val_succ, Fin.coe_cast]

lemma eraseIdx_toList  : {l : List I} → {n : Fin l.length} → (a : CreatAnnilateSect f l) →
    (eraseIdx a n).toList = a.toList.eraseIdx n
  | [], n, _ => Fin.elim0 n
  | r0 :: r, ⟨0, h⟩, a => by
    simp [toList_tail]
  | r0 :: r, ⟨n + 1, h⟩, a => by
    simp [toList]
    apply And.intro
    · rw [eraseIdx_succ_head]
    · conv_rhs => rw [← eraseIdx_toList (l := r) (n := ⟨n,  Nat.succ_lt_succ_iff.mp h⟩) a.tail]
      rw [eraseIdx_succ_tail]

lemma extractEquiv_symm_eraseIdx {I : Type} {f : I → Type} [(i : I) → Fintype (f i)]
    {l : List I} (n : Fin l.length) (a0 : f l[↑n]) (a : CreatAnnilateSect f (l.eraseIdx n)) :
    ((extractEquiv n).symm (a0, a)).eraseIdx n = a := by
  match l with
  | [] => exact Fin.elim0 n
  | l0 :: l =>
    rw [eraseIdx, extractEquiv]
    simp

lemma toList_koszulSignInsert  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (a : CreatAnnilateSect f l) (x : (i : I) × f i):
    koszulSignInsert (fun i j => le1 i.fst j.fst) (fun i => q i.fst) x a.toList  =
    koszulSignInsert le1 q x.1 l := by
  induction l with
  | nil => simp [koszulSignInsert]
  | cons b l ih =>
    simp [koszulSignInsert]
    rw [ih]

lemma toList_koszulSign  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (a : CreatAnnilateSect f l) :
    koszulSign (fun i j => le1 i.fst j.fst) (fun i => q i.fst) a.toList  =
    koszulSign le1 q l := by
  induction l with
  | nil => simp [koszulSign]
  | cons i l ih =>
    simp [koszulSign, liftM]
    rw [ih]
    congr 1
    rw [toList_koszulSignInsert]


lemma insertionSortEquiv_toList {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1](l : List I)
      (a : CreatAnnilateSect f l)  :
    insertionSortEquiv (fun i j => le1 i.fst j.fst) a.toList =
    (Fin.castOrderIso (by simp)).toEquiv.trans ((insertionSortEquiv le1 l).trans
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
    have h2' (i : Σ i, f i) (l' : List ( Σ i, f i)) :
      List.map (fun i => i.1) (List.orderedInsert (fun i j => le1 i.fst j.fst) i l') =
      List.orderedInsert le1 i.1 (List.map (fun i => i.1) l') := by
      induction l' with
      | nil =>
        simp [HepLean.List.orderedInsertEquiv]
      | cons j l' ih' =>
        by_cases hij : (fun i j => le1 i.fst j.fst)  i j
        · rw [List.orderedInsert_of_le]
          · erw [List.orderedInsert_of_le]
            · simp
            · exact hij
          · exact hij
        · simp only [List.orderedInsert, hij, ↓reduceIte, List.unzip_snd, List.map_cons]
          have hn : ¬ le1 i.1 j.1 := hij
          simp only [hn, ↓reduceIte, List.cons.injEq, true_and]
          simpa using ih'
    have h2 (l' : List ( Σ i, f i)) :
        List.map (fun i => i.1) (List.insertionSort (fun i j => le1 i.fst j.fst) l') =
        List.insertionSort le1 (List.map (fun i => i.1) l') := by
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
    have h3 : (List.insertionSort le1 (List.map (fun i => i.1) a.tail.toList)) =
      List.insertionSort le1 l := by
      congr
      have h3' (l : List I) (a : CreatAnnilateSect f l) :
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


def sort (le1 : I → I → Prop) [DecidableRel le1] : CreatAnnilateSect f (List.insertionSort le1 l) :=
  Equiv.piCongr (HepLean.List.insertionSortEquiv le1 l) (fun i => (Equiv.cast (by
      congr 1
      rw [← HepLean.List.insertionSortEquiv_get]
      simp))) a

lemma sort_toList {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1](l : List I)  (a : CreatAnnilateSect f l) :
    (a.sort le1).toList =  List.insertionSort (fun i j => le1 i.fst j.fst) a.toList := by
  let l1 := List.insertionSort (fun i j => le1 i.fst j.fst) a.toList
  let l2 := (a.sort le1).toList
  symm
  change l1 = l2
  have hlen : l1.length = l2.length := by
    simp [l1, l2]
  have hget : l1.get = l2.get ∘ Fin.cast hlen := by
    rw [← HepLean.List.insertionSortEquiv_get]
    rw [toList_get, toList_get]
    funext i
    rw [insertionSortEquiv_toList]
    simp only [ Function.comp_apply, Equiv.symm_trans_apply,
      OrderIso.toEquiv_symm, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, id_eq, eq_mpr_eq_cast, Fin.coe_cast, Sigma.mk.inj_iff]
    apply And.intro
    · have h1 := congrFun (HepLean.List.insertionSortEquiv_get (r := le1) l) (Fin.cast (by simp) i)
      rw [← h1]
      simp
    · simp [Equiv.piCongr, sort]
      exact (cast_heq _ _).symm
  apply List.ext_get hlen
  rw [hget]
  simp

end CreatAnnilateSect


lemma ofListM_expand {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (x : ℂ) :
    (l : List I) → ofListM f l x = ∑ (a : CreatAnnilateSect f l), ofList a.toList x
  | [] => by
    simp only [ofListM, CreatAnnilateSect, List.length_nil, List.get_eq_getElem, Finset.univ_unique,
      CreatAnnilateSect.toList, Finset.sum_const, Finset.card_singleton, one_smul]
    rw [ofList_eq_smul_one, map_smul, ofList_empty, ofList_eq_smul_one, ofList_empty, map_one]
  | i :: l => by
    rw [ofListM_cons, ofListM_expand f x l]
    conv_rhs => rw [← (CreatAnnilateSect.extractEquiv
        ⟨0, by exact Nat.zero_lt_succ l.length⟩).symm.sum_comp (α := FreeAlgebra ℂ _)]
    erw [Finset.sum_product]
    rw [Finset.sum_mul]
    conv_lhs =>
      rhs
      intro n
      rw [Finset.mul_sum]
    congr
    funext j
    congr
    funext n
    rw [← ofList_singleton, ← ofList_pair, one_mul]
    rfl

lemma koszulOrder_ofListM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (x : ℂ) : koszulOrder (fun i j => le1 i.1 j.1) (fun i => q i.fst) (ofListM f l x) =
    freeAlgebraMap f (koszulOrder le1 q (ofList l x)) := by
  rw [koszulOrder_ofList]
  rw [map_smul]
  change _ = _ • ofListM _ _ _
  rw [ofListM_expand]
  rw [map_sum]
  conv_lhs =>
    rhs
    intro a
    rw [koszulOrder_ofList]
    rw [CreatAnnilateSect.toList_koszulSign]
  rw [← Finset.smul_sum]
  apply congrArg
  conv_lhs =>
    rhs
    intro n
    rw [← CreatAnnilateSect.sort_toList]
  rw [ofListM_expand]
  refine Fintype.sum_equiv ((HepLean.List.insertionSortEquiv le1 l).piCongr fun i => Equiv.cast ?_) _ _ ?_
  congr 1
  · rw [← HepLean.List.insertionSortEquiv_get]
    simp
  · intro x
    rfl

lemma koszulOrder_ofListM_eq_ofListM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (x : ℂ) : koszulOrder (fun i j => le1 i.1 j.1) (fun i => q i.fst) (ofListM f l x) =
    koszulSign le1 q l • ofListM f (List.insertionSort le1 l) x := by
  rw [koszulOrder_ofListM, koszulOrder_ofList, map_smul]
  rfl

end
end Wick
