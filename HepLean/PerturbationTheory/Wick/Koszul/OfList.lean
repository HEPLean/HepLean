/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
import HepLean.Lorentz.RealVector.Basic
import HepLean.Mathematics.Fin
import HepLean.SpaceTime.Basic
import HepLean.Mathematics.SuperAlgebra.Basic
import HepLean.Mathematics.List
import HepLean.Meta.Notes.Basic
import Init.Data.List.Sort.Basic
import Mathlib.Data.Fin.Tuple.Take
import HepLean.PerturbationTheory.Wick.Koszul.Grade
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

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

lemma ofListM_cons_eq_ofListM {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (r : List I)  (x : ℂ) :
    ofListM f (i :: r) x = ofListM f [i] 1 * ofListM f r x  := by
  rw [ofListM_cons, ofListM_singleton]
  simp only [one_smul]

def liftM {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  :
    (l : List I) →  (a : Π i, f (l.get i)) →  List (Σ i, f i)
  | [], _ => []
  | i :: l, a => ⟨i, a ⟨0, Nat.zero_lt_succ l.length⟩⟩ :: liftM f l (fun i => a (Fin.succ i))

@[simp]
lemma liftM_length {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (r : List I) (a : Π i, f (r.get i)) :
    (liftM f r a).length = r.length := by
  induction r with
  | nil => rfl
  | cons i r ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, add_left_inj]
    rw [ih]

lemma liftM_get {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (r : List I) (a : Π i, f (r.get i)) :
    (liftM f r a).get = (fun i => ⟨r.get i, a i⟩) ∘ Fin.cast (by simp) := by
  induction r with
  | nil =>
    funext i
    exact Fin.elim0 i
  | cons i l ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, List.get_eq_getElem]
    funext x
    match x with
    | ⟨0, h⟩ => rfl
    | ⟨x + 1, h⟩ =>
      simp only [List.length_cons, List.get_eq_getElem, Prod.mk.eta, List.getElem_cons_succ,
        Function.comp_apply, Fin.cast_mk]
      change (liftM f _ _).get _ = _
      rw [ih]
      simp

lemma ofListM_expand {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (x : ℂ) :
    (l : List I) → ofListM f l x = ∑ (a : Π i, f (l.get i)), ofList (liftM f l a) x
  | [] => by
    simp only [ofListM, List.length_nil, List.get_eq_getElem, Finset.univ_unique, liftM,
      Finset.sum_const, Finset.card_singleton, one_smul]
    rw [ofList_eq_smul_one, map_smul, ofList_empty, ofList_eq_smul_one, ofList_empty, map_one]
  | i :: l => by
    rw [ofListM_cons, ofListM_expand f x l]
    let e1 :  f i × (Π j, f (l.get j)) ≃ (Π j, f ((i :: l).get j)) :=
      (Fin.insertNthEquiv (fun j => f ((i :: l).get j)) 0)
    rw [← e1.sum_comp (α := FreeAlgebra ℂ _)]
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


@[simp]
lemma liftM_grade {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I) (a : Π i, f (r.get i))  :
    grade (fun i => q i.fst) (liftM f r a) = 1 ↔ grade q r = 1 := by
  induction r with
  | nil =>
    simp [liftM]
  | cons i r ih =>
    simp only [grade, Fin.isValue, ite_eq_right_iff, zero_ne_one, imp_false]
    have ih' := ih (fun i => a i.succ)
    have h1 : grade (fun i => q i.fst) (liftM f r fun i => a i.succ) = grade q r  := by
      by_cases h : grade q r = 1
      · simp_all
      · have h0 : grade q r = 0 := by
          omega
        rw [h0] at ih'
        simp only [Fin.isValue, zero_ne_one, iff_false] at ih'
        have h0' : grade (fun i => q i.fst) (liftM f r fun i => a i.succ)  = 0 := by
          omega
        rw [h0, h0']
    rw [h1]

lemma liftM_grade_take {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) : (r : List I) →  (a : Π i, f (r.get i)) → (n : ℕ) →
    grade (fun i => q i.fst) (List.take n (liftM f r a)) = grade q (List.take n r)
  | [], _, _ => by
    simp [liftM]
  | i :: r, a, 0 => by
    simp
  | i :: r, a, Nat.succ n => by
    simp only [grade, Fin.isValue]
    have ih : grade (fun i => q i.fst) (List.take n (liftM f r fun i => a i.succ))  = grade q (List.take n r) := by
      refine (liftM_grade_take q r (fun i => a i.succ) n)
    rw [ih]


lemma koszulSignInsert_liftM  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (a : (j : Fin l.length) → f (l.get j)) (x : (i : I) × f i):
    koszulSignInsert (fun i j => le1 i.fst j.fst) (fun i => q i.fst) x
      (liftM f l a)  =
    koszulSignInsert le1 q x.1 l := by
  induction l with
  | nil => simp [koszulSignInsert]
  | cons b l ih =>
    simp [koszulSignInsert]
    rw [ih]

lemma koszulSign_liftM  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (a : (i : Fin l.length) → f (l.get i)) :
    koszulSign (fun i j => le1 i.fst j.fst) (fun i => q i.fst) (liftM f l a) =
    koszulSign le1 q l := by
  induction l with
  | nil => simp [koszulSign]
  | cons i l ih =>
    simp [koszulSign, liftM]
    rw [ih]
    congr 1
    rw [koszulSignInsert_liftM]

lemma insertionSortEquiv_liftM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1](l : List I)  (a : (i : Fin l.length) → f (l.get i))  :
    (HepLean.List.insertionSortEquiv (fun i j => le1 i.fst j.fst) (liftM f l a)) =
    (Fin.castOrderIso (by simp)).toEquiv.trans ((HepLean.List.insertionSortEquiv le1 l).trans
    (Fin.castOrderIso (by simp)).toEquiv) := by
  induction l with
  | nil =>
    simp [liftM, HepLean.List.insertionSortEquiv]
  | cons i l ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, List.insertionSort]
    conv_lhs => simp [HepLean.List.insertionSortEquiv]
    have h1 (l' : List (Σ i, f i)) :
        (HepLean.List.insertEquiv  (fun i j => le1 i.fst j.fst) ⟨i, a ⟨0, by simp⟩⟩ l') =
        (Fin.castOrderIso (by simp)).toEquiv.trans
        ((HepLean.List.insertEquiv le1 i (List.map (fun i => i.1) l')).trans
        (Fin.castOrderIso (by simp [List.orderedInsert_length])).toEquiv) := by
      induction l' with
      | nil =>
        simp only [List.length_cons, Nat.add_zero, Nat.zero_eq, Fin.zero_eta, List.length_singleton,
          List.orderedInsert, HepLean.List.insertEquiv, Fin.castOrderIso_refl,
          OrderIso.refl_toEquiv, Equiv.trans_refl]
        rfl
      | cons j l' ih' =>
        by_cases hr : (fun (i j : Σ i, f i) => le1 i.fst j.fst) ⟨i, a ⟨0, by simp⟩⟩  j
        · rw [HepLean.List.insertEquiv_cons_pos]
          · erw [HepLean.List.insertEquiv_cons_pos]
            · rfl
            · exact hr
          · exact hr
        · rw [HepLean.List.insertEquiv_cons_neg]
          · erw [HepLean.List.insertEquiv_cons_neg]
            · simp only [List.length_cons, Nat.add_zero, Nat.zero_eq, Fin.zero_eta,
              List.orderedInsert, Prod.mk.eta, Fin.mk_one]
              erw [ih']
              ext x
              simp only [Prod.mk.eta, List.length_cons, Nat.add_zero, Nat.zero_eq, Fin.zero_eta,
                HepLean.Fin.equivCons_trans, Nat.succ_eq_add_one,
                HepLean.Fin.equivCons_castOrderIso, Equiv.trans_apply, RelIso.coe_fn_toEquiv,
                Fin.castOrderIso_apply, Fin.cast_trans, Fin.coe_cast]
              congr 2
              match x with
              | ⟨0, h⟩ => rfl
              | ⟨1, h⟩ => rfl
              | ⟨Nat.succ (Nat.succ x), h⟩ => rfl
            · exact hr
          · exact hr
    erw [h1]
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
        simp [HepLean.List.insertEquiv]
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
        simp [HepLean.List.insertEquiv]
      | cons i l' ih' =>
        simp only [List.insertionSort, List.unzip_snd]
        simp only [List.unzip_snd] at h2'
        rw [h2']
        congr
    rw [HepLean.List.insertEquiv_congr _ _ _ (h2 _)]
    simp only [List.length_cons, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.coe_cast]
    have h3 : (List.insertionSort le1 (List.map (fun i => i.1) (liftM f l (fun i => a i.succ)))) =
      List.insertionSort le1 l := by
      congr
      have h3' (l : List I) (a : Π (i : Fin l.length), f (l.get i)) :
        List.map (fun i => i.1) (liftM f l a) = l := by
        induction l with
        | nil => rfl
        | cons i l ih' =>
          simp only [liftM, List.length_cons, Fin.zero_eta, Prod.mk.eta,
            List.unzip_snd, List.map_cons, List.cons.injEq, true_and]
          simpa using ih' _
      rw [h3']
    rw [HepLean.List.insertEquiv_congr _ _ _ h3]
    simp only [List.length_cons, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, Fin.coe_cast]

lemma insertionSort_liftM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1](l : List I)  (a : (i : Fin l.length) → f (l.get i))
    :
    List.insertionSort (fun i j => le1 i.fst j.fst) (liftM f l a) =
    liftM f (List.insertionSort le1 l)
    (Equiv.piCongr (HepLean.List.insertionSortEquiv le1 l) (fun i => (Equiv.cast (by
      congr 1
      rw [← HepLean.List.insertionSortEquiv_get]
      simp))) a) := by
  let l1 := List.insertionSort (fun i j => le1 i.fst j.fst) (liftM f l a)
  let l2 := liftM f (List.insertionSort le1 l)
    (Equiv.piCongr (HepLean.List.insertionSortEquiv le1 l) (fun i => (Equiv.cast (by
      congr 1
      rw [← HepLean.List.insertionSortEquiv_get]
      simp))) a)
  change l1 = l2
  have hlen : l1.length = l2.length := by
    simp [l1, l2]
  have hget : l1.get = l2.get ∘ Fin.cast hlen := by
    rw [← HepLean.List.insertionSortEquiv_get]
    rw [liftM_get, liftM_get]
    funext i
    rw [insertionSortEquiv_liftM]
    simp only [ Function.comp_apply, Equiv.symm_trans_apply,
      OrderIso.toEquiv_symm, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, id_eq, eq_mpr_eq_cast, Fin.coe_cast, Sigma.mk.inj_iff]
    apply And.intro
    · have h1 := congrFun (HepLean.List.insertionSortEquiv_get (r := le1) l) (Fin.cast (by simp) i)
      rw [← h1]
      simp
    · simp [Equiv.piCongr]
      exact (cast_heq _ _).symm
  apply List.ext_get hlen
  rw [hget]
  simp

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
    rw [koszulSign_liftM]
  rw [← Finset.smul_sum]
  apply congrArg
  conv_lhs =>
    rhs
    intro n
    rw [insertionSort_liftM]
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
