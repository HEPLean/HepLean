/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

## Commutativity of two contractions

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorStruct

end TensorStruct

namespace TensorTree

variable {S : TensorStruct}

structure ContrQuartet {n : ℕ} (c : Fin n.succ.succ.succ.succ → S.C) where
  i : Fin n.succ.succ.succ.succ
  j : Fin n.succ.succ.succ
  k : Fin n.succ.succ
  l : Fin n.succ
  hij : c (i.succAbove j) = S.τ (c i)
  hkl : (c ∘ i.succAbove ∘ j.succAbove) (k.succAbove l) = S.τ ((c ∘ i.succAbove ∘ j.succAbove) k)

namespace ContrQuartet
variable {n : ℕ} {c : Fin n.succ.succ.succ.succ → S.C} (q : ContrQuartet c)

def swapI : Fin n.succ.succ.succ.succ := q.i.succAbove (q.j.succAbove q.k)


 /-
 (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i).succAbove ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l)

 predAboveI
    ((predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i).succAbove
      ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l))
    (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i)

  predAboveI ((predAboveI (q.j.succAbove q.k) q.j).succAbove q.l) (predAboveI (q.j.succAbove q.k) q.j)
 -/
def swapJ : Fin n.succ.succ.succ := predAboveI q.swapI (q.i.succAbove (q.j.succAbove (q.k.succAbove q.l)))

def swapK :  Fin n.succ.succ := predAboveI q.swapJ (predAboveI q.swapI q.i)

def swapL :  Fin n.succ := predAboveI q.swapK (predAboveI q.swapJ (predAboveI q.swapI (q.i.succAbove q.j)))

@[simp]
lemma swapI_neq_i : ¬ q.swapI = q.i := by
  simp [swapI]
  exact Fin.succAbove_ne q.i (q.j.succAbove q.k)

@[simp]
lemma swapI_neq_succAbove : ¬ q.swapI = q.i.succAbove q.j := by
  simp [swapI]
  apply Function.Injective.ne Fin.succAbove_right_injective
  exact Fin.succAbove_ne q.j q.k

@[simp]
lemma swapI_neq_i_j_k_l_succAbove : ¬ q.swapI = q.i.succAbove (q.j.succAbove (q.k.succAbove q.l)) := by
  simp [swapI]
  apply Function.Injective.ne Fin.succAbove_right_injective
  apply Function.Injective.ne Fin.succAbove_right_injective
  exact Fin.ne_succAbove q.k q.l

@[simp]
lemma swapJ_neq_predAboveI_swapI_i : ¬ q.swapJ = predAboveI q.swapI q.i := by
  simp [swapJ]
  erw [predAbove_eq_iff]
  rw [succsAbove_predAboveI]
  · exact Fin.succAbove_ne q.i (q.j.succAbove (q.k.succAbove q.l))
  · apply Function.Injective.ne Fin.succAbove_right_injective
    apply Function.Injective.ne Fin.succAbove_right_injective
    exact Fin.ne_succAbove q.k q.l
  · simp only [Nat.succ_eq_add_one, ne_eq, swapI_neq_i, not_false_eq_true]

lemma swapJ_neq_predAboveI_swapI_i_succAbove_j :
    ¬q.swapJ = predAboveI q.swapI (q.i.succAbove q.j) := by
  simp [swapJ]
  erw [predAbove_eq_iff]
  rw [succsAbove_predAboveI]
  · apply Function.Injective.ne Fin.succAbove_right_injective
    exact Fin.succAbove_ne q.j (q.k.succAbove q.l)
  · exact swapI_neq_i_j_k_l_succAbove q
  · exact swapI_neq_succAbove q

@[simp]
lemma swapJ_swapI_succAbove : q.swapI.succAbove q.swapJ = (q.i.succAbove (q.j.succAbove (q.k.succAbove q.l))) := by
  simp [swapI, swapJ]
  rw [succsAbove_predAboveI]
  apply Function.Injective.ne Fin.succAbove_right_injective
  simp
  apply Function.Injective.ne Fin.succAbove_right_injective
  exact Fin.ne_succAbove q.k q.l

@[simp]
lemma swapK_swapJ_succAbove : (q.swapJ).succAbove (q.swapK) = predAboveI q.swapI q.i := by
  simp [swapJ, swapK]
  rw [succsAbove_predAboveI]
  simp
  erw [predAbove_eq_iff]
  rw [succsAbove_predAboveI]
  · exact Fin.succAbove_ne q.i (q.j.succAbove (q.k.succAbove q.l))
  · apply Function.Injective.ne Fin.succAbove_right_injective
    apply Function.Injective.ne Fin.succAbove_right_injective
    exact Fin.ne_succAbove q.k q.l
  · simp only [Nat.succ_eq_add_one, ne_eq, swapI_neq_i, not_false_eq_true]

@[simp]
lemma swapK_swapJ_swapI_succAbove : (q.swapI).succAbove ( predAboveI q.swapI q.i) = q.i := by
  rw [succsAbove_predAboveI]
  simp

@[simp]
lemma swapL_swapK_succAbove : (q.swapK).succAbove (q.swapL) =
    predAboveI q.swapJ (predAboveI q.swapI (q.i.succAbove q.j)) := by
  simp [swapK, swapL]
  rw [succsAbove_predAboveI]
  simp
  erw [predAbove_eq_iff]
  rw [succsAbove_predAboveI]
  · erw [predAbove_eq_iff]
    · rw [succsAbove_predAboveI]
      · exact Fin.ne_succAbove q.i q.j
      · exact swapI_neq_i q
    · simp only [Nat.succ_eq_add_one, ne_eq, swapI_neq_succAbove, not_false_eq_true]
  · exact swapJ_neq_predAboveI_swapI_i q
  · exact swapJ_neq_predAboveI_swapI_i_succAbove_j q

@[simp]
lemma swapL_swapK_swapJ_succAbove :
    (q.swapJ).succAbove (predAboveI q.swapJ (predAboveI q.swapI (q.i.succAbove q.j))) =
    (predAboveI q.swapI (q.i.succAbove q.j)) := by
  rw [succsAbove_predAboveI]
  simp
  exact swapJ_neq_predAboveI_swapI_i_succAbove_j q

@[simp]
lemma swapL_swapK_swapJ_swapI_succAbove :
    (q.swapI).succAbove (predAboveI q.swapI (q.i.succAbove q.j)) = (q.i.succAbove q.j) := by
  simp [swapI]
  rw [succsAbove_predAboveI]
  apply Function.Injective.ne Fin.succAbove_right_injective
  exact Fin.succAbove_ne q.j q.k

@[simp]
def swap : ContrQuartet c where
  i := q.swapI
  j := q.swapJ
  k := q.swapK
  l := q.swapL
  hij := by
   simpa using q.hkl
  hkl := by
    simpa using q.hij


lemma swap_map_eq (x : Fin n ): (q.swap.i.succAbove (q.swap.j.succAbove
    (q.swap.k.succAbove (q.swap.l.succAbove x)))) =
    (q.i.succAbove (q.j.succAbove (q.k.succAbove (q.l.succAbove x)))) := by
  rw [succAbove_succAbove_predAboveI q.j q.k]
  rw [succAbove_succAbove_predAboveI q.i]
  apply congrArg

  rw [succAbove_succAbove_predAboveI (predAboveI (q.j.succAbove q.k) q.j)]
  rw [succAbove_succAbove_predAboveI (predAboveI (q.i.succAbove (q.j.succAbove q.k)) q.i)]
  congr



noncomputable section

def contrMapFst := S.contrMap c q.i q.j q.hij

def contrMapSnd := S.contrMap (c ∘ q.i.succAbove ∘ q.j.succAbove) q.k q.l q.hkl

lemma contrMap_swap :
  q.contrMapFst ≫ q.contrMapSnd = q.swap.contrMapFst ≫ q.swap.contrMapSnd
  ≫ S.F.map (OverColor.mkIso (by sorry)).hom := by sorry

end
end ContrQuartet

theorem contr_contr {n : ℕ} {c : Fin n.succ.succ.succ.succ → S.C}
  (i : Fin n.succ.succ.succ.succ) (j : Fin n.succ.succ.succ)
  (k : Fin n.succ.succ) (l : Fin n.succ)
  (hij : c (i.succAbove j) = S.τ (c i))
  (hkl : (c ∘ i.succAbove ∘ j.succAbove) (k.succAbove l) = S.τ ((c ∘ i.succAbove ∘ j.succAbove) k))
  (t : TensorTree S c) :
  (contr k l hkl (contr i j hij t)).tensor =
  (
    contr (i.succAbove (j.succAbove k))
    (predAboveI (i.succAbove (j.succAbove k)) (i.succAbove (j.succAbove (k.succAbove l))))
    (by sorry) t).tensor := by sorry

end TensorTree

end IndexNotation
