/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

## Products and contractions


-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies}

namespace ContrPair
variable {n n1 : ℕ} {c : Fin n.succ.succ → S.C} {c1 : Fin n1 → S.C} (q : ContrPair c)

/-!

## Left contractions.

-/
/-- An equivalence needed to perform contraction. For specified `n` and `n1`
  this reduces to an identity. -/
def leftContrEquivSuccSucc : Fin (n.succ.succ + n1) ≃ Fin ((n + n1).succ.succ) :=
  (Fin.castOrderIso (by omega)).toEquiv

/-- An equivalence needed to perform contraction. For specified `n` and `n1`
  this reduces to an identity. -/
def leftContrEquivSucc : Fin (n.succ + n1) ≃ Fin ((n + n1).succ) :=
  (Fin.castOrderIso (by omega)).toEquiv

def leftContrI (n1 : ℕ): Fin ((n + n1).succ.succ) := leftContrEquivSuccSucc <| Fin.castAdd n1 q.i

def leftContrJ (n1 : ℕ) : Fin ((n + n1).succ) := leftContrEquivSucc <| Fin.castAdd n1 q.j

@[simp]
lemma leftContrJ_succAbove_leftContrI : (q.leftContrI n1).succAbove (q.leftContrJ n1)
      = leftContrEquivSuccSucc (Fin.castAdd n1  (q.i.succAbove q.j)) := by
  rw [leftContrI, leftContrJ]
  rw [Fin.ext_iff]
  simp only [Fin.succAbove, Nat.succ_eq_add_one, leftContrEquivSucc, RelIso.coe_fn_toEquiv,
    Fin.castOrderIso_apply, leftContrEquivSuccSucc, Fin.coe_cast, Fin.coe_castAdd]
  split_ifs
    <;> rename_i h1 h2
    <;> rw [Fin.lt_def] at h1 h2
  · simp only [Fin.coe_castSucc, Fin.coe_cast, Fin.coe_castAdd]
  · simp_all only [Fin.coe_castSucc, Fin.coe_cast, Fin.coe_castAdd, not_true_eq_false]
  · simp_all only [Fin.coe_castSucc, Fin.coe_cast, Fin.coe_castAdd, not_lt, Fin.val_succ,
    add_right_eq_self, one_ne_zero]
    omega
  · simp only [Fin.val_succ, Fin.coe_cast, Fin.coe_castAdd]

def leftContr : ContrPair ((Sum.elim c c1 ∘ (@finSumFinEquiv n.succ.succ n1).symm.toFun) ∘
    leftContrEquivSuccSucc.symm) where
  i := q.leftContrI n1
  j := q.leftContrJ n1
  h := by
    simp only [Nat.succ_eq_add_one, Equiv.toFun_as_coe, leftContrJ_succAbove_leftContrI,
      Function.comp_apply, Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    simpa only [leftContrI, Nat.succ_eq_add_one, Equiv.symm_apply_apply,
      finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl] using q.h

lemma leftContr_map_eq : ((Sum.elim c (OverColor.mk c1).hom ∘ finSumFinEquiv.symm.toFun) ∘ ⇑leftContrEquivSuccSucc.symm) ∘
    (q.leftContr (c1 := c1)).i.succAbove ∘ (q.leftContr (c1 := c1)).j.succAbove =
    Sum.elim (OverColor.mk (c ∘ q.i.succAbove ∘ q.j.succAbove)).hom (OverColor.mk c1).hom ∘
    ⇑finSumFinEquiv.symm := by
  funext x
  simp
  sorry

lemma contrMap_prod :
    (q.contrMap ▷ S.F.obj (OverColor.mk c1)) ≫ (S.F.μ _ ((OverColor.mk c1))) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom =
    (S.F.μ ((OverColor.mk c)) ((OverColor.mk c1))) ≫
    S.F.map (OverColor.equivToIso finSumFinEquiv).hom ≫
    S.F.map (OverColor.equivToIso leftContrEquivSuccSucc).hom ≫ q.leftContr.contrMap
    ≫ S.F.map (OverColor.mkIso (q.leftContr_map_eq)).hom  := by
  sorry

/-!

## Right contractions.

-/

end ContrPair

theorem contr_prod {n n1 : ℕ} {c : Fin n.succ.succ → S.C} {c1  : Fin n1 → S.C} {i : Fin n.succ.succ}
    {j : Fin n.succ} (hij : c (i.succAbove j) = S.τ (c i))
    (t : TensorTree S c) (t1 : TensorTree S c1) :
    (prod t t1).tensor =  sorry :=by

  sorry

end TensorTree
