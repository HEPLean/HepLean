/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
/-!

## Congr results

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct

namespace TensorTree

variable {S : TensorSpecies}

/-!

## Congr results

-/
variable {n m : ℕ}

lemma perm_congr {c1 : Fin n → S.C} {c2 : Fin m → S.C} {T T' : TensorTree S c1}
    {σ σ' : OverColor.mk c1 ⟶ OverColor.mk c2}
    (h : σ = σ') (hT : T.tensor = T'.tensor) :
    (perm σ T).tensor = (perm σ' T').tensor := by
  rw [h]
  simp only [perm_tensor, hT]

lemma perm_update {c1 : Fin n → S.C} {c2 : Fin m → S.C} {T : TensorTree S c1}
    {σ : OverColor.mk c1 ⟶ OverColor.mk c2} (σ' : OverColor.mk c1 ⟶ OverColor.mk c2)
    (h : σ = σ') :
    (perm σ T).tensor = (perm σ' T).tensor := by rw [h]

lemma contr_congr {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ}
    (i' : Fin n.succ.succ) {j : Fin n.succ} (j' : Fin n.succ){h : c (i.succAbove j) = S.τ (c i)}
    {t : TensorTree S c} (hi : i = i' := by decide) (hj : j = j' := by decide) :
    (contr i j h t).tensor =
    (perm (mkIso (by rw [hi, hj])).hom (contr i' j' (by rw [← hi, ← hj, h]) t)).tensor := by
  subst hi
  subst hj
  simp [perm_tensor, mkIso_refl_hom]

end TensorTree
