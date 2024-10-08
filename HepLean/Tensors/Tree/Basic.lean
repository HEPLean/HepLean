/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ColorCat.Basic
/-!

## Tensor trees

-/

open IndexNotation
open CategoryTheory

structure TensorStruct where
  C : Type
  G : Type
  G_group : Group G
  k : Type
  k_commRing : CommRing k
  F : MonoidalFunctor (OverColor C) (Rep k G)
  τ : C → C
  evalNo : C → N

namespace TensorStruct

variable (S : TensorStruct)

instance : CommRing S.k := S.k_commRing

instance : Group S.G := S.G_group

end TensorStruct

inductive TensorTree (S : TensorStruct) : ∀ {n : ℕ}, (Fin n → S.C) → Type where
  | tensorNode {n : ℕ} {c : Fin n → S.C} : S.F.obj (OverColor.mk c) → TensorTree S c
  | add {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c → TensorTree S c
  | perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) : TensorTree S c1
  | prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t : TensorTree S c) (t1 : TensorTree S c1) : TensorTree S (Sum.elim c c1 ∘ finSumFinEquiv.symm)
  | scale {n : ℕ} {c : Fin n → S.C} : S.k → TensorTree S c → TensorTree S c
  | mult {n m : ℕ} {c : Fin n.succ → S.C} {c1 : Fin m.succ → S.C} :
    (i : Fin n.succ) → (j : Fin m.succ) → TensorTree S c → TensorTree S c1 →
    TensorTree S (Sum.elim (c ∘ Fin.succAbove i) (c1 ∘ Fin.succAbove j) ∘ finSumFinEquiv.symm)
  | contr {n : ℕ} {c : Fin n.succ.succ → S.C} : (i : Fin n.succ.succ) →
    (j : Fin n.succ) → TensorTree S c → TensorTree S (c ∘ Fin.succAbove i ∘ Fin.succAbove j)
  | jiggle {n : ℕ} {c : Fin n → S.C} : (i : Fin n) → TensorTree S c  →
     TensorTree S (Function.update c i (S.τ (c i)))
  | eval {n : ℕ} {c : Fin n.succ → S.C} : TensorTree S c →
    (i : Fin n.succ) → (x : Fin (S.evalNo (c i))) →
     TensorTree S (c ∘ Fin.succAbove i)

namespace TensorTree

variable {S : TensorStruct} {n : ℕ} {c : Fin n → S.C} (T : TensorTree S c)

open MonoidalCategory
open TensorProduct

def size : ∀  {n : ℕ} {c : Fin n → S.C}, TensorTree S c → ℕ := fun
  | tensorNode _ => 1
  | add t1 t2 => t1.size + t2.size + 1
  | perm _ t => t.size + 1
  | scale _ t => t.size + 1
  | prod t1 t2 => t1.size + t2.size + 1
  | mult _ _ t1 t2 => t1.size + t2.size + 1
  | contr _ _ t => t.size + 1
  | jiggle _ t => t.size + 1
  | eval t _ _ => t.size + 1


noncomputable section

def tensor : ∀  {n : ℕ} {c : Fin n → S.C}, TensorTree S c → S.F.obj (OverColor.mk c) := fun
  | tensorNode t => t
  | add t1 t2 => t1.tensor + t2.tensor
  | perm σ t => (S.F.map σ).hom t.tensor
  | scale a t => a • t.tensor
  | prod t1 t2 => (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor))
  | _ => 0

lemma tensor_tensorNode {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    (tensorNode T).tensor = T := rfl

end

end TensorTree
