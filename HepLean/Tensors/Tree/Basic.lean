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

/-- The sturcture of a type of tensors e.g. Lorentz tensors, Einstien tensors,
  complex Lorentz tensors.
  Note: This structure is not fully defined yet. -/
structure TensorStruct where
  /-- The colors of indices e.g. up or down. -/
  C : Type
  /-- The symmetry group acting on these tensor e.g. the Lorentz group or SL(2,ℂ). -/
  G : Type
  /-- An instance of `G` as a group. -/
  G_group : Group G
  /-- The field over which we want to consider the tensors to live in, usually `ℝ` or `ℂ`. -/
  k : Type
  /-- An instance of `k` as a commutative ring. -/
  k_commRing : CommRing k
  /-- A `MonoidalFunctor` from `OverColor C` giving the rep corresponding to a map of colors
    `X → C`. -/
  F : MonoidalFunctor (OverColor C) (Rep k G)
  /-- A map from `C` to `C`. An involution. -/
  τ : C → C
  /-- A specification of the dimension of each color in C. This will be used for explicit
    evaluation of tensors. -/
  evalNo : C → ℕ

namespace TensorStruct

variable (S : TensorStruct)

instance : CommRing S.k := S.k_commRing

instance : Group S.G := S.G_group

end TensorStruct

/-- A syntax tree for tensor expressions. -/
inductive TensorTree (S : TensorStruct) : ∀ {n : ℕ}, (Fin n → S.C) → Type where
  | tensorNode {n : ℕ} {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) : TensorTree S c
  | add {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c → TensorTree S c
  | perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) : TensorTree S c1
  | prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t : TensorTree S c) (t1 : TensorTree S c1) : TensorTree S (Sum.elim c c1 ∘ finSumFinEquiv.symm)
  | smul {n : ℕ} {c : Fin n → S.C} : S.k → TensorTree S c → TensorTree S c
  | mult {n m : ℕ} {c : Fin n.succ → S.C} {c1 : Fin m.succ → S.C} :
    (i : Fin n.succ) → (j : Fin m.succ) → TensorTree S c → TensorTree S c1 →
    TensorTree S (Sum.elim (c ∘ Fin.succAbove i) (c1 ∘ Fin.succAbove j) ∘ finSumFinEquiv.symm)
  | contr {n : ℕ} {c : Fin n.succ.succ → S.C} : (i : Fin n.succ.succ) →
    (j : Fin n.succ) → TensorTree S c → TensorTree S (c ∘ Fin.succAbove i ∘ Fin.succAbove j)
  | jiggle {n : ℕ} {c : Fin n → S.C} : (i : Fin n) → TensorTree S c →
    TensorTree S (Function.update c i (S.τ (c i)))
  | eval {n : ℕ} {c : Fin n.succ → S.C} :
    (i : Fin n.succ) → (x : Fin (S.evalNo (c i))) → TensorTree S c →
    TensorTree S (c ∘ Fin.succAbove i)

namespace TensorTree

variable {S : TensorStruct} {n : ℕ} {c : Fin n → S.C} (T : TensorTree S c)

open MonoidalCategory
open TensorProduct

/-- The number of nodes in a tensor tree. -/
def size : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → ℕ := fun
  | tensorNode _ => 1
  | add t1 t2 => t1.size + t2.size + 1
  | perm _ t => t.size + 1
  | smul _ t => t.size + 1
  | prod t1 t2 => t1.size + t2.size + 1
  | mult _ _ t1 t2 => t1.size + t2.size + 1
  | contr _ _ t => t.size + 1
  | jiggle _ t => t.size + 1
  | eval _ _ t => t.size + 1

noncomputable section

/-- The underlying tensor a tensor tree corresponds to.
  Note: This function is not fully defined yet. -/
def tensor : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → S.F.obj (OverColor.mk c) := fun
  | tensorNode t => t
  | add t1 t2 => t1.tensor + t2.tensor
  | perm σ t => (S.F.map σ).hom t.tensor
  | smul a t => a • t.tensor
  | prod t1 t2 => (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor))
  | _ => 0

lemma tensor_tensorNode {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    (tensorNode T).tensor = T := rfl

end

end TensorTree
