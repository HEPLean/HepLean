/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.Contractions.ContrMap
/-!

# Tensor trees

- Tensor trees provide an abstract way to represent tensor expressions.
- Their nodes are either tensors or operations between tensors.
- Every tensor tree has associated with an underlying tensor.
- This is not a one-to-one correspondence. Lots tensor trees represent the same tensor.
  In the same way that lots of tensor expressions represent the same tensor.
- Define a sub-tensor tree as a node of a tensor tree and all child nodes thereof. One
  can replace sub-tensor tree with another tensor tree which has the same underlying tensor
  without changing the underlying tensor of the parent tensor tree. These appear as the e.g.
  the lemmas `contr_tensor_eq` in what follows.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

noncomputable section

/-- A syntax tree for tensor expressions. -/
inductive TensorTree (S : TensorSpecies) : {n : ℕ} → (Fin n → S.C) → Type where
  /-- A general tensor node. -/
  | tensorNode {n : ℕ} {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) : TensorTree S c
  /-- A node corresponding to the scalar multiple of a tensor by a element of the field. -/
  | smul {n : ℕ} {c : Fin n → S.C} : S.k → TensorTree S c → TensorTree S c
  /-- A node corresponding to negation of a tensor. -/
  | neg {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c
  /-- A node corresponding to the addition of two tensors. -/
  | add {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c → TensorTree S c
  /-- A node corresponding to the action of a group element on a tensor. -/
  | action {n : ℕ} {c : Fin n → S.C} : S.G → TensorTree S c → TensorTree S c
  /-- A node corresponding to the permutation of indices of a tensor. -/
  | perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) : TensorTree S c1
  /-- A node corresponding to the product of two tensors. -/
  | prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t : TensorTree S c) (t1 : TensorTree S c1) : TensorTree S (Sum.elim c c1 ∘ finSumFinEquiv.symm)
  /-- A node corresponding to the contraction of indices of a tensor. -/
  | contr {n : ℕ} {c : Fin n.succ.succ → S.C} : (i : Fin n.succ.succ) →
    (j : Fin n.succ) → (h : c (i.succAbove j) = S.τ (c i)) → TensorTree S c →
    TensorTree S (c ∘ i.succAbove ∘ j.succAbove)
  /-- A node corresponding to the evaluation of an index of a tensor. -/
  | eval {n : ℕ} {c : Fin n.succ → S.C} : (i : Fin n.succ) → (x : ℕ) → TensorTree S c →
    TensorTree S (c ∘ i.succAbove)

namespace TensorTree

variable {S : TensorSpecies} {n : ℕ} {c : Fin n → S.C} (T : TensorTree S c)

open MonoidalCategory
open TensorProduct

/-!

## Composite nodes

-/

/-- A node consisting of a single vector. -/
def vecNode {c : S.C} (v : S.FD.obj (Discrete.mk c)) : TensorTree S ![c] :=
  perm (OverColor.mkIso (by
    ext x; fin_cases x; rfl)).hom
  (tensorNode ((OverColor.forgetLiftApp S.FD c).symm.hom.hom v))

/-- The node `vecNode` of a tensor tree, with all arguments explicit. -/
abbrev vecNodeE (S : TensorSpecies) (c1 : S.C)
    (v : (S.FD.obj (Discrete.mk c1)).V) :
    TensorTree S ![c1] := vecNode v

/-- A node consisting of a two tensor. -/
def twoNode {c1 c2 : S.C} (t : (S.FD.obj (Discrete.mk c1) ⊗
    S.FD.obj (Discrete.mk c2)).V) :
    TensorTree S ![c1, c2] :=
  (tensorNode ((OverColor.Discrete.pairIsoSep S.FD).hom.hom t))

/-- The node `twoNode` of a tensor tree, with all arguments explicit. -/
abbrev twoNodeE (S : TensorSpecies) (c1 c2 : S.C)
    (v : (S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)).V) :
    TensorTree S ![c1, c2] := twoNode v

/-- A node consisting of a three tensor. -/
def threeNode {c1 c2 c3 : S.C} (t : (S.FD.obj (Discrete.mk c1) ⊗
    S.FD.obj (Discrete.mk c2) ⊗ S.FD.obj (Discrete.mk c3)).V) :
    TensorTree S ![c1, c2, c3] :=
  (tensorNode ((OverColor.Discrete.tripleIsoSep S.FD).hom.hom t))

/-- The node `threeNode` of a tensor tree, with all arguments explicit. -/
abbrev threeNodeE (S : TensorSpecies) (c1 c2 c3 : S.C)
    (v : (S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
    S.FD.obj (Discrete.mk c3)).V) :
    TensorTree S ![c1, c2, c3] := threeNode v

/-- A general constant node. -/
def constNode {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep S.k S.G) ⟶ S.F.obj (OverColor.mk c)) :
    TensorTree S c := tensorNode (T.hom (1 : S.k))

/-- A constant vector. -/
def constVecNode {c : S.C} (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c)) :
    TensorTree S ![c] := vecNode (v.hom (1 : S.k))

/-- A constant two tensor (e.g. metric and unit). -/
def constTwoNode {c1 c2 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
    TensorTree S ![c1, c2] := twoNode (v.hom (1 : S.k))

/-- The node `constTwoNode` of a tensor tree, with all arguments explicit. -/
abbrev constTwoNodeE (S : TensorSpecies) (c1 c2 : S.C)
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
    TensorTree S ![c1, c2] := constTwoNode v

/-- A constant three tensor (e.g. Pauli matrices). -/
def constThreeNode {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
    S.FD.obj (Discrete.mk c3)) : TensorTree S ![c1, c2, c3] :=
  threeNode (v.hom (1 : S.k))

/-- The node `constThreeNode` of a tensor tree, with all arguments explicit. -/
abbrev constThreeNodeE (S : TensorSpecies) (c1 c2 c3 : S.C)
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
    S.FD.obj (Discrete.mk c3)) : TensorTree S ![c1, c2, c3] :=
  constThreeNode v

/-!

## Other operations.

-/
/-- The number of nodes in a tensor tree. -/
def size {n : ℕ} {c : Fin n → S.C} : TensorTree S c → ℕ := fun
  | tensorNode _ => 1
  | add t1 t2 => t1.size + t2.size + 1
  | perm _ t => t.size + 1
  | neg t => t.size + 1
  | smul _ t => t.size + 1
  | prod t1 t2 => t1.size + t2.size + 1
  | contr _ _ _ t => t.size + 1
  | eval _ _ t => t.size + 1
  | action _ t => t.size + 1

noncomputable section

/-- The underlying tensor a tensor tree corresponds to. -/
def tensor {n : ℕ} {c : Fin n → S.C} : TensorTree S c → S.F.obj (OverColor.mk c) := fun
  | tensorNode t => t
  | smul a t => a • t.tensor
  | neg t => - t.tensor
  | add t1 t2 => t1.tensor + t2.tensor
  | action g t => (S.F.obj (OverColor.mk _)).ρ g t.tensor
  | perm σ t => (S.F.map σ).hom t.tensor
  | prod t1 t2 => (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor))
  | contr i j h t => (S.contrMap _ i j h).hom t.tensor
  | eval i e t => (S.evalMap i (Fin.ofNat' _ e)) t.tensor

/-- Takes a tensor tree based on `Fin 0`, into the field `S.k`. -/
def field {c : Fin 0 → S.C} (t : TensorTree S c) : S.k := S.castFin0ToField t.tensor

/-!

## Tensor on different nodes.

-/

@[simp]
lemma tensorNode_tensor {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    (tensorNode T).tensor = T := rfl

@[simp]
lemma constTwoNode_tensor {c1 c2 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
    (constTwoNode v).tensor =
    (OverColor.Discrete.pairIsoSep S.FD).hom.hom (v.hom (1 : S.k)) :=
  rfl

@[simp]
lemma constThreeNode_tensor {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
    S.FD.obj (Discrete.mk c3)) :
    (constThreeNode v).tensor =
    (OverColor.Discrete.tripleIsoSep S.FD).hom.hom (v.hom (1 : S.k)) :=
  rfl

lemma prod_tensor {c1 : Fin n → S.C} {c2 : Fin m → S.C} (t1 : TensorTree S c1)
    (t2 : TensorTree S c2) :
    (prod t1 t2).tensor = (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor)) := rfl

lemma add_tensor (t1 t2 : TensorTree S c) : (add t1 t2).tensor = t1.tensor + t2.tensor := rfl

lemma perm_tensor (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
    (perm σ t).tensor = (S.F.map σ).hom t.tensor := rfl

lemma contr_tensor {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)} (t : TensorTree S c) :
    (contr i j h t).tensor = (S.contrMap c i j h).hom t.tensor := rfl

lemma neg_tensor (t : TensorTree S c) : (neg t).tensor = - t.tensor := rfl

lemma eval_tensor {n : ℕ} {c : Fin n.succ → S.C} (i : Fin n.succ) (e : ℕ) (t : TensorTree S c) :
    (eval i e t).tensor = (S.evalMap i (Fin.ofNat' (S.repDim (c i)) e)) t.tensor := rfl

lemma smul_tensor {c : Fin n → S.C} (a : S.k) (T : TensorTree S c) :
    (smul a T).tensor = a • T.tensor:= rfl

lemma action_tensor {c : Fin n → S.C} (g : S.G) (T : TensorTree S c) :
    (action g T).tensor = (S.F.obj (OverColor.mk c)).ρ g T.tensor := rfl

/-!

## Equality of tensors and rewrites.

-/
lemma contr_tensor_eq {n : ℕ} {c : Fin n.succ.succ → S.C} {T1 T2 : TensorTree S c}
    (h : T1.tensor = T2.tensor) {i : Fin n.succ.succ} {j : Fin n.succ}
    {h' : c (i.succAbove j) = S.τ (c i)} :
    (contr i j h' T1).tensor = (contr i j h' T2).tensor := by
  simp only [Nat.succ_eq_add_one, contr_tensor]
  rw [h]

lemma prod_tensor_eq_fst {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {T1 T1' : TensorTree S c} { T2 : TensorTree S c1}
    (h : T1.tensor = T1'.tensor) :
    (prod T1 T2).tensor = (prod T1' T2).tensor := by
  simp only [prod_tensor, Functor.id_obj, OverColor.mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [h]

lemma prod_tensor_eq_snd {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {T1 : TensorTree S c} {T2 T2' : TensorTree S c1}
    (h : T2.tensor = T2'.tensor) :
    (prod T1 T2).tensor = (prod T1 T2').tensor := by
  simp only [prod_tensor, Functor.id_obj, OverColor.mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [h]

lemma perm_tensor_eq {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)} {T1 T2 : TensorTree S c}
    (h : T1.tensor = T2.tensor) :
    (perm σ T1).tensor = (perm σ T2).tensor := by
  simp only [perm_tensor]
  rw [h]

lemma add_tensor_eq_fst {T1 T1' T2 : TensorTree S c} (h : T1.tensor = T1'.tensor) :
    (add T1 T2).tensor = (add T1' T2).tensor := by
  simp only [add_tensor]
  rw [h]

lemma add_tensor_eq_snd {T1 T2 T2' : TensorTree S c} (h : T2.tensor = T2'.tensor) :
    (add T1 T2).tensor = (add T1 T2').tensor := by
  simp only [add_tensor]
  rw [h]

lemma add_tensor_eq {T1 T1' T2 T2' : TensorTree S c} (h1 : T1.tensor = T1'.tensor)
    (h2 : T2.tensor = T2'.tensor) :
    (add T1 T2).tensor = (add T1' T2').tensor := by
  simp only [add_tensor]
  rw [h1, h2]

lemma neg_tensor_eq {T1 T2 : TensorTree S c} (h : T1.tensor = T2.tensor) :
    (neg T1).tensor = (neg T2).tensor := by
  simp only [neg_tensor]
  rw [h]

lemma smul_tensor_eq {T1 T2 : TensorTree S c} {a : S.k} (h : T1.tensor = T2.tensor) :
    (smul a T1).tensor = (smul a T2).tensor := by
  simp only [smul_tensor]
  rw [h]

lemma action_tensor_eq {T1 T2 : TensorTree S c} {g : S.G} (h : T1.tensor = T2.tensor) :
    (action g T1).tensor = (action g T2).tensor := by
  simp only [action_tensor]
  rw [h]

lemma smul_mul_eq {T1 : TensorTree S c} {a b : S.k} (h : a = b) :
    (smul a T1).tensor = (smul b T1).tensor := by
  rw [h]

lemma eq_tensorNode_of_eq_tensor {T1 : TensorTree S c} {t : S.F.obj (OverColor.mk c)}
    (h : T1.tensor = t) : T1.tensor = (tensorNode t).tensor := by
  simpa using h

/-!

## The zero tensor tree

-/

/-- The zero tensor tree. -/
def zeroTree {n : ℕ} {c : Fin n → S.C} : TensorTree S c := tensorNode 0

@[simp]
lemma zeroTree_tensor {n : ℕ} {c : Fin n → S.C} : (zeroTree (c := c)).tensor = 0 := by
  rfl

lemma zero_smul {T1 : TensorTree S c} :
    (smul 0 T1).tensor = zeroTree.tensor := by
  simp only [smul_tensor, _root_.zero_smul, zeroTree_tensor]

lemma smul_zero {a : S.k} : (smul a (zeroTree (c := c))).tensor = zeroTree.tensor := by
  simp only [smul_tensor, zeroTree_tensor, _root_.smul_zero]

lemma zero_add {T1 : TensorTree S c} : (add zeroTree T1).tensor = T1.tensor := by
  simp only [add_tensor, zeroTree_tensor, _root_.zero_add]

lemma add_zero {T1 : TensorTree S c} : (add T1 zeroTree).tensor = T1.tensor := by
  simp only [add_tensor, zeroTree_tensor, _root_.add_zero]

lemma perm_zero {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C} (σ : (OverColor.mk c) ⟶
    (OverColor.mk c1)) : (perm σ zeroTree).tensor = zeroTree.tensor := by
  simp only [perm_tensor, zeroTree_tensor, map_zero]

lemma neg_zero : (neg (zeroTree (c := c))).tensor = zeroTree.tensor := by
  simp only [neg_tensor, zeroTree_tensor, _root_.neg_zero]

lemma contr_zero {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)} : (contr i j h zeroTree).tensor = zeroTree.tensor := by
  simp only [contr_tensor, zeroTree_tensor, map_zero]

lemma zero_prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C} (t : TensorTree S c1) :
    (prod (zeroTree (c := c)) t).tensor = zeroTree.tensor := by
  simp only [prod_tensor, Functor.id_obj, OverColor.mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, zeroTree_tensor, zero_tmul, map_zero]

lemma prod_zero {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C} (t : TensorTree S c) :
    (prod t (zeroTree (c := c1))).tensor = zeroTree.tensor := by
  simp only [prod_tensor, Functor.id_obj, OverColor.mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, zeroTree_tensor, tmul_zero, map_zero]

/-- A structure containing a pair of indices (i, j) to be contracted in a tensor.
  This is used in some proofs of node identities for tensor trees. -/
structure ContrPair {n : ℕ} (c : Fin n.succ.succ → S.C) where
  /-- The first index in the pair, appearing on the left in the contraction
    node `contr i j h _`. -/
  i : Fin n.succ.succ
  /-- The second index in the pair, appearing on the right in the contraction
    node `contr i j h _`. -/
  j : Fin n.succ
  /-- A proof that the two indices can be contracted. -/
  h : c (i.succAbove j) = S.τ (c i)

namespace ContrPair
variable {n : ℕ} {c : Fin n.succ.succ → S.C} (q q' : ContrPair c)

lemma ext (hi : q.i = q'.i) (hj : q.j = q'.j) : q = q' := by
  cases q
  cases q'
  subst hi
  subst hj
  rfl

/-- The contraction map for a pair of indices. -/
def contrMap := S.contrMap c q.i q.j q.h

end ContrPair
end

end TensorTree

end
