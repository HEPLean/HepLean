/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.Basic
/-!

## Basic node identities

This file contains the basic node identities for tensor trees.
More complicated identities appear in there own files.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open PhysLean.Fin
open TensorProduct

namespace TensorTree

variable {S : TensorSpecies}

/-!

## Equality of constructors.

-/

/-- A `constVecNode` has equal tensor to the `vecNode` with the map evaluated at 1. -/
informal_lemma constVecNode_eq_vecNode where
  deps := [``constVecNode, ``vecNode]

/-- A `constTwoNode` has equal tensor to the `twoNode` with the map evaluated at 1. -/
informal_lemma constTwoNode_eq_twoNode where
  deps := [``constTwoNode, ``twoNode]

/-!

## Tensornode

-/

/-- The tensor node of a tensor tree's tensor has a tensor which is the tensor tree's tensor. -/
lemma tensorNode_of_tree (t : TensorTree S c) : (tensorNode t.tensor).tensor = t.tensor := by
  simp [tensorNode]

/-!

## Negation

-/

/-- Two `neg` nodes of a tensor tree cancel. -/
@[simp]
lemma neg_neg (t : TensorTree S c) : (neg (neg t)).tensor = t.tensor := by
  simp only [neg_tensor, _root_.neg_neg]

/-- A `neg` node can be moved out of the LHS of a `prod` node. -/
@[simp]
lemma neg_fst_prod {c1 : Fin n → S.C} {c2 : Fin m → S.C} (T1 : TensorTree S c1)
    (T2 : TensorTree S c2) :
    (prod (neg T1) T2).tensor = (neg (prod T1 T2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, neg_tensor, neg_tmul, map_neg]

/-- A `neg` node can be moved out of the RHS of a `prod` node. -/
@[simp]
lemma neg_snd_prod {c1 : Fin n → S.C} {c2 : Fin m → S.C} (T1 : TensorTree S c1)
    (T2 : TensorTree S c2) :
    (prod T1 (neg T2)).tensor = (neg (prod T1 T2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, neg_tensor, tmul_neg, map_neg]

/-- A `neg` node can be moved through a `contr` node. -/
@[simp]
lemma neg_contr {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)}
    (t : TensorTree S c) : (contr i j h (neg t)).tensor = (neg (contr i j h t)).tensor := by
  simp only [Nat.succ_eq_add_one, contr_tensor, neg_tensor, map_neg]

/-- A `neg` node can be moved through a `perm` node. -/
lemma neg_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
    (perm σ (neg t)).tensor = (neg (perm σ t)).tensor := by
  simp only [perm_tensor, neg_tensor, map_neg]

/-- The negation of a tensor tree plus itself is zero. -/
@[simp]
lemma neg_add (t : TensorTree S c) : (add (neg t) t).tensor = 0 := by
  rw [add_tensor, neg_tensor]
  simp only [neg_add_cancel]

/-- A tensor tree plus its negation is zero. -/
@[simp]
lemma add_neg (t : TensorTree S c) : (add t (neg t)).tensor = 0 := by
  rw [add_tensor, neg_tensor]
  simp only [add_neg_cancel]

/-!

## Basic perm identities

-/

/-- Applying two permutations is the same as applying the transitive permutation. -/
lemma perm_perm {n n1 n2 : ℕ} {c : Fin n → S.C} {c1 : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (σ2 : (OverColor.mk c1) ⟶ (OverColor.mk c2))
    (t : TensorTree S c) : (perm σ2 (perm σ t)).tensor = (perm (σ ≫ σ2) t).tensor := by
  simp [perm_tensor]

/-- Applying the identity permutation is the same as not applying a permutation. -/
lemma perm_id (t : TensorTree S c) : (perm (𝟙 (OverColor.mk c)) t).tensor = t.tensor := by
  simp [perm_tensor]

/-- Applying a permutation which is equal to the identity permutation is the same
  as not applying a permutation. -/
lemma perm_eq_id {n : ℕ} {c : Fin n → S.C} (σ : (OverColor.mk c) ⟶ (OverColor.mk c))
    (h : σ = 𝟙 _) (t : TensorTree S c) : (perm σ t).tensor = t.tensor := by
  simp [perm_tensor, h]

/-- Given an equality of tensors corresponding to tensor trees where the tensor tree on the
  left finishes with a permutation node, this permutation node can be moved to the
  tensor tree on the right. This lemma holds here for isomorphisms only, but holds in practice
  more generally. -/
lemma perm_eq_of_eq_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ≅ (OverColor.mk c1))
    {t : TensorTree S c} {t2 : TensorTree S c1} (h : (perm σ.hom t).tensor = t2.tensor) :
    t.tensor = (perm σ.inv t2).tensor := by
  rw [perm_tensor, ← h]
  change _ = (S.F.map σ.hom ≫ S.F.map σ.inv).hom _
  simp only [Iso.map_hom_inv_id, Action.id_hom, ModuleCat.id_apply]

/-- A permutation of a tensor tree `t1` has equal tensor to a tensor tree `t2` if and only if
  the inverse-permutation of `t2` has equal tensor to `t1`. -/
lemma perm_eq_iff_eq_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1))
    {t : TensorTree S c} {t2 : TensorTree S c1} :
    (perm σ t).tensor = t2.tensor ↔ t.tensor =
    (perm (equivToHomEq (Hom.toEquiv σ).symm (fun x => Hom.toEquiv_comp_apply σ x)) t2).tensor := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · simp only [mk_hom, perm_tensor, ← h]
    change _ = (S.F.map _ ≫ S.F.map _).hom _
    rw [← S.F.map_comp]
    have h1 : (σ ≫ equivToHomEq (Hom.toEquiv σ).symm
        (fun x => Hom.toEquiv_comp_apply σ x)) = 𝟙 _ := by
      apply Hom.ext
      ext x
      change (Hom.toEquiv σ).symm ((Hom.toEquiv σ) x) = x
      simp
    rw [h1]
    simp
  · rw [perm_tensor, h]
    change (S.F.map _ ≫ S.F.map _).hom _ = _
    rw [← S.F.map_comp]
    have h1 : (equivToHomEq (Hom.toEquiv σ).symm
        (fun x => Hom.toEquiv_comp_apply σ x) ≫ σ) = 𝟙 _ := by
      apply Hom.ext
      ext x
      change (Hom.toEquiv σ) ((Hom.toEquiv σ).symm x) = x
      simp [-OverColor.mk_left]
    rw [h1]
    simp

/-!

## Vector based identities

These identities are related to the fact that all the maps are linear.

-/

/-- Two `smul` nodes can be replaced with a single `smul` node with
  the product of the two scalars. -/
lemma smul_smul (t : TensorTree S c) (a b : S.k) :
    (smul a (smul b t)).tensor = (smul (a * b) t).tensor := by
  simp only [smul_tensor]
  exact _root_.smul_smul a b t.tensor

/-- An `smul`-node with scalar `1` does nothing. -/
lemma smul_one (t : TensorTree S c) :
    (smul 1 t).tensor = t.tensor := by
  simp [smul_tensor]

/-- An `smul`-node with scalar equal to `1` does nothing. -/
lemma smul_eq_one (t : TensorTree S c) (a : S.k) (h : a = 1) :
    (smul a t).tensor = t.tensor := by
  rw [h]
  exact smul_one _

/-- The addition node is commutative. -/
lemma add_comm (t1 t2 : TensorTree S c) : (add t1 t2).tensor = (add t2 t1).tensor := by
  simp only [add_tensor]
  exact AddCommMagma.add_comm t1.tensor t2.tensor

/-- The addition node is associative. -/
lemma add_assoc (t1 t2 t3 : TensorTree S c) :
    (add (add t1 t2) t3).tensor = (add t1 (add t2 t3)).tensor := by
  simp only [add_tensor]
  exact _root_.add_assoc t1.tensor t2.tensor t3.tensor

/-- When the same permutation acts on both arguments of an addition, the permutation
  can be moved out of the addition. -/
lemma add_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t t1 : TensorTree S c) :
    (add (perm σ t) (perm σ t1)).tensor = (perm σ (add t t1)).tensor := by
  simp only [add_tensor, perm_tensor, map_add]

/-- When a `perm` acts on an add node, it can be moved through the add-node
  to act on each of the two parts. -/
lemma perm_add {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t t1 : TensorTree S c) :
    (perm σ (add t t1)).tensor = (add (perm σ t) (perm σ t1)).tensor := by
  simp only [add_tensor, perm_tensor, map_add]

/-- A `smul` node can be moved through an `perm` node. -/
lemma perm_smul {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (a : S.k) (t : TensorTree S c) :
    (perm σ (smul a t)).tensor = (smul a (perm σ t)).tensor := by
  simp only [smul_tensor, perm_tensor, map_smul]

/-- When the same evaluation acts on both arguments of an addition, the evaluation
  can be moved out of the addition. -/
lemma add_eval {n : ℕ} {c : Fin n.succ → S.C} (i : Fin n.succ) (e : ℕ) (t t1 : TensorTree S c) :
    (add (eval i e t) (eval i e t1)).tensor = (eval i e (add t t1)).tensor := by
  simp only [add_tensor, eval_tensor, Nat.succ_eq_add_one, map_add]

/-- When a `contr` acts on an add node, it can be moved through the add-node
  to act on each of the two parts. -/
lemma contr_add {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)} (t1 t2 : TensorTree S c) :
  (contr i j h (add t1 t2)).tensor = (add (contr i j h t1) (contr i j h t2)).tensor := by
  simp [contr_tensor, add_tensor]

/-- A `smul` node can be moved through an `contr` node. -/
lemma contr_smul {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)} (a : S.k) (t : TensorTree S c) :
    (contr i j h (smul a t)).tensor = (smul a (contr i j h t)).tensor := by
  simp [contr_tensor, smul_tensor]

/-- When a `prod` acts on an add node on the left, it can be moved through the add-node
  to act on each of the two parts. -/
@[simp]
lemma add_prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t1 t2 : TensorTree S c) (t3 : TensorTree S c1) :
    (prod (add t1 t2) t3).tensor = (add (prod t1 t3) (prod t2 t3)).tensor := by
  simp only [prod_tensor, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, add_tensor, add_tmul, map_add]

/-- When a `prod` acts on an add node on the right, it can be moved through the add-node
  to act on each of the two parts. -/
@[simp]
lemma prod_add {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t1 : TensorTree S c) (t2 t3 : TensorTree S c1) :
    (prod t1 (add t2 t3)).tensor = (add (prod t1 t2) (prod t1 t3)).tensor := by
  simp only [prod_tensor, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, add_tensor, tmul_add, map_add]

/-- A `smul` node in the LHS of a `prod` node can be moved through that `prod` node. -/
lemma smul_prod {n m: ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (a : S.k) (t1 : TensorTree S c) (t2 : TensorTree S c1) :
    ((prod (smul a t1) t2)).tensor = (smul a (prod t1 t2)).tensor := by
  simp [prod_tensor, smul_tensor, tmul_smul, smul_tmul, map_smul]

/-- A `smul` node in the RHS of a `prod` node can be moved through that `prod` node. -/
lemma prod_smul {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (a : S.k) (t1 : TensorTree S c) (t2 : TensorTree S c1) :
    (prod t1 (smul a t2)).tensor = (smul a (prod t1 t2)).tensor := by
  simp [prod_tensor, smul_tensor, tmul_smul, smul_tmul, map_smul]

/-- When a `prod` node acts on an `add` node in both the LHS and RHS entries,
  it can be moved through both `add` nodes. -/
lemma prod_add_both {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t1 t2 : TensorTree S c) (t3 t4 : TensorTree S c1) :
    (prod (add t1 t2) (add t3 t4)).tensor = (add (add (prod t1 t3) (prod t1 t4))
    (add (prod t2 t3) (prod t2 t4))).tensor := by
  rw [add_prod]
  rw [add_tensor_eq_fst (prod_add _ _ _)]
  rw [add_tensor_eq_snd (prod_add _ _ _)]

/-!

## Nodes and the group action.

-/

/-- An `action` node can be moved through a `smul` node. -/
lemma smul_action {n : ℕ} {c : Fin n → S.C} (g : S.G) (a : S.k) (t : TensorTree S c) :
    (smul a (action g t)).tensor = (action g (smul a t)).tensor := by
  simp only [smul_tensor, action_tensor, map_smul]

/-- An `action` node can be moved through a `contr` node. -/
lemma contr_action {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ}
    {h : c (i.succAbove j) = S.τ (c i)} (g : S.G) (t : TensorTree S c) :
    (contr i j h (action g t)).tensor = (action g (contr i j h t)).tensor := by
  simp only [Nat.succ_eq_add_one, contr_tensor, action_tensor]
  change (ModuleCat.ofHom ((S.F.obj (OverColor.mk c)).ρ g) ≫ (S.contrMap c i j h).hom) t.tensor = _
  erw [(S.contrMap c i j h).comm g]
  rfl

/-- An `action` node can be moved through a `prod` node when acting on both elements. -/
lemma prod_action {n n1 : ℕ} {c : Fin n → S.C} {c1 : Fin n1 → S.C} (g : S.G)
    (t : TensorTree S c) (t1 : TensorTree S c1) :
    (prod (action g t) (action g t1)).tensor = (action g (prod t t1)).tensor := by
  simp only [prod_tensor, action_tensor, map_tmul]
  change _ = ((S.F.map (equivToIso finSumFinEquiv).hom).hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm))).ρ g))
    (((Functor.LaxMonoidal.μ S.F (OverColor.mk c) (OverColor.mk c1)).hom
    (t.tensor ⊗ₜ[S.k] t1.tensor)))
  erw [← (S.F.map (equivToIso finSumFinEquiv).hom).comm g]
  simp only [Action.forget_obj, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, Function.comp_apply]
  change _ = (S.F.map (equivToIso finSumFinEquiv).hom).hom
    (((Functor.LaxMonoidal.μ S.F (OverColor.mk c) (OverColor.mk c1)).hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk (Sum.elim c c1))).ρ g)) (t.tensor ⊗ₜ[S.k] t1.tensor))
  erw [← (Functor.LaxMonoidal.μ S.F (OverColor.mk c) (OverColor.mk c1)).comm g]
  rfl

/-- An `action` node can be moved through a `add` node when acting on both elements. -/
lemma add_action {n : ℕ} {c : Fin n → S.C} (g : S.G) (t t1 : TensorTree S c) :
    (add (action g t) (action g t1)).tensor = (action g (add t t1)).tensor := by
  simp only [add_tensor, action_tensor, map_add]

/-- An `action` node can be moved through a `perm` node. -/
lemma perm_action {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (g : S.G) (t : TensorTree S c) :
    (perm σ (action g t)).tensor = (action g (perm σ t)).tensor := by
  simp only [perm_tensor, action_tensor]
  change (ModuleCat.ofHom ((S.F.obj (OverColor.mk c)).ρ g) ≫ (S.F.map σ).hom) t.tensor = _
  erw [(S.F.map σ).comm g]
  rfl

/-- An `action` node can be moved through a `neg` node. -/
lemma neg_action {n : ℕ} {c : Fin n → S.C} (g : S.G) (t : TensorTree S c) :
    (neg (action g t)).tensor = (action g (neg t)).tensor := by
  simp only [neg_tensor, action_tensor, map_neg]

/-- Two `action` nodes can be combined into a single `action` node. -/
lemma action_action {n : ℕ} {c : Fin n → S.C} (g h : S.G) (t : TensorTree S c) :
    (action g (action h t)).tensor = (action (g * h) t).tensor := by
  simp only [action_tensor, map_mul, LinearMap.mul_apply]

/-- The `action` node for the identity leaves the tensor invariant. -/
lemma action_id {n : ℕ} {c : Fin n → S.C} (t : TensorTree S c) :
    (action 1 t).tensor = t.tensor := by
  simp only [action_tensor, map_one, LinearMap.one_apply]

/-- An `action` node on a `constTwoNode` leaves the tensor invariant. -/
lemma action_constTwoNode {c1 c2 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2))
    (g : S.G) : (action g (constTwoNode v)).tensor = (constTwoNode v).tensor := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, action_tensor, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  change ((Discrete.pairIsoSep S.FD).hom.hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk ![c1, c2])).ρ g)) (v.hom _) = _
  erw [← (Discrete.pairIsoSep S.FD).hom.comm g]
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 }).ρ g)) ≫
    (Discrete.pairIsoSep S.FD).hom.hom) _ = _
  erw [← v.comm g]
  simp
  rfl

/-- An `action` node on a `constThreeNode` leaves the tensor invariant. -/
lemma action_constThreeNode {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep S.k S.G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
      S.FD.obj (Discrete.mk c3))
    (g : S.G) : (action g (constThreeNode v)).tensor = (constThreeNode v).tensor := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, action_tensor, constThreeNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  change ((Discrete.tripleIsoSep S.FD).hom.hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk ![c1, c2, c3])).ρ g)) (v.hom _) = _
  erw [← (Discrete.tripleIsoSep S.FD).hom.comm g]
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 } ⊗
    S.FD.obj { as := c3 }).ρ g)) ≫ (Discrete.tripleIsoSep S.FD).hom.hom) _ = _
  erw [← v.comm g]
  simp
  rfl

end TensorTree
