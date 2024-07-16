/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import HepLean.SpaceTime.LorentzTensor.Real.LorentzAction
/-!

# Constructors for real Lorentz tensors

In this file we will constructors of real Lorentz tensors from real numbers,
vectors and matrices.

We will derive properties of these constructors.

-/

namespace RealLorentzTensor

/-!

# Tensors from reals, vectors and matrices

Note that that these definitions are not equivariant with respect to an
action of the Lorentz group. They are provided for constructive purposes.

-/

/-- A 0-tensor from a real number. -/
def ofReal (d : ℕ) (r : ℝ) : RealLorentzTensor d Empty where
  color := fun _ => Colors.up
  coord := fun _ => r

/-- A marked 1-tensor with a single up index constructed from a vector.

  Note: This is not the same as rising indices on `ofVecDown`. -/
def ofVecUp {d : ℕ} (v : Fin 1 ⊕ Fin d → ℝ) :
    Marked d Empty 1 where
  color := fun _ => Colors.up
  coord := fun i => v <| i <| Sum.inr <| ⟨0, PUnit.unit⟩

/-- A marked 1-tensor with a single down index constructed from a vector.

  Note: This is not the same as lowering indices on `ofVecUp`. -/
def ofVecDown {d : ℕ} (v : Fin 1 ⊕ Fin d → ℝ) :
    Marked d Empty 1 where
  color := fun _ => Colors.down
  coord := fun i => v <| i <| Sum.inr <| ⟨0, PUnit.unit⟩

/-- A tensor with two up indices constructed from a matrix.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
def ofMatUpUp {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d Empty 2 where
  color := fun _ => Colors.up
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- A tensor with two down indices constructed from a matrix.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
def ofMatDownDown {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d Empty 2 where
  color := fun _ => Colors.down
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- A marked 2-tensor with the first index up and the second index down.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
@[simps!]
def ofMatUpDown {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d Empty 2 where
  color := fun i => match i with
  | Sum.inr ⟨0, PUnit.unit⟩ => Colors.up
  | Sum.inr ⟨1, PUnit.unit⟩ => Colors.down
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-- A marked 2-tensor with the first index down and the second index up.

Note: This is not the same as rising or lowering indices on other `ofMat...`. -/
def ofMatDownUp {d : ℕ} (m : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Marked d Empty 2 where
  color := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => Colors.down
    | Sum.inr ⟨1, PUnit.unit⟩ => Colors.up
  coord := fun i => m (i (Sum.inr ⟨0, PUnit.unit⟩)) (i (Sum.inr ⟨1, PUnit.unit⟩))

/-!

## Equivalence of `IndexValue` for constructors

-/

/-- Index values for `ofVecUp v` are equivalent to elements of `Fin 1 ⊕ Fin d`. -/
def ofVecUpIndexValue (v : Fin 1 ⊕ Fin d → ℝ) :
    IndexValue d (ofVecUp v).color ≃ (Fin 1 ⊕ Fin d) where
  toFun i := i (Sum.inr ⟨0, PUnit.unit⟩)
  invFun x := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => x
  left_inv i := by
    funext y
    match y with
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
  right_inv x := rfl

/-- Index values for `ofVecDown v` are equivalent to elements of `Fin 1 ⊕ Fin d`. -/
def ofVecDownIndexValue (v : Fin 1 ⊕ Fin d → ℝ) :
    IndexValue d (ofVecDown v).color ≃ (Fin 1 ⊕ Fin d) where
  toFun i := i (Sum.inr ⟨0, PUnit.unit⟩)
  invFun x := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => x
  left_inv i := by
    funext y
    match y with
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
  right_inv x := rfl

/-- Index values for `ofMatUpUp v` are equivalent to elements of
  `(Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)`. -/
def ofMatUpUpIndexValue (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    IndexValue d (ofMatUpUp M).color ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) where
  toFun i := (i (Sum.inr ⟨0, PUnit.unit⟩), i (Sum.inr ⟨1, PUnit.unit⟩))
  invFun x := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => x.1
    | Sum.inr ⟨1, PUnit.unit⟩ => x.2
  left_inv i := by
    funext y
    match y with
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
    | Sum.inr ⟨1, PUnit.unit⟩ => rfl
  right_inv x := rfl

/-- Index values for `ofMatDownDown v` are equivalent to elements of
  `(Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)`. -/
def ofMatDownDownIndexValue (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    IndexValue d (ofMatDownDown M).color ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) where
  toFun i := (i (Sum.inr ⟨0, PUnit.unit⟩), i (Sum.inr ⟨1, PUnit.unit⟩))
  invFun x := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => x.1
    | Sum.inr ⟨1, PUnit.unit⟩ => x.2
  left_inv i := by
    funext y
    match y with
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
    | Sum.inr ⟨1, PUnit.unit⟩ => rfl
  right_inv x := rfl

/-- Index values for `ofMatUpDown v` are equivalent to elements of
  `(Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)`. -/
def ofMatUpDownIndexValue (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    IndexValue d (ofMatUpDown M).color ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) where
  toFun i := (i (Sum.inr ⟨0, PUnit.unit⟩), i (Sum.inr ⟨1, PUnit.unit⟩))
  invFun x := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => x.1
    | Sum.inr ⟨1, PUnit.unit⟩ => x.2
  left_inv i := by
    funext y
    match y with
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
    | Sum.inr ⟨1, PUnit.unit⟩ => rfl
  right_inv x := rfl

/-- Index values for `ofMatDownUp v` are equivalent to elements of
  `(Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)`. -/
def ofMatDownUpIndexValue (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    IndexValue d (ofMatDownUp M).color ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) where
  toFun i := (i (Sum.inr ⟨0, PUnit.unit⟩), i (Sum.inr ⟨1, PUnit.unit⟩))
  invFun x := fun i => match i with
    | Sum.inr ⟨0, PUnit.unit⟩ => x.1
    | Sum.inr ⟨1, PUnit.unit⟩ => x.2
  left_inv i := by
    funext y
    match y with
    | Sum.inr ⟨0, PUnit.unit⟩ => rfl
    | Sum.inr ⟨1, PUnit.unit⟩ => rfl
  right_inv x := rfl

/-!

## Contraction of indices of tensors from matrices

-/
open Matrix
open Marked

/-- Contracting the indices of `ofMatUpDown` returns the trace of the matrix. -/
lemma contr_ofMatUpDown_eq_trace {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contr (ofMatUpDown M) (by rfl) = ofReal d M.trace := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    simp only [Fin.isValue, contr, IndexValue, Equiv.cast_apply, trace, diag_apply, ofReal,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    apply Finset.sum_congr rfl
    intro x _
    rfl

/-- Contracting the indices of `ofMatDownUp` returns the trace of the matrix. -/
lemma contr_ofMatDownUp_eq_trace {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contr (ofMatDownUp M) (by rfl) = ofReal d M.trace := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    rfl

/-!

## Multiplication of tensors from vectors and matrices

-/

/-- Multiplying `ofVecUp` with `ofVecDown` gives the dot product. -/
@[simp]
lemma mul_ofVecUp_ofVecDown_eq_dot_prod {d : ℕ} (v₁ v₂ : Fin 1 ⊕ Fin d → ℝ) :
    congrSet (@Equiv.equivEmpty (Empty ⊕ Empty) instIsEmptySum)
    (mul (ofVecUp v₁) (ofVecDown v₂) (by rfl)) = ofReal d (v₁ ⬝ᵥ v₂) := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    rfl

/-- Multiplying `ofVecDown` with `ofVecUp` gives the dot product. -/
@[simp]
lemma mul_ofVecDown_ofVecUp_eq_dot_prod {d : ℕ} (v₁ v₂ : Fin 1 ⊕ Fin d → ℝ) :
    congrSet (Equiv.equivEmpty (Empty ⊕ Empty))
    (mul (ofVecDown v₁) (ofVecUp v₂) rfl) = ofReal d (v₁ ⬝ᵥ v₂) := by
  refine ext' ?_ ?_
  · funext i
    exact Empty.elim i
  · funext i
    rfl

lemma mul_ofMatUpDown_ofVecUp_eq_mulVec {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (v : Fin 1 ⊕ Fin d → ℝ) :
    congrSet ((Equiv.sumEmpty (Empty ⊕ PUnit.{1}) Empty).trans equivPUnitToSigma)
    (mul (unmarkFirst $ ofMatUpDown M) (ofVecUp v) rfl) = ofVecUp (M *ᵥ v) := by
  refine ext' ?_ ?_
  · funext i
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, congrSet_apply_color, mul_color, Equiv.symm_symm]
    fin_cases i
    rfl
  · funext i
    rfl

lemma mul_ofMatDownUp_ofVecDown_eq_mulVec {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (v : Fin 1 ⊕ Fin d → ℝ) :
    congrSet ((Equiv.sumEmpty (Empty ⊕ PUnit.{1}) Empty).trans equivPUnitToSigma)
    (mul (unmarkFirst $ ofMatDownUp M) (ofVecDown v) rfl) = ofVecDown (M *ᵥ v) := by
  refine ext' ?_ ?_
  · funext i
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, congrSet_apply_color, mul_color, Equiv.symm_symm]
    fin_cases i
    rfl
  · funext i
    rfl

/-!

## The Lorentz action on constructors

-/
section lorentzAction
variable {d : ℕ} {X : Type} [Fintype X] [DecidableEq X] (T : RealLorentzTensor d X) (c : X → Colors)
variable (Λ Λ' : LorentzGroup d)

open Matrix

/-- The action of the Lorentz group on `ofReal v` is trivial. -/
@[simp]
lemma lorentzAction_ofReal (r : ℝ) : Λ • ofReal d r = ofReal d r := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton, IndexValue]
  rfl

/-- The action of the Lorentz group on `ofVecUp v` is by vector multiplication. -/
@[simp]
lemma lorentzAction_ofVecUp (v : Fin 1 ⊕ Fin d → ℝ) :
    Λ • ofVecUp v = ofVecUp (Λ *ᵥ v) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  simp only [ofVecUp, IndexValue, Fin.isValue, Fintype.prod_sum_type, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul]
  rw [mulVec]
  simp only [Fin.isValue, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  erw [Finset.sum_equiv (ofVecUpIndexValue v)]
  intro i
  simp_all only [Finset.mem_univ, Fin.isValue, Equiv.coe_fn_mk]
  intro j _
  erw [Finset.prod_singleton]
  rfl

/-- The action of the Lorentz group on `ofVecDown v` is
  by vector multiplication of the transpose-inverse. -/
@[simp]
lemma lorentzAction_ofVecDown (v : Fin 1 ⊕ Fin d → ℝ) :
    Λ • ofVecDown v = ofVecDown ((LorentzGroup.transpose Λ⁻¹) *ᵥ v) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  simp only [ofVecDown, IndexValue, Fin.isValue, Fintype.prod_sum_type, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, lorentzGroupIsGroup_inv]
  rw [mulVec]
  simp only [Fin.isValue, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  erw [Finset.sum_equiv (ofVecUpIndexValue v)]
  intro i
  simp_all only [Finset.mem_univ, Fin.isValue, Equiv.coe_fn_mk]
  intro j _
  erw [Finset.prod_singleton]
  rfl

@[simp]
lemma lorentzAction_ofMatUpUp (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Λ • ofMatUpUp M = ofMatUpUp (Λ.1 * M * (LorentzGroup.transpose Λ).1) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  erw [← Equiv.sum_comp (ofMatUpUpIndexValue M).symm]
  simp only [ofMatUpUp, IndexValue, Fin.isValue, Fintype.prod_sum_type, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, mul_apply]
  erw [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  erw [← Equiv.prod_comp (Equiv.sigmaPUnit (Fin 2)).symm]
  rw [Fin.prod_univ_two]
  simp only [colorMatrix, Fin.isValue, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, mul_comm _ (M _ _), ← mul_assoc]
  congr

@[simp]
lemma lorentzAction_ofMatDownDown (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Λ • ofMatDownDown M = ofMatDownDown ((LorentzGroup.transpose Λ⁻¹).1 * M * (Λ⁻¹).1) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  erw [← Equiv.sum_comp (ofMatDownDownIndexValue M).symm]
  simp only [ofMatDownDown, IndexValue, Fin.isValue, Fintype.prod_sum_type, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, mul_apply]
  erw [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  erw [← Equiv.prod_comp (Equiv.sigmaPUnit (Fin 2)).symm]
  rw [Fin.prod_univ_two]
  simp only [colorMatrix, Fin.isValue, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, mul_comm _ (M _ _), ← mul_assoc]
  congr

@[simp]
lemma lorentzAction_ofMatUpDown (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Λ • ofMatUpDown M = ofMatUpDown (Λ.1 * M * (Λ⁻¹).1) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  erw [← Equiv.sum_comp (ofMatUpDownIndexValue M).symm]
  simp only [ofMatUpDown, IndexValue, Fin.isValue, Fintype.prod_sum_type, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, mul_apply]
  erw [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  erw [← Equiv.prod_comp (Equiv.sigmaPUnit (Fin 2)).symm]
  rw [Fin.prod_univ_two]
  simp only [colorMatrix, Fin.isValue, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, mul_comm _ (M _ _), ← mul_assoc]
  congr

@[simp]
lemma lorentzAction_ofMatDownUp (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Λ • ofMatDownUp M =
    ofMatDownUp ((LorentzGroup.transpose Λ⁻¹).1 * M * (LorentzGroup.transpose Λ).1) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  erw [← Equiv.sum_comp (ofMatDownUpIndexValue M).symm]
  simp only [ofMatDownUp, IndexValue, Fin.isValue, Fintype.prod_sum_type, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, mul_apply]
  erw [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  erw [← Equiv.prod_comp (Equiv.sigmaPUnit (Fin 2)).symm]
  rw [Fin.prod_univ_two]
  simp only [colorMatrix, Fin.isValue, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, mul_comm _ (M _ _), ← mul_assoc]
  congr

end lorentzAction

end RealLorentzTensor
