/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Tensors.TensorSpecies.Basis
/-!

# Basis for tensors in a tensor species

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable (S : TensorSpecies)

/-- A tensor from a `(Π j, Fin (S.repDim (c j))) → ℤ`. All tensors
  which have integer coefficents with respect to `tensorBasis` are of this form. -/
noncomputable def tensorOfInt {n : ℕ} {c : Fin n → S.C}
    (f : (Π j, Fin (S.repDim (c j))) → ℤ) :
    S.F.obj (OverColor.mk c) :=
  (S.tensorBasis c).repr.symm <|
  (Finsupp.linearEquivFunOnFinite S.k S.k ((j : Fin n) → Fin (S.repDim (c j)))).symm <|
  (fun j => Int.cast (f j))

@[simp]
lemma tensorOfInt_tensorBasis_repr_apply {n : ℕ} {c : Fin n → S.C}
    (f : (Π j, Fin (S.repDim (c j))) → ℤ) (b : Π j, Fin (S.repDim (c j))) :
  (S.tensorBasis c).repr (S.tensorOfInt f) b = Int.cast (f b) := by
  simp [tensorOfInt]
  rfl

lemma tensorBasis_eq_ofInt {n : ℕ} {c : Fin n → S.C}
    (b : Π j, Fin (S.repDim (c j))) :
    S.tensorBasis c b
    = S.tensorOfInt (fun b' => if b = b' then 1 else 0) := by
  apply (S.tensorBasis c).repr.injective
  simp only [Basis.repr_self]
  ext b'
  simp only [tensorOfInt_tensorBasis_repr_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rw [Finsupp.single_apply]

end TensorSpecies
