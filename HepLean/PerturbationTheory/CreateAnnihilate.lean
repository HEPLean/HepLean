/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.BigOperators.Group.Finset
/-!

# Creation and annihlation parts of fields

-/

/-- The type specifing whether an operator is a creation or annihilation operator. -/
inductive CreateAnnihilate where
  | create : CreateAnnihilate
  | annihilate : CreateAnnihilate
deriving Inhabited, BEq, DecidableEq

namespace CreateAnnihilate

/-- The type `CreateAnnihilate` is finite. -/
instance : Fintype CreateAnnihilate where
  elems := {create, annihilate}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self create {annihilate}
    · refine Finset.insert_eq_self.mp ?_
      exact rfl

lemma eq_create_or_annihilate (φ : CreateAnnihilate) : φ = create ∨ φ = annihilate := by
  cases φ <;> simp

/-- The normal ordering on creation and annihlation operators.
  Under this relation, `normalOrder a b` is false only if `a` is annihlate and `b` is create.  -/
def normalOrder : CreateAnnihilate → CreateAnnihilate → Prop
  | create, _ => True
  | annihilate, annihilate => True
  | annihilate, create => False

/-- The normal ordering on `CreateAnnihilate` is decidable. -/
instance : (φ φ' : CreateAnnihilate) → Decidable (normalOrder φ φ')
  | create, create => isTrue True.intro
  | annihilate, annihilate => isTrue True.intro
  | create, annihilate => isTrue True.intro
  | annihilate, create => isFalse False.elim

/-- Normal ordering is total. -/
instance : IsTotal CreateAnnihilate normalOrder where
  total a b := by
    cases a <;> cases b <;> simp [normalOrder]

/-- Normal ordering is transitive. -/
instance : IsTrans CreateAnnihilate normalOrder where
  trans a b c := by
    cases a <;> cases b <;> cases c <;> simp [normalOrder]

@[simp]
lemma not_normalOrder_annihilate_iff_false (a : CreateAnnihilate) :
    (¬ normalOrder a annihilate) ↔ False := by
  cases a
  · simp [normalOrder]
  · simp [normalOrder]

lemma sum_eq {M : Type} [AddCommMonoid M] (f : CreateAnnihilate → M) :
    ∑ i, f i = f create + f annihilate := by
  change ∑ i in {create, annihilate}, f i = f create + f annihilate
  simp

end CreateAnnihilate
