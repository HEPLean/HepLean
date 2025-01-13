/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Fintype.Basic
/-!

# Creation and annihilation parts of fields

-/

/-- The type specifying whether an operator is a creation or annihilation operator. -/
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

/-- The normal ordering on creation and annihilation operators.
  Creation operators are put to the left. -/
def normalOrder : CreateAnnihilate → CreateAnnihilate → Prop
  | create, create => True
  | annihilate, annihilate => True
  | create, annihilate => True
  | annihilate, create => False

/-- Normal ordering is total. -/
instance : IsTotal CreateAnnihilate normalOrder where
  total a b := by
    cases a <;> cases b <;> simp [normalOrder]

/-- Normal ordering is transitive. -/
instance : IsTrans CreateAnnihilate normalOrder where
  trans a b c := by
    cases a <;> cases b <;> cases c <;> simp [normalOrder]

end CreateAnnihilate
