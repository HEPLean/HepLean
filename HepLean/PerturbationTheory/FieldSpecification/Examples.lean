/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.Basic
/-!

# Specific examples of field specifications

-/

namespace FieldSpecification
variable (𝓕 : FieldSpecification)

/-- The Field specification corresponding to a single bosonic field. -/
def singleBoson : FieldSpecification where
  Fields := Unit
  statistics := fun _ => FieldStatistic.bosonic

/-- The Field specification corresponding to a single fermionic field. -/
def singleFermion : FieldSpecification where
  Fields := Unit
  statistics := fun _ => FieldStatistic.fermionic

/-- The Field specification corresponding to a two bosonic field and
  two fermionic fields. -/
def doubleBosonDoubleFermion : FieldSpecification where
  Fields := Fin 2 ⊕ Fin 2
  statistics := fun b =>
    match b with
    | Sum.inl _ => FieldStatistic.bosonic
    | Sum.inr _ => FieldStatistic.fermionic

end FieldSpecification
