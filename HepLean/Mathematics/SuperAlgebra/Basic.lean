/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.RingTheory.GradedAlgebra.Basic
import HepLean.Meta.Informal
/-!

# Super Algebras

A super algebra is a special type of graded algebra.

It is used in physics to model the commutator of fermionic operators among themselves,
aswell as among bosonic operators.

-/

informal_definition SuperAlgebra where
  math :≈ "A super algebra is a graded algebra A with a ℤ₂ grading."
  physics :≈ "A super algebra is used to model the commutator of fermionic operators among
    themselves, aswell as among bosonic operators."
  ref :≈ "https://en.wikipedia.org/wiki/Superalgebra"

namespace SuperAlgebra

informal_definition superCommuator where
  math :≈ "The commutator which for `a ∈ Aᵢ` and `b ∈ Aⱼ` is defined as `ab - (-1)^(i * j) ba`."
  deps :≈ [``SuperAlgebra]

end SuperAlgebra
