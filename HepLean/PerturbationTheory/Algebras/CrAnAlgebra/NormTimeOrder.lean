/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Norm-time Ordering in the CrAnAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace CrAnAlgebra

noncomputable section
open HepLean.List

/-!

## Norm-time order

-/

/-- The normal-time ordering on `CrAnAlgebra`. -/
def normTimeOrder : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  normTimeOrderSign φs • ofCrAnList (normTimeOrderList φs)

@[inherit_doc normTimeOrder]
scoped[FieldSpecification.CrAnAlgebra] notation "𝓣𝓝ᶠ(" a ")" => normTimeOrder a

lemma normTimeOrder_ofCrAnList (φs : List 𝓕.CrAnStates) :
    𝓣𝓝ᶠ(ofCrAnList φs) = normTimeOrderSign φs • ofCrAnList (normTimeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [normTimeOrder, Basis.constr_basis]

end

end CrAnAlgebra

end FieldSpecification
