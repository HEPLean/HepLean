/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.StaticWickTerm
/-!

# Static Wick's theorem

-/



namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra

open HepLean.List
open WickContraction
open FieldStatistic
namespace FieldOpAlgebra

/--
The static Wicks theorem states that
`φ₀…φₙ` is equal to
`∑ φsΛ, φsΛ.1.sign • φsΛ.1.staticContract * 𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)`
over all Wick contraction `φsΛ`.
This is compared to the ordinary Wicks theorem in which `staticContract` is replaced with
`timeContract`.

The proof is via induction on `φs`. The base case `φs = []` is handled by `static_wick_theorem_nil`.
The inductive step works as follows:
- The proof considers `φ₀…φₙ` as `φ₀(φ₁…φₙ)` and use the induction hypothesis on `φ₁…φₙ`.
- It also uses `ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum`
-/
theorem static_wick_theorem : (φs : List 𝓕.FieldOp) →
    ofFieldOpList φs = ∑ (φsΛ : WickContraction φs.length), φsΛ.staticWickTerm
  | [] => by
    simp only [ofFieldOpList, ofFieldOpListF_nil, map_one, List.length_nil]
    rw [sum_WickContraction_nil]
    simp
  | φ :: φs => by
    rw [ofFieldOpList_cons, static_wick_theorem φs]
    rw [show (φ :: φs) = φs.insertIdx (⟨0, Nat.zero_lt_succ φs.length⟩ : Fin φs.length.succ) φ
      from rfl]
    conv_rhs => rw [insertLift_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_staticWickTerm_eq_sum]
    rfl

end FieldOpAlgebra
end FieldSpecification
