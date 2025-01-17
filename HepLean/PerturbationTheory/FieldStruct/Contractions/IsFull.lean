/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Contractions.Involutions
import HepLean.PerturbationTheory.FieldStruct.TimeOrder
import HepLean.PerturbationTheory.FieldStruct.TimeContraction
import HepLean.PerturbationTheory.FieldStruct.Contractions
import HepLean.Mathematics.Fin.Involutions
/-!

# Full contraction

We say that a contraction is full if it has no uncontracted fields.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}
namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List
open FieldStatistic

/-- A contraction is full if there are no uncontracted fields, i.e. the finite set
  of uncontracted fields is empty. -/
def IsFull : Prop := c.uncontracted = ∅

/-- The condition on whether or not a contraction is full is decidable. -/
instance : Decidable (IsFull c) := decEq c.uncontracted ∅

lemma isFull_iff_equivInvolution_no_fixed_point :
    IsFull c ↔ ∀ (i : Fin n), (equivInvolution c).1 i ≠ i := by
  simp [IsFull]
  rw [Finset.eq_empty_iff_forall_not_mem]
  simp [equivInvolution, toInvolution, uncontracted]

def isFullInvolutionEquiv : {c : ContractionsNat n // IsFull c} ≃
    {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} where
  toFun c := ⟨equivInvolution c.1, by
    apply And.intro (equivInvolution c.1).2
    rw [← isFull_iff_equivInvolution_no_fixed_point]
    exact c.2⟩
  invFun f := ⟨equivInvolution.symm ⟨f.1, f.2.1⟩, by
    rw [isFull_iff_equivInvolution_no_fixed_point]
    simpa using f.2.2⟩
  left_inv c := by simp
  right_inv f := by simp

open Nat

theorem card_of_isfull_even (he : Even n) :
    Fintype.card {c : ContractionsNat n // IsFull c} = (n - 1)‼ := by
  rw [Fintype.card_congr (isFullInvolutionEquiv)]
  exact HepLean.Fin.involutionNoFixed_card_even n he

theorem card_of_isfull_odd (ho : Odd n) :
    Fintype.card  {c : ContractionsNat n // IsFull c} = 0 := by
  rw [Fintype.card_congr (isFullInvolutionEquiv)]
  exact HepLean.Fin.involutionNoFixed_card_odd n ho

end ContractionsNat

end FieldStruct
