/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.PureU1.Permutations
/-!
# The Pure U(1) case with 2 fermions

We define an equivalence between `LinSols` and `Sols`.
-/

universe v u

open Nat
open  Finset

namespace PureU1

variable {n : ℕ}

namespace Two

/-- An equivalence between `LinSols` and `Sols`. -/
def equiv : (PureU1 2).LinSols ≃ (PureU1 2).Sols where
  toFun S := ⟨⟨S, by intro i; simp at i; exact Fin.elim0 i⟩, by
    have hLin := pureU1_linear S
    simp at hLin
    erw [accCube_explicit]
    simp only [Fin.sum_univ_two, Fin.isValue]
    rw [show S.val (0 : Fin 2) = - S.val (1 : Fin 2) by linear_combination hLin]
    ring⟩
  invFun S := S.1.1
  left_inv S := rfl
  right_inv S := rfl

end Two

end PureU1
