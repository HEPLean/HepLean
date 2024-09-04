/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Basic
import HepLean.SpaceTime.LorentzGroup.Basic
import Mathlib.RepresentationTheory.Basic
/-!

# Lorentz group action on Lorentz vectors.

-/
noncomputable section

namespace LorentzVector

variable {d : ℕ} (v : LorentzVector d)

/-- The contravariant action of the Lorentz group on a Lorentz vector. -/
def rep : Representation ℝ (LorentzGroup d) (LorentzVector d) where
  toFun g := Matrix.toLinAlgEquiv e g
  map_one' := (MulEquivClass.map_eq_one_iff (Matrix.toLinAlgEquiv e)).mpr rfl
  map_mul' x y := by
    simp only [lorentzGroupIsGroup_mul_coe, map_mul]

open Matrix in
lemma rep_apply (g : LorentzGroup d) : rep g v = g *ᵥ v := rfl

lemma rep_apply_stdBasis (g : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    rep g (stdBasis μ) = ∑ ν, g.1.transpose μ ν • stdBasis ν := by
  simp only [rep_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, decomp_stdBasis']
  funext ν
  simp [LorentzVector.stdBasis, Pi.basisFun_apply]
  erw [Pi.basisFun_apply, Matrix.mulVec_single_one]
  rfl

end LorentzVector

end
