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
  map_one' := by
    simp only [lorentzGroupIsGroup_one_coe, map_one]
  map_mul' x y := by
    simp only [lorentzGroupIsGroup_mul_coe, map_mul]

open Matrix in
lemma rep_apply (g : LorentzGroup d) : rep g v = g *ᵥ v := rfl

end LorentzVector

end
