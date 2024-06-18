/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Category.ModuleCat.Basic
/-!
# Momentum in Feynman diagrams

The aim of this file is to associate with each half-edge of a Feynman diagram a momentum,
and constrain the momentums based conservation at each vertex and edge.

-/

namespace FeynmanDiagram

open CategoryTheory
open PreFeynmanRule

variable {P : PreFeynmanRule} (F : FeynmanDiagram P)
variable (d : ℕ)

/-- The momentum space for a `d`-dimensional field theory for a single particle.
  TODO: Move this definition, and define it as a four-vector. -/
def SingleMomentumSpace : Type :=  Fin d → ℝ

instance : AddCommGroup (SingleMomentumSpace d) := Pi.addCommGroup

noncomputable instance : Module ℝ (SingleMomentumSpace d) := Pi.module _ _ _

/-- The type which asociates to each half-edge a `d`-dimensional vector.
 This is to be interpreted as the momentum associated to that half-edge flowing from the
 corresponding `edge` to the corresponding `vertex`. So all momentums flow into vertices. -/
def FullMomentumSpace : Type := F.𝓱𝓔 → Fin d → ℝ

instance : AddCommGroup (F.FullMomentumSpace d) := Pi.addCommGroup

noncomputable instance : Module ℝ (F.FullMomentumSpace d) := Pi.module _ _ _

/-- The linear map taking a half-edge to its momentum.
 (defined as flowing from the `edge` to the vertex.) -/
def toHalfEdgeMomentum (i : F.𝓱𝓔) : F.FullMomentumSpace d →ₗ[ℝ] SingleMomentumSpace d where
  toFun x := x i
  map_add' x y := by rfl
  map_smul' c x := by rfl

namespace Hom

variable {F G : FeynmanDiagram P}
variable (f : F ⟶ G)

/-- The linear map induced by a morphism of Feynman diagrams. -/
def toLinearMap : G.FullMomentumSpace d →ₗ[ℝ] F.FullMomentumSpace d where
  toFun x := x ∘ f.𝓱𝓔
  map_add' x y := by rfl
  map_smul' c x := by rfl


end Hom

/-- The contravariant functor from Feynman diagrams to Modules over `ℝ`.  -/
noncomputable def funcFullMomentumSpace : FeynmanDiagram P ⥤ (ModuleCat ℝ)ᵒᵖ where
  obj F := Opposite.op $ ModuleCat.of ℝ (F.FullMomentumSpace d)
  map f := Opposite.op $ Hom.toLinearMap d f


/-!
## Edge constraints

-/
end FeynmanDiagram
