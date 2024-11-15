/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.Basic
/-!

# Isomorphism between rep of color `c` and rep of dual color.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

noncomputable section

namespace TensorSpecies
variable (S : TensorSpecies)

/-- The morphism from `S.FD.obj (Discrete.mk c)` to `S.FD.obj (Discrete.mk (S.τ c))`
  defined by contracting with the metric. -/
def toDualRep (c : S.C) : S.FD.obj (Discrete.mk c) ⟶ S.FD.obj (Discrete.mk (S.τ c)) :=
  (ρ_ (S.FD.obj (Discrete.mk c))).inv
  ≫ (S.FD.obj { as := c } ◁ (S.metric.app (Discrete.mk (S.τ c))))
  ≫ (α_ (S.FD.obj (Discrete.mk c)) (S.FD.obj (Discrete.mk (S.τ c)))
    (S.FD.obj (Discrete.mk (S.τ c)))).inv
  ≫ (S.contr.app (Discrete.mk c) ▷ S.FD.obj { as := S.τ c })
  ≫ (λ_ (S.FD.obj (Discrete.mk (S.τ c)))).hom

/-- The `toDualRep` for equal colors is the same, up-to conjugation by a trivial equivalence. -/
lemma toDualRep_congr {c c' : S.C} (h : c = c') : S.toDualRep c = S.FD.map (Discrete.eqToHom h) ≫
    S.toDualRep c' ≫ S.FD.map (Discrete.eqToHom (congrArg S.τ h.symm)) := by
  subst h
  simp only [eqToHom_refl, Discrete.functor_map_id, Category.comp_id, Category.id_comp]

/-- The morphism from `S.FD.obj (Discrete.mk (S.τ c))` to `S.FD.obj (Discrete.mk c)`
  defined by contracting with the metric. -/
def fromDualRep (c : S.C) : S.FD.obj (Discrete.mk (S.τ c)) ⟶ S.FD.obj (Discrete.mk c) :=
  S.toDualRep (S.τ c) ≫ S.FD.map (Discrete.eqToHom (S.τ_involution c))

end TensorSpecies

end
