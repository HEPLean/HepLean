/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
import HepLean.Tensors.OverColor.Lift
import HepLean.Mathematics.PiTensorProduct
import HepLean.Tensors.OverColor.Iso
/-!

# Discrete color category

-/

namespace IndexNotation
namespace OverColor
namespace Discrete

open CategoryTheory
open MonoidalCategory
open TensorProduct
variable {C k : Type} [CommRing k] {G : Type} [Group G]

variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')
noncomputable section

def pair : Discrete C ⥤ Rep k G := F ⊗ F

def pairIso (c : C) : (pair F).obj (Discrete.mk c) ≅
    (lift.obj F).obj (OverColor.mk ![c,c]) := by
  symm
  apply ((lift.obj F).mapIso fin2Iso).trans
  apply ((lift.obj F).μIso _ _).symm.trans
  apply tensorIso ?_ ?_
  · symm
    apply (forgetLiftApp F c).symm.trans
    refine (lift.obj F).mapIso (mkIso ?_)
    funext x
    fin_cases x
    rfl
  · symm
    apply (forgetLiftApp F c).symm.trans
    refine (lift.obj F).mapIso (mkIso ?_)
    funext x
    fin_cases x
    rfl


def pairτ (τ : C → C) : Discrete C ⥤ Rep k G :=
  F ⊗ ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤  Discrete C) ⋙ F)

def τPair (τ : C → C) : Discrete C ⥤ Rep k G :=
  ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤  Discrete C) ⋙ F) ⊗ F

end
end Discrete
end OverColor
end IndexNotation
