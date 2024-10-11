/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
import HepLean.Mathematics.PiTensorProduct
/-!

## Complex Lorentz tensors

-/

namespace Fermion

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open MonoidalCategory

/-- The colors associated with complex representations of SL(2, ℂ) of intrest to physics. -/
inductive Color
  | upL : Color
  | downL : Color
  | upR : Color
  | downR : Color
  | up : Color
  | down : Color

def τ : Color → Color
  | Color.upL => Color.downL
  | Color.downL => Color.upL
  | Color.upR => Color.downR
  | Color.downR => Color.upR
  | Color.up => Color.down
  | Color.down => Color.up

def evalNo : Color → ℕ
  | Color.upL => 2
  | Color.downL => 2
  | Color.upR => 2
  | Color.downR => 2
  | Color.up => 4
  | Color.down => 4

noncomputable section
/-- The corresponding representations associated with a color. -/
def colorToRep (c : Color) : Rep ℂ SL(2, ℂ) :=
  match c with
  | Color.upL => Fermion.altLeftHanded
  | Color.downL => Fermion.leftHanded
  | Color.upR => Fermion.altRightHanded
  | Color.downR => Fermion.rightHanded
  | Color.up => Lorentz.complexContr
  | Color.down => Lorentz.complexCo

end
end Fermion
