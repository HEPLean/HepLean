/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Informal
/-!

# Weyl fermions

-/

/-!

## The definition of Weyl fermion vector spaces.

-/

informal_definition leftHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the fundamental representation of SL(2,C)."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition rightHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the conjguate representation of SL(2,C)."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition altLeftHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition altRightHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

/-!

## Equivalences between Weyl fermion vector spaces.

-/

informal_definition leftHandedWeylFermionAltEquiv where
  math :≈ "The linear equiv between leftHandedWeylFermion and altLeftHandedWeylFermion given
    by multiplying an element of rightHandedWeylFermion by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`."
  deps :≈ [`leftHandedWeylFermion, `altLeftHandedWeylFermion]

informal_lemma leftHandedWeylFermionAltEquiv_equivariant where
  math :≈ "The linear equiv leftHandedWeylFermionAltEquiv is equivariant with respect to the
    action of SL(2,C) on leftHandedWeylFermion and altLeftHandedWeylFermion."
  deps :≈ [`leftHandedWeylFermionAltEquiv]

informal_definition rightHandedWeylFermionAltEquiv where
  math :≈ "The linear equiv between rightHandedWeylFermion and altRightHandedWeylFermion given
    by multiplying an element of rightHandedWeylFermion by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`"
  deps :≈ [`rightHandedWeylFermion, `altRightHandedWeylFermion]

informal_lemma rightHandedWeylFermionAltEquiv_equivariant where
  math :≈ "The linear equiv rightHandedWeylFermionAltEquiv is equivariant with respect to the
    action of SL(2,C) on rightHandedWeylFermion and altRightHandedWeylFermion."
  deps :≈ [`rightHandedWeylFermionAltEquiv]
