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

We define the vector spaces corresponding to different types of Weyl fermions.

Note: We should prevent casting between these vector spaces.
-/

namespace Fermion

informal_definition leftHandedWeyl where
  math :≈ "The vector space ℂ^2 carrying the fundamental representation of SL(2,C)."
  physics :≈ "A Weyl fermion with indices ψ_a."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition rightHandedWeyl where
  math :≈ "The vector space ℂ^2 carrying the conjguate representation of SL(2,C)."
  physics :≈ "A Weyl fermion with indices ψ_{dot a}."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition altLeftHandedWeyl where
  math :≈ "The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ."
  physics :≈ "A Weyl fermion with indices ψ^a."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition altRightHandedWeyl where
  math :≈ "The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†."
  physics :≈ "A Weyl fermion with indices ψ^{dot a}."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

/-!

## Equivalences between Weyl fermion vector spaces.

-/

informal_definition leftHandedWeylAltEquiv where
  math :≈ "The linear equiv between leftHandedWeyl and altLeftHandedWeyl given
    by multiplying an element of rightHandedWeyl by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`."
  deps :≈ [``leftHandedWeyl, ``altLeftHandedWeyl]

informal_lemma leftHandedWeylAltEquiv_equivariant where
  math :≈ "The linear equiv leftHandedWeylAltEquiv is equivariant with respect to the
    action of SL(2,C) on leftHandedWeyl and altLeftHandedWeyl."
  deps :≈ [``leftHandedWeylAltEquiv]

informal_definition rightHandedWeylAltEquiv where
  math :≈ "The linear equiv between rightHandedWeyl and altRightHandedWeyl given
    by multiplying an element of rightHandedWeyl by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`"
  deps :≈ [``rightHandedWeyl, ``altRightHandedWeyl]

informal_lemma rightHandedWeylAltEquiv_equivariant where
  math :≈ "The linear equiv rightHandedWeylAltEquiv is equivariant with respect to the
    action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``rightHandedWeylAltEquiv]

/-!

## Contraction of Weyl fermions.

-/

informal_definition leftAltWeylContraction where
  math :≈ "The linear map from leftHandedWeyl ⊗ altLeftHandedWeyl to ℂ given by
    summing over components of leftHandedWeyl and altLeftHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a left-handed Weyl fermion with a right-handed Weyl fermion.
    In index notation this is ψ_a φ^a."
  deps :≈ [``leftHandedWeyl, ``altLeftHandedWeyl]

informal_lemma leftAltWeylContraction_invariant where
  math :≈ "The contraction leftAltWeylContraction is invariant with respect to
    the action of SL(2,C) on leftHandedWeyl and altLeftHandedWeyl."
  deps :≈ [``leftAltWeylContraction]

informal_definition altLeftWeylContraction where
  math :≈ "The linear map from altLeftHandedWeyl ⊗ leftHandedWeyl to ℂ given by
    summing over components of altLeftHandedWeyl and leftHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a left-handed Weyl fermion with a right-handed Weyl fermion.
    In index notation this is φ^a ψ_a ."
  deps :≈ [``leftHandedWeyl, ``altLeftHandedWeyl]

informal_lemma leftAltWeylContraction_symm_altLeftWeylContraction where
  math :≈ "The linear map altLeftWeylContraction is leftAltWeylContraction composed
    with the braiding of the tensor product."
  deps :≈ [``leftAltWeylContraction, ``altLeftWeylContraction]

informal_lemma altLeftWeylContraction_invariant where
  math :≈ "The contraction altLeftWeylContraction is invariant with respect to
    the action of SL(2,C) on leftHandedWeyl and altLeftHandedWeyl."
  deps :≈ [``altLeftWeylContraction]

informal_definition rightAltWeylContraction where
  math :≈ "The linear map from rightHandedWeyl ⊗ altRightHandedWeyl to ℂ given by
    summing over components of rightHandedWeyl and altRightHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is ψ_{dot a} φ^{dot a}."
  deps :≈ [``rightHandedWeyl, ``altRightHandedWeyl]

informal_lemma rightAltWeylContraction_invariant where
  math :≈ "The contraction rightAltWeylContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``rightAltWeylContraction]

informal_definition altRightWeylContraction where
  math :≈ "The linear map from altRightHandedWeyl ⊗ rightHandedWeyl to ℂ given by
    summing over components of altRightHandedWeyl and rightHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ^{dot a} ψ_{dot a}."
  deps :≈ [``rightHandedWeyl, ``altRightHandedWeyl]

informal_lemma rightAltWeylContraction_symm_altRightWeylContraction where
  math :≈ "The linear map altRightWeylContraction is rightAltWeylContraction composed
    with the braiding of the tensor product."
  deps :≈ [``rightAltWeylContraction, ``altRightWeylContraction]

informal_lemma altRightWeylContraction_invariant where
  math :≈ "The contraction altRightWeylContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``altRightWeylContraction]

end Fermion
