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

informal_definition leftHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the fundamental representation of SL(2,C)."
  physics :≈ "A Weyl fermion with indices ψ_a."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition rightHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the conjguate representation of SL(2,C)."
  physics :≈ "A Weyl fermion with indices ψ_{dot a}."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition altLeftHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ."
  physics :≈ "A Weyl fermion with indices ψ^a."
  ref :≈ "https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf"

informal_definition altRightHandedWeylFermion where
  math :≈ "The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†."
  physics :≈ "A Weyl fermion with indices ψ^{dot a}."
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

/-!

## Contraction of Weyl fermions.

-/

informal_definition leftAltWeylFermionContraction where
  math :≈ "The linear map from leftHandedWeylFermion ⊗ altLeftHandedWeylFermion to ℂ given by
    summing over components of leftHandedWeylFermion and altLeftHandedWeylFermion in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a left-handed Weyl fermion with a right-handed Weyl fermion.
    In index notation this is ψ_a φ^a."
  deps :≈ [``leftHandedWeylFermion, ``altLeftHandedWeylFermion]

informal_lemma leftAltWeylFermionContraction_invariant where
  math :≈ "The contraction leftAltWeylFermionContraction is invariant with respect to
    the action of SL(2,C) on leftHandedWeylFermion and altLeftHandedWeylFermion."
  deps :≈ [``leftAltWeylFermionContraction]

informal_definition altLeftWeylFermionContraction where
  math :≈ "The linear map from altLeftHandedWeylFermion ⊗ leftHandedWeylFermion  to ℂ given by
    summing over components of altLeftHandedWeylFermion and leftHandedWeylFermion  in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a left-handed Weyl fermion with a right-handed Weyl fermion.
    In index notation this is φ^a ψ_a ."
  deps :≈ [``leftHandedWeylFermion, ``altLeftHandedWeylFermion]

informal_lemma leftAltWeylFermionContraction_symm_altLeftWeylFermionContraction where
  math :≈ "The linear map altLeftWeylFermionContraction is leftAltWeylFermionContraction composed
    with the braiding of the tensor product."
  deps :≈ [``leftAltWeylFermionContraction, ``altLeftWeylFermionContraction]

informal_lemma altLeftWeylFermionContraction_invariant where
  math :≈ "The contraction altLeftWeylFermionContraction is invariant with respect to
    the action of SL(2,C) on leftHandedWeylFermion and altLeftHandedWeylFermion."
  deps :≈ [``altLeftWeylFermionContraction]

informal_definition rightAltWeylFermionContraction where
  math :≈ "The linear map from rightHandedWeylFermion ⊗ altRightHandedWeylFermion to ℂ given by
    summing over components of rightHandedWeylFermion and altRightHandedWeylFermion in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is ψ_{dot a} φ^{dot a}."
  deps :≈ [``rightHandedWeylFermion, ``altRightHandedWeylFermion]

informal_lemma rightAltWeylFermionContraction_invariant where
  math :≈ "The contraction rightAltWeylFermionContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeylFermion and altRightHandedWeylFermion."
  deps :≈ [``rightAltWeylFermionContraction]

informal_definition altRightWeylFermionContraction where
  math :≈ "The linear map from altRightHandedWeylFermion ⊗ rightHandedWeylFermion to ℂ given by
    summing over components of altRightHandedWeylFermion and rightHandedWeylFermion in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ^{dot a} ψ_{dot a}."
  deps :≈ [``rightHandedWeylFermion, ``altRightHandedWeylFermion]

informal_lemma rightAltWeylFermionContraction_symm_altRightWeylFermionContraction where
  math :≈ "The linear map altRightWeylFermionContraction is rightAltWeylFermionContraction composed
    with the braiding of the tensor product."
  deps :≈ [``rightAltWeylFermionContraction, ``altRightWeylFermionContraction]

informal_lemma altRightWeylFermionContraction_invariant where
  math :≈ "The contraction altRightWeylFermionContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeylFermion and altRightHandedWeylFermion."
  deps :≈ [``altRightWeylFermionContraction]
