/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
import HepLean.Mathematics.SuperAlgebra.Basic
import HepLean.Meta.Notes.Basic
/-!

# Operator algebra

Currently this file is only for an example of Wick strings, correpsonding to a
theory with two complex scalar fields. The concepts will however generalize.

We will formally define the operator ring, in terms of the fields present in the theory.

## Futher reading

- https://physics.stackexchange.com/questions/258718/ and links therein
- Ryan Thorngren (https://physics.stackexchange.com/users/10336/ryan-thorngren), Fermions,
  different species and (anti-)commutation rules, URL (version: 2019-02-20) :
  https://physics.stackexchange.com/q/461929
- Tong, https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf
-/

note "
  <h1>Operator algebra</h1>
  This is a test note."

namespace Wick

informal_definition_note WickAlgebra where
  math :≈ "
    Modifications of this may be needed.
    A structure with the following data:
    - A super algebra A.
    - A map from `ψ : S.𝓯 × SpaceTime → A` where S.𝓯 are field colors.
    - A map `ψc : S.𝓯 × SpaceTime → A`.
    - A map `ψd : S.𝓯 × SpaceTime → A`.
    Subject to the conditions:
    - The sum of `ψc` and `ψd` is `ψ`.
    - All maps land on homogeneous elements.
    - Two fields super-commute if there colors are not dual to each other.
    - The super-commutator of two fields is always in the
      center of the algebra.
    Asympotic states:
    - `φc : S.𝓯 × SpaceTime → A`. The creation asympotic state (incoming).
    - `φd : S.𝓯 × SpaceTime → A`. The destruction asympotic state (outgoing).
    Subject to the conditions:
    ...
      "
  physics :≈ "This is defined to be an
    abstraction of the notion of an operator algebra."
  ref :≈ "https://physics.stackexchange.com/questions/24157/"
  deps :≈ [``SuperAlgebra, ``SuperAlgebra.superCommuator]

informal_definition_note WickMonomial where
  math :≈ "The type of elements of the Wick algebra which is a product of fields."
  deps :≈ [``WickAlgebra]

namespace WickMonomial

informal_definition toWickAlgebra where
  math :≈ "A function from WickMonomial to WickAlgebra which takes a monomial and
    returns the product of the fields in the monomial."
  deps :≈ [``WickAlgebra, ``WickMonomial]

informal_definition timeOrder where
  math :≈ "A function from WickMonomial to WickAlgebra which takes a monomial and
    returns the monomial with the fields time ordered, with the correct sign
    determined by the Koszul sign factor.

    If two fields have the same time, then their order is preserved e.g.
    T(ψ₁(t)ψ₂(t)) = ψ₁(t)ψ₂(t)
    and
    T(ψ₂(t)ψ₁(t)) = ψ₂(t)ψ₁(t).
    This allows us to make sense of the construction in e.g.
    https://www.physics.purdue.edu/~clarkt/Courses/Physics662/ps/qftch32.pdf
    which permits normal-ordering within time-ordering.
    "
  deps :≈ [``WickAlgebra, ``WickMonomial]

informal_definition normalOrder where
  math :≈ "A function from WickMonomial to WickAlgebra which takes a monomial and
    returns the element in `WickAlgebra` defined as follows
    - The ψd fields are move to the right.
    - The ψc fields are moved to the left.
    - Othewise the order of the fields is preserved."
  ref :≈ "https://www.imperial.ac.uk/media/imperial-college/research-centres-and-groups/theoretical-physics/msc/current/qft/handouts/qftwickstheorem.pdf"
  deps :≈ [``WickAlgebra, ``WickMonomial]

end WickMonomial

informal_definition asymptoicContract where
  math :≈ "Given two `i j : S.𝓯 × SpaceTime`, the super-commutator [φd(i), ψ(j)]."
  ref :≈ "See e.g. http://www.dylanjtemples.com:82/solutions/QFT_Solution_I-6.pdf"

informal_definition contractAsymptotic where
  math :≈ "Given two `i j : S.𝓯 × SpaceTime`, the super-commutator [ψ(i), φc(j)]."

informal_definition asymptoicContractAsymptotic where
  math :≈ "Given two `i j : S.𝓯 × SpaceTime`, the super-commutator
    [φd(i), φc(j)]."

informal_definition contraction where
  math :≈ "Given two `i j : S.𝓯 × SpaceTime`, the element of WickAlgebra
    defined by subtracting the normal ordering of `ψ i ψ j` from the time-ordering of
    `ψ i ψ j`."
  deps :≈ [``WickAlgebra, ``WickMonomial]

informal_lemma contraction_in_center where
  math :≈ "The contraction of two fields is in the center of the algebra."
  deps :≈ [``WickAlgebra, ``contraction]

informal_lemma contraction_non_dual_is_zero where
  math :≈ "The contraction of two fields is zero if the fields are not dual to each other."
  deps :≈ [``WickAlgebra, ``contraction]

informal_lemma timeOrder_single where
  math :≈ "The time ordering of a single field is the normal ordering of that field."
  proof :≈ "Follows from the definitions."
  deps :≈ [``WickAlgebra, ``WickMonomial.timeOrder, ``WickMonomial.normalOrder]

informal_lemma timeOrder_pair where
  math :≈ "The time ordering of two fields is the normal ordering of the fields plus the
    contraction of the fields."
  proof :≈ "Follows from the definition of contraction."
  deps :≈ [``WickAlgebra, ``WickMonomial.timeOrder, ``WickMonomial.normalOrder,
    ``contraction]

informal_definition WickMap where
  math :≈ "A linear map `vev` from the Wick algebra `A` to the underlying field such that
    `vev(...ψd(t)) = 0` and `vev(ψc(t)...) = 0`."
  physics :≈ "An abstraction of the notion of a vacuum expectation value, containing
    the necessary properties for lots of theorems to hold."
  deps :≈ [``WickAlgebra, ``WickMonomial]

informal_lemma normalOrder_wickMap where
  math :≈ "Any normal ordering maps to zero under a Wick map."
  deps :≈ [``WickMap, ``WickMonomial.normalOrder]

end Wick
