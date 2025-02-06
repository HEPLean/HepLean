/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.RealVector.Basic
import HepLean.PerturbationTheory.FieldStatistics.ExchangeSign
import HepLean.SpaceTime.Basic
import HepLean.PerturbationTheory.FieldStatistics.OfFinset
import HepLean.Meta.Remark.Basic
/-!

# Field specification

In this module is the definition of a field specification.
A field specification is a structure consisting of a type of fields and a
the field statistics of each field.

From each field we can create three different types of `FieldOp`.
- Negative asymptotic states.
- Position states.
- Positive asymptotic states.

These states carry the same field statistic as the field they are derived from.

## Some references

- https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf

-/

/-- A field specification is defined as a structure containing the basic data needed to write down
  position and asymptotic field operators for a theory. It contains:
  - A type `positionDOF` containing the degree-of-freedom in position-based field
  operators (excluding space-time position). Thus a sutible (but not unique) choice
    - Real-scalar fields correspond to a single element of `positionDOF`.
    - Complex-scalar fields correspond to two elements of `positionDOF`, one for the field and one
      for its conjugate.
    - Dirac fermions correspond to eight elements of `positionDOF`. One for each Lorentz index of
      the field and its conjugate. (These are not all independent)
    - Weyl fermions correspond to four elements of `positionDOF`. One for each Lorentz index of the
      field. (These are not all independent)
  - A type `asymptoticDOF` containing the degree-of-freedom in asymptotic field operators. Thus a
    sutible (but not unique) choice is
    - Real-scalar fields correspond to a single element of `asymptoticDOF`.
    - Complex-scalar fields correspond to two elements of `asymptoticDOF`, one for the field and one
      for its conjugate.
    - Dirac fermions correspond to four elements of `asymptoticDOF`, two for each type of spin.
    - Weyl fermions correspond to two elements of `asymptoticDOF`, one for each spin.
  - A specification `statisticsPos` on a `positionDOF` is Fermionic or Bosonic.
  - A specification `statisticsAsym` on a `asymptoticDOF` is Fermionic or Bosonic.
-/
structure FieldSpecification where
  /-- Degrees of freedom for position based field operators. -/
  positionDOF : Type
  /-- Degrees of freedom for asymptotic based field operators. -/
  asymptoticDOF : Type
  /-- The specification if the `positionDOF` are Fermionic or Bosonic. -/
  statisticsPos : positionDOF → FieldStatistic
  /-- The specification if the `asymptoticDOF` are Fermionic or Bosonic. -/
  statisticsAsym : asymptoticDOF → FieldStatistic

namespace FieldSpecification
variable (𝓕 : FieldSpecification)

/-- For a field specification `𝓕`, the type `𝓕.FieldOp` is defined such that every element of
  `FieldOp` corresponds either to:
- an incoming asymptotic field operator `.inAsymp` specified by a field and a `3`-momentum.
- an position operator `.position` specified by a field and a point in spacetime.
- an outgoing asymptotic field operator `.outAsymp` specified by a field and a `3`-momentum.
-/
inductive FieldOp (𝓕 : FieldSpecification) where
  | inAsymp : 𝓕.asymptoticDOF × (Fin 3 → ℝ) → 𝓕.FieldOp
  | position : 𝓕.positionDOF × SpaceTime → 𝓕.FieldOp
  | outAsymp : 𝓕.asymptoticDOF × (Fin 3 → ℝ) → 𝓕.FieldOp


/-- The bool on `FieldOp` which is true only for position field operator. -/
def statesIsPosition : 𝓕.FieldOp → Bool
  | FieldOp.position _ => true
  | _ => false

/-- The statistics associated to a field operator. -/
def statesStatistic : 𝓕.FieldOp → FieldStatistic := fun f =>
  match f with
  | FieldOp.inAsymp (a, _) => 𝓕.statisticsAsym a
  | FieldOp.position (a, _) => 𝓕.statisticsPos a
  | FieldOp.outAsymp (a, _) => 𝓕.statisticsAsym a

/-- The field statistics associated with a field operator. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => statesStatistic 𝓕 φ

/-- The field statistics associated with a list field operators. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => FieldStatistic.ofList
    (statesStatistic 𝓕) φ

/-- The field statistic associated with a finite set-/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" "⟨" f ","a "⟩"=> FieldStatistic.ofFinset
    (statesStatistic 𝓕) f a

end FieldSpecification
