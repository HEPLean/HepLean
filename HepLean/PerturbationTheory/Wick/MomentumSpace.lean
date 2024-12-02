/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Contract
/-!

# Wick contraction in momentum space

Every complete Wick contraction leads to a function on momenta, following
the Feynman rules.

-/

namespace Wick

informal_definition toMomentumTensorTree where
  math :≈ "A function which takes a Wick contraction,
    and corresponding momenta, and outputs the corresponding
    tensor tree associated with that contraction. The rules for how this is done
    is given by the `Feynman rules`.
    The appropriate ring to consider here is a ring permitting the abstract notion of a
    Dirac delta function. "
  ref :≈ "
    Some references for Feynman rules are:
    - QED Feynman rules: http://hitoshi.berkeley.edu/public_html/129A/point.pdf,
    - Weyl Fermions: http://scipp.ucsc.edu/~haber/susybook/feyn115.pdf."

informal_definition toMomentumTensor where
  math :≈ "The tensor associated to `toMomentumTensorTree` associated with a Wick contraction,
    and corresponding internal momenta, and external momenta."
  deps :≈ [``toMomentumTensorTree]

end Wick
