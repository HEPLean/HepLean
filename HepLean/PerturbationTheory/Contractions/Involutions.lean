/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Basic
import HepLean.Meta.Informal.Basic
/-!

# Involutions

There is an isomorphism between the type of contractions of a list `l` and
the type of involutions from `Fin l.length` to `Fin l.length`.

Likewise, there is an isomorphism from the type of full contractions of a list `l`
and the type of fixed-point free involutions from `Fin l.length` to `Fin l.length`.

Given this, the number of full contractions of a list `l` is
is given by the OEIS sequence A000085.

-/

namespace Wick

open HepLean.List
open FieldStatistic

variable {𝓕 : Type}
namespace Contractions

variable {l : List 𝓕}

informal_definition equivInvolution where
  math :≈ "There is an isomorphism between the type of contractions of a list `l` and
    the type of involutions from `Fin l.length` to `Fin l.length."

informal_definition equivFullInvolution where
  math :≈ "There is an isomorphism from the type of full contractions of a list `l`
    and the type of fixed-point free involutions from `Fin l.length` to `Fin l.length."

end Contractions

end Wick
