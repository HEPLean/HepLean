/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
/-!

# Wick's theorem

Wick's theorem is related to a result in probability theory called Isserlis' theorem.

-/

namespace Wick
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

informal_lemma wicks_theorem where
  math :≈ "Wick's theorem for fields which are not normally ordered."

informal_lemma wicks_theorem_normal_order where
  math :≈ "Wick's theorem for which fields at the same space-time point are normally ordered."
  ref :≈ "https://www.physics.purdue.edu/~clarkt/Courses/Physics662/ps/qftch32.pdf"

informal_lemma wicks_theorem_vev where
  math :≈ "Wick's theorem in a vev leaving only full contractions of Wick strings left."

informal_lemma wicks_theorem_asymptotic_states where
  math :≈ "Wick's theorem for a term in the Dyson series within asymptotic states
    leaves only full contractions with the asymptotic states."

end Wick
