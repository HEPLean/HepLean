/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.HiggsBoson.Basic
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

Currently this file contains the definition of the 2HDM potential.

-/

namespace TwoHDM

open StandardModel
open ComplexConjugate

noncomputable section

/-- The potential of the two Higgs doublet model.  -/
def potential (Φ1 Φ2 : higgsField)
    (m11Sq m22Sq lam₁ lam₂ lam₃ lam₄ : ℝ) (m12Sq lam₅ lam₆ lam₇ : ℂ) (x : spaceTime) : ℝ :=
  m11Sq * Φ1.normSq x  + m22Sq * Φ2.normSq x
  - (m12Sq * (Φ1.innerProd Φ2) x + conj m12Sq * (Φ2.innerProd Φ1) x).re
  + 1/2 * lam₁ * Φ1.normSq x ^ 2 + 1/2 * lam₂ * Φ2.normSq x ^ 2
  + lam₃ * Φ1.normSq x * Φ2.normSq x
  + lam₄ * ‖Φ1.innerProd Φ2 x‖
  + (1/2 * lam₅ * (Φ1.innerProd Φ2) x ^ 2 + 1/2 * conj lam₅ * (Φ2.innerProd Φ1) x ^ 2).re
  + (lam₆ * Φ1.normSq x * (Φ1.innerProd Φ2) x + conj lam₆ * Φ1.normSq x * (Φ2.innerProd Φ1) x).re
  + (lam₇ * Φ2.normSq x * (Φ1.innerProd Φ2) x + conj lam₇ * Φ2.normSq x * (Φ2.innerProd Φ1) x).re

end
end TwoHDM
