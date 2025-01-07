/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Basic
import HepLean.PerturbationTheory.FieldStruct.CreateAnnihilateAlgebra
/-!

# Creation and annihlation parts of fields

-/

namespace FieldStruct
variable (𝓕 : FieldStruct)
open CrAnAlgebra

structure OperatorAlgebra where
  A : Type
  [A_semiRing : Semiring A] [A_algebra : Algebra ℂ A]
  crAnF : 𝓕.CrAnAlgebra →ₐ[ℂ] A
  superCommute_crAn_center : ∀ (φ ψ : 𝓕.CrAnStates),
    crAnF (superCommute (ofCrAnState φ) (ofCrAnState ψ))
    ∈ Subalgebra.center ℂ A
  superCommute_create_create : ∀ (φc φc' : 𝓕.CrAnStates)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.create),
    crAnF (superCommute (ofCrAnState φc) (ofCrAnState φc')) = 0
  superCommute_annihilate_annihilate : ∀ (φa φa' : 𝓕.CrAnStates)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.annihilate)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.annihilate),
    crAnF (superCommute (ofCrAnState φa) (ofCrAnState φa')) = 0

namespace OperatorAlgebra

variable {𝓕 : FieldStruct} (𝓞 : 𝓕.OperatorAlgebra)

instance : Semiring 𝓞.A := 𝓞.A_semiRing

instance : Algebra ℂ 𝓞.A := 𝓞.A_algebra

end OperatorAlgebra
end FieldStruct
