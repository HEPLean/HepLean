/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Module.LinearMap.Basic
/-!
# Linear maps

Some definitions and properites of linear, bilinear, and trilinear maps, along with homogeneous
quadratic and cubic equations.

## TODO

Use definitions in `Mathlib4` for definitions where possible.

-/

/-- The structure defining a homogeneous quadratic equation. -/
structure HomogeneousQuadratic (V : Type) [AddCommMonoid V] [Module ℚ V] where
  /-- The quadratic equation. -/
  toFun : V → ℚ
  /-- The equation is homogeneous. -/
  map_smul' : ∀ a S,  toFun (a • S) = a ^ 2 * toFun S

namespace HomogeneousQuadratic

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (HomogeneousQuadratic V) V ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

lemma map_smul (f : HomogeneousQuadratic V) (a : ℚ) (S : V) : f (a • S) = a ^ 2 * f S :=
  f.map_smul' a S

end HomogeneousQuadratic


structure BiLinear (V : Type) [AddCommMonoid V] [Module ℚ V] where
  toFun : V × V → ℚ
  map_smul₁' : ∀ a S T, toFun (a • S, T) = a * toFun (S, T)
  map_smul₂' : ∀ a S T , toFun (S, a • T) = a * toFun (S, T)
  map_add₁' : ∀ S1 S2 T, toFun (S1 + S2, T) = toFun (S1, T) + toFun (S2, T)
  map_add₂' : ∀ S T1 T2, toFun (S, T1 + T2) = toFun (S, T1) + toFun (S, T2)

namespace BiLinear

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (BiLinear V) (V × V) ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

lemma map_smul₁ (f : BiLinear V) (a : ℚ) (S T : V) : f (a • S, T) = a * f (S, T) :=
  f.map_smul₁' a S T

lemma map_smul₂ (f : BiLinear V) (S : V) (a : ℚ) (T : V) : f (S, a • T) = a * f (S, T) :=
  f.map_smul₂' a S T

lemma map_add₁ (f : BiLinear V) (S1 S2 T : V) : f (S1 + S2, T) = f (S1, T) + f (S2, T) :=
  f.map_add₁' S1 S2 T

lemma map_add₂ (f : BiLinear V) (S : V) (T1 T2 : V) : f (S, T1 + T2) = f (S, T1) + f (S, T2) :=
  f.map_add₂' S T1 T2

end BiLinear

structure BiLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] where
  toFun : V × V → ℚ
  map_smul₁' : ∀ a S T, toFun (a • S, T) = a * toFun (S, T)
  map_add₁' : ∀ S1 S2 T, toFun (S1 + S2, T) = toFun (S1, T) + toFun (S2, T)
  swap' : ∀ S T, toFun (S, T) = toFun (T, S)



namespace BiLinearSymm

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun (V : Type) [AddCommMonoid V] [Module ℚ V] :
    FunLike (BiLinearSymm V) (V × V) ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all


lemma toFun_eq_coe (f : BiLinearSymm V) : f.toFun = f := rfl


lemma map_smul₁ (f : BiLinearSymm V) (a : ℚ) (S T : V) : f (a • S, T) = a * f (S, T) :=
  f.map_smul₁' a S T

lemma swap (f : BiLinearSymm V) (S T : V) : f (S, T) = f (T, S) :=
  f.swap' S T

lemma map_smul₂ (f : BiLinearSymm V) (a : ℚ)  (S : V) (T : V) : f (S, a • T) = a * f (S, T) := by
  rw [f.swap, f.map_smul₁, f.swap]


lemma map_add₁ (f : BiLinearSymm V) (S1 S2 T : V) : f (S1 + S2, T) = f (S1, T) + f (S2, T) :=
  f.map_add₁' S1 S2 T

lemma map_add₂ (f : BiLinearSymm V) (S : V) (T1 T2 : V) :
    f (S, T1 + T2) = f (S, T1) + f (S, T2) := by
  rw [f.swap, f.map_add₁, f.swap T1 S, f.swap T2 S]


@[simps!]
def toHomogeneousQuad {V : Type} [AddCommMonoid V] [Module ℚ V]
    (τ : BiLinearSymm V) : HomogeneousQuadratic V where
  toFun S := τ (S, S)
  map_smul' a S := by
    simp only
    rw [τ.map_smul₁, τ.map_smul₂]
    ring

lemma toHomogeneousQuad_add {V : Type} [AddCommMonoid V] [Module ℚ V]
    (τ : BiLinearSymm V) (S T : V) :
    τ.toHomogeneousQuad (S + T) = τ.toHomogeneousQuad S +
    τ.toHomogeneousQuad T + 2 * τ (S, T) := by
  simp only [toHomogeneousQuad_toFun]
  rw [τ.map_add₁, τ.map_add₂, τ.map_add₂, τ.swap T S]
  ring


end BiLinearSymm


structure HomogeneousCubic (V : Type) [AddCommMonoid V] [Module ℚ V] where
  toFun : V → ℚ
  map_smul' : ∀ a S, toFun (a • S) = a ^ 3 * toFun S

namespace HomogeneousCubic

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (HomogeneousCubic V) V ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

lemma map_smul (f : HomogeneousCubic V) (a : ℚ) (S : V) : f (a • S) = a ^ 3 * f S :=
  f.map_smul' a S

end HomogeneousCubic

structure TriLinear (V : Type) [AddCommMonoid V] [Module ℚ V] where
  toFun : V × V × V → ℚ
  map_smul₁' : ∀ a S T L, toFun (a • S, T, L) = a * toFun (S, T, L)
  map_smul₂' : ∀ a S T L, toFun (S, a • T, L) = a * toFun (S, T, L)
  map_smul₃' : ∀ a S T L, toFun (S, T, a • L) = a * toFun (S, T, L)
  map_add₁' : ∀ S1 S2 T L, toFun (S1 + S2, T, L) = toFun (S1, T, L) + toFun (S2, T, L)
  map_add₂' : ∀ S T1 T2 L, toFun (S, T1 + T2, L) = toFun (S, T1, L) + toFun (S, T2, L)
  map_add₃' : ∀ S T L1 L2, toFun (S, T, L1 + L2) = toFun (S, T, L1) + toFun (S, T, L2)

namespace TriLinear

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (TriLinear V) (V × V × V) ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

end TriLinear

structure TriLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] where
  toFun : V × V × V → ℚ
  map_smul₁' : ∀ a S T L, toFun (a • S, T, L) = a * toFun (S, T, L)
  map_add₁' : ∀ S1 S2 T L, toFun (S1 + S2, T, L) = toFun (S1, T, L) + toFun (S2, T, L)
  swap₁' : ∀ S T L, toFun (S, T, L) = toFun (T, S, L)
  swap₂' : ∀ S T L, toFun (S, T, L) = toFun (S, L, T)

namespace TriLinearSymm

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (TriLinearSymm V) (V × V × V) ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all


lemma toFun_eq_coe (f : TriLinearSymm V) : f.toFun = f := rfl

lemma swap₁ (f : TriLinearSymm V) (S T L : V) : f (S, T, L) = f (T, S, L) :=
  f.swap₁' S T L

lemma swap₂ (f : TriLinearSymm V) (S T L : V) : f (S, T, L) = f (S, L, T) :=
  f.swap₂' S T L

lemma swap₃ (f : TriLinearSymm V) (S T L : V) : f (S, T, L) = f (L, T, S) := by
  rw [f.swap₁, f.swap₂, f.swap₁]

lemma map_smul₁ (f : TriLinearSymm V) (a : ℚ) (S T L : V) :
    f (a • S, T, L) = a * f (S, T, L) :=
  f.map_smul₁' a S T L

lemma map_smul₂ (f : TriLinearSymm V) (S : V) (a : ℚ) (T L : V) :
    f (S, a • T, L) = a * f (S, T, L) := by
  rw [f.swap₁, f.map_smul₁, f.swap₁]

lemma map_smul₃ (f : TriLinearSymm V) (S T : V) (a : ℚ) (L : V) :
    f (S, T, a • L) = a * f (S, T, L) := by
  rw [f.swap₃, f.map_smul₁, f.swap₃]

lemma map_add₁ (f : TriLinearSymm V) (S1 S2 T L : V) :
    f (S1 + S2, T, L) = f (S1, T, L) + f (S2, T, L) :=
  f.map_add₁' S1 S2 T L

lemma map_add₂ (f : TriLinearSymm V) (S T1 T2 L : V) :
    f (S, T1 + T2, L) = f (S, T1, L) + f (S, T2, L) := by
  rw [f.swap₁, f.map_add₁, f.swap₁ S T1, f.swap₁ S T2]

lemma map_add₃ (f : TriLinearSymm V) (S T L1 L2 : V) :
    f (S, T, L1 + L2) = f (S, T, L1) + f (S, T, L2) := by
  rw [f.swap₃, f.map_add₁, f.swap₃, f.swap₃ L2 T S]

@[simps!]
def toCubic {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) : HomogeneousCubic charges where
  toFun S := τ (S, S, S)
  map_smul' a S := by
    simp only
    rw [τ.map_smul₁, τ.map_smul₂, τ.map_smul₃]
    ring

lemma toCubic_add {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) (S T : charges) :
    τ.toCubic (S + T) = τ.toCubic S +
    τ.toCubic T + 3 * τ (S, S, T) + 3 * τ (T, T, S) := by
  simp only [toCubic_toFun]
  rw [τ.map_add₁, τ.map_add₂, τ.map_add₂, τ.map_add₃, τ.map_add₃, τ.map_add₃, τ.map_add₃]
  rw [τ.swap₂ S T S, τ.swap₁ T S S, τ.swap₂ S T S, τ.swap₂ T S T, τ.swap₁ S T T, τ.swap₂ T S T]
  ring

end TriLinearSymm
