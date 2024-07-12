/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.BigOperators
/-!
# Linear maps

Some definitions and properties of linear, bilinear, and trilinear maps, along with homogeneous
quadratic and cubic equations.

-/
/-! TODO: Replace the definitions in this file with Mathlib definitions. -/

/-- The structure defining a homogeneous quadratic equation. -/
@[simp]
def HomogeneousQuadratic (V : Type) [AddCommMonoid V] [Module ℚ V] : Type :=
  V →ₑ[((fun a => a ^ 2) : ℚ → ℚ)] ℚ

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

/-- The structure of a symmetric bilinear function. -/
structure BiLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] extends V →ₗ[ℚ] V →ₗ[ℚ] ℚ where
  swap' : ∀ S T, toFun S T = toFun T S

/-- A symmetric bilinear function. -/
class IsSymmetric {V : Type} [AddCommMonoid V] [Module ℚ V] (f : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) : Prop where
  swap : ∀ S T, f S T = f T S

namespace BiLinearSymm
open BigOperators

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun (V : Type) [AddCommMonoid V] [Module ℚ V] :
    FunLike (BiLinearSymm V) V (V →ₗ[ℚ] ℚ) where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

/-- The construction of a symmetric bilinear map from `smul` and `map_add` in the first factor,
and swap. -/
@[simps!]
def mk₂ (f : V × V → ℚ) (map_smul : ∀ a S T, f (a • S, T) = a * f (S, T))
    (map_add : ∀ S1 S2 T, f (S1 + S2, T) = f (S1, T) + f (S2, T))
    (swap : ∀ S T, f (S, T) = f (T, S)) : BiLinearSymm V where
  toFun := fun S => {
    toFun := fun T => f (S, T)
    map_add' := by
      intro T1 T2
      simp only
      rw [swap, map_add]
      exact Mathlib.Tactic.LinearCombination.add_pf (swap T1 S) (swap T2 S)
    map_smul' :=by
      intro a T
      simp only [eq_ratCast, Rat.cast_eq_id, id_eq, smul_eq_mul]
      rw [swap, map_smul]
      exact congrArg (HMul.hMul a) (swap T S)
  }
  map_smul' := fun a S  => LinearMap.ext fun T => map_smul a S T
  map_add' := fun S1 S2 => LinearMap.ext fun T => map_add S1 S2 T
  swap' := swap

lemma map_smul₁ (f : BiLinearSymm V) (a : ℚ) (S T : V) : f (a • S) T = a * f S T := by
  erw [f.map_smul a S]
  rfl

lemma swap (f : BiLinearSymm V) (S T : V) : f S T = f T S :=
  f.swap' S T

lemma map_smul₂ (f : BiLinearSymm V) (a : ℚ)  (S : V) (T : V) : f S (a • T) = a * f S T := by
  rw [f.swap, f.map_smul₁, f.swap]

lemma map_add₁ (f : BiLinearSymm V) (S1 S2 T : V) : f (S1 + S2) T = f S1 T + f S2 T := by
  erw [f.map_add]
  rfl

lemma map_add₂ (f : BiLinearSymm V) (S : V) (T1 T2 : V) :
    f S (T1 + T2) = f S T1 + f S T2 := by
  rw [f.swap, f.map_add₁, f.swap T1 S, f.swap T2 S]

/-- Fixing the second input vectors, the resulting linear map. -/
def toLinear₁ (f : BiLinearSymm V) (T : V) : V →ₗ[ℚ] ℚ where
  toFun S := f S T
  map_add' S1 S2 := map_add₁ f S1 S2 T
  map_smul' a S := by
    simp only [f.map_smul₁]
    rfl

lemma toLinear₁_apply (f : BiLinearSymm V) (S T : V) : f S T = f.toLinear₁ T S := rfl

lemma map_sum₁ {n : ℕ} (f : BiLinearSymm V) (S : Fin n → V) (T : V)  :
    f (∑ i, S i) T = ∑ i, f (S i) T := by
  rw [f.toLinear₁_apply]
  rw [map_sum]
  rfl

lemma map_sum₂ {n : ℕ} (f : BiLinearSymm V) (S : Fin n → V) (T : V) :
    f T (∑ i, S i) = ∑ i, f T (S i) := by
  rw [swap, map_sum₁]
  apply Fintype.sum_congr
  intro i
  rw [swap]

/-- The homogenous quadratic equation obtainable from a bilinear function. -/
@[simps!]
def toHomogeneousQuad {V : Type} [AddCommMonoid V] [Module ℚ V]
    (τ : BiLinearSymm V) : HomogeneousQuadratic V where
  toFun S := τ S S
  map_smul' a S := by
    simp only
    rw [τ.map_smul₁, τ.map_smul₂]
    ring_nf
    rfl

lemma toHomogeneousQuad_add {V : Type} [AddCommMonoid V] [Module ℚ V]
    (τ : BiLinearSymm V) (S T : V) :
    τ.toHomogeneousQuad (S + T) = τ.toHomogeneousQuad S +
    τ.toHomogeneousQuad T + 2 * τ S T := by
  simp [toHomogeneousQuad_apply]
  rw [τ.map_add₁, τ.map_add₁, τ.swap T S]
  ring

end BiLinearSymm

/-- The structure of a homogeneous cubic equation. -/
@[simp]
def HomogeneousCubic (V : Type) [AddCommMonoid V] [Module ℚ V] : Type :=
  V →ₑ[((fun a => a ^ 3) : ℚ → ℚ)] ℚ

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

/-- The structure of a symmetric trilinear function. -/
structure TriLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] extends
    V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] ℚ where
  swap₁' : ∀ S T L, toFun S T L = toFun T S L
  swap₂' : ∀ S T L, toFun S T L = toFun S L T

namespace TriLinearSymm
open BigOperators
variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (TriLinearSymm V) V (V →ₗ[ℚ] V →ₗ[ℚ] ℚ )  where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

/-- The construction of a symmetric trilinear map from `smul` and `map_add` in the first factor,
and two swap. -/
@[simps!]
def mk₃ (f : V × V × V→ ℚ) (map_smul : ∀ a S T L, f (a • S, T, L) = a * f (S, T, L))
    (map_add : ∀ S1 S2 T L, f (S1 + S2, T, L) = f (S1, T, L) + f (S2, T, L))
    (swap₁ : ∀ S T L, f (S, T, L) = f (T, S, L))
    (swap₂ : ∀ S T L, f (S, T, L) = f (S, L, T)) : TriLinearSymm V where
  toFun := fun S => (BiLinearSymm.mk₂ (fun T => f (S, T))
    (by
      intro a T L
      simp only
      rw [swap₁, map_smul, swap₁])
    (by
      intro S1 S2 T
      simp only
      rw [swap₁, map_add, swap₁, swap₁ S2 S T])
    (by
      intro L T
      simp only
      rw [swap₂])).toLinearMap
  map_add' S1 S2 := by
    apply LinearMap.ext
    intro T
    apply LinearMap.ext
    intro S
    simp [BiLinearSymm.mk₂, map_add]
  map_smul' a S := by
    apply LinearMap.ext
    intro T
    apply LinearMap.ext
    intro L
    simp [BiLinearSymm.mk₂, map_smul]
  swap₁' := swap₁
  swap₂' := swap₂

lemma swap₁ (f : TriLinearSymm V) (S T L : V) : f S T L = f T S L :=
  f.swap₁' S T L

lemma swap₂ (f : TriLinearSymm V) (S T L : V) : f S T L = f S L T :=
  f.swap₂' S T L

lemma swap₃ (f : TriLinearSymm V) (S T L : V) : f S T L = f L T S := by
  rw [f.swap₁, f.swap₂, f.swap₁]

lemma map_smul₁ (f : TriLinearSymm V) (a : ℚ) (S T L : V) :
    f (a • S) T L = a * f S T L := by
  erw [f.map_smul a S]
  rfl

lemma map_smul₂ (f : TriLinearSymm V) (S : V) (a : ℚ) (T L : V) :
    f S (a • T) L = a * f S T L := by
  rw [f.swap₁, f.map_smul₁, f.swap₁]

lemma map_smul₃ (f : TriLinearSymm V) (S T : V) (a : ℚ) (L : V) :
    f S T (a • L) = a * f S T L := by
  rw [f.swap₃, f.map_smul₁, f.swap₃]

lemma map_add₁ (f : TriLinearSymm V) (S1 S2 T L : V) :
    f (S1 + S2) T L = f S1 T L + f S2 T L := by
  erw [f.map_add]
  rfl

lemma map_add₂ (f : TriLinearSymm V) (S T1 T2 L : V) :
    f S (T1 + T2) L = f S T1 L + f S T2 L := by
  rw [f.swap₁, f.map_add₁, f.swap₁ S T1, f.swap₁ S T2]

lemma map_add₃ (f : TriLinearSymm V) (S T L1 L2 : V) :
    f S T (L1 + L2) = f S T L1 + f S T L2 := by
  rw [f.swap₃, f.map_add₁, f.swap₃, f.swap₃ L2 T S]

/-- Fixing the second and third input vectors, the resulting linear map. -/
def toLinear₁  (f : TriLinearSymm V) (T L : V) : V →ₗ[ℚ] ℚ where
  toFun S := f S T L
  map_add' S1 S2 := by
    simp only [f.map_add₁]
  map_smul' a S := by
    simp only [f.map_smul₁]
    rfl

lemma toLinear₁_apply (f : TriLinearSymm V) (S T L : V) : f S T L = f.toLinear₁ T L S := rfl

lemma map_sum₁ {n : ℕ} (f : TriLinearSymm V) (S : Fin n → V) (T : V) (L : V) :
    f (∑ i, S i) T L = ∑ i, f (S i) T L := by
  rw [f.toLinear₁_apply]
  rw [map_sum]
  rfl

lemma map_sum₂ {n : ℕ} (f : TriLinearSymm V) (S : Fin n → V) (T : V) (L : V) :
    f T (∑ i, S i) L = ∑ i, f T (S i) L := by
  rw [swap₁, map_sum₁]
  apply Fintype.sum_congr
  intro i
  rw [swap₁]

lemma map_sum₃ {n : ℕ} (f : TriLinearSymm V) (S : Fin n → V) (T : V) (L : V) :
    f T L (∑ i, S i) = ∑ i, f T L (S i) := by
  rw [swap₃, map_sum₁]
  apply Fintype.sum_congr
  intro i
  rw [swap₃]

lemma map_sum₁₂₃ {n1 n2 n3 : ℕ} (f : TriLinearSymm V) (S : Fin n1 → V)
    (T : Fin n2 → V) (L : Fin n3 → V) :
    f (∑ i, S i) (∑ i, T i) (∑ i, L i) = ∑ i, ∑ k, ∑ l, f (S i) (T k) (L l) := by
  rw [map_sum₁]
  apply Fintype.sum_congr
  intro i
  rw [map_sum₂]
  apply Fintype.sum_congr
  intro i
  rw [map_sum₃]

/-- The homogenous cubic equation obtainable from a symmetric trilinear function. -/
@[simps!]
def toCubic {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) : HomogeneousCubic charges where
  toFun S := τ S S S
  map_smul' a S := by
    simp only [smul_eq_mul]
    rw [τ.map_smul₁, τ.map_smul₂, τ.map_smul₃]
    ring

lemma toCubic_add {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) (S T : charges) :
    τ.toCubic (S + T) = τ.toCubic S +
    τ.toCubic T + 3 * τ S S T + 3 * τ T T S := by
  simp only [HomogeneousCubic, toCubic_apply]
  rw [τ.map_add₁, τ.map_add₂, τ.map_add₂, τ.map_add₃, τ.map_add₃, τ.map_add₃, τ.map_add₃]
  rw [τ.swap₂ S T S, τ.swap₁ T S S, τ.swap₂ S T S, τ.swap₂ T S T, τ.swap₁ S T T, τ.swap₂ T S T]
  ring

end TriLinearSymm
