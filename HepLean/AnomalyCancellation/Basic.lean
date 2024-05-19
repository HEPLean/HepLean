/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.LinearMaps
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
/-!
# Basic set up for anomaly cancellation conditions

This file defines the basic structures for the anomaly cancellation conditions.

It defines a module structure on the charges, and the solutions to the linear ACCs.

## TODO

- Derive ACC systems from gauge algebras and fermionic representations.
- Relate ACCSystems to algebraic varities.

-/

/-- A system of charges, specified by the number of charges. -/
structure ACCSystemCharges where
  /-- The number of charges. -/
  numberCharges : ℕ

/--
  Creates an `ACCSystemCharges` object with the specified number of charges.
-/
def ACCSystemChargesMk (n : ℕ) : ACCSystemCharges where
  numberCharges := n

namespace ACCSystemCharges

/-- The charges as functions from `Fin χ.numberCharges → ℚ`. -/
def charges (χ : ACCSystemCharges) : Type := Fin χ.numberCharges → ℚ

/--
  An instance to provide the necessary operations and properties for `charges` to form an additive
  commutative monoid.
-/
@[simps!]
instance chargesAddCommMonoid (χ : ACCSystemCharges) : AddCommMonoid χ.charges :=
  Pi.addCommMonoid

/--
  An instance to provide the necessary operations and properties for `charges` to form a module over
  the field `ℚ`.
-/
@[simps!]
instance chargesModule (χ : ACCSystemCharges) : Module ℚ χ.charges :=
  Pi.module _ _ _

/--
  An instance provides the necessary operations and properties for `charges` to form an additive
  commutative group.
-/
instance ChargesAddCommGroup (χ : ACCSystemCharges) : AddCommGroup χ.charges :=
  Module.addCommMonoidToAddCommGroup ℚ

instance (χ : ACCSystemCharges) : Module.Finite ℚ χ.charges :=
  FiniteDimensional.finiteDimensional_pi ℚ

end ACCSystemCharges

/-- The type of charges plus the linear ACCs. -/
structure ACCSystemLinear extends ACCSystemCharges where
  /-- The number of linear ACCs. -/
  numberLinear : ℕ
  /-- The linear ACCs. -/
  linearACCs : Fin numberLinear → (toACCSystemCharges.charges →ₗ[ℚ] ℚ)

namespace ACCSystemLinear

/-- The type of solutions to the linear ACCs. -/
structure LinSols (χ : ACCSystemLinear) where
  /-- The underlying charge. -/
  val : χ.1.charges
  /-- The condition that the charge satisfies the linear ACCs. -/
  linearSol : ∀ i : Fin χ.numberLinear, χ.linearACCs i val = 0

/-- Two solutions are equal if the underlying charges are equal. -/
@[ext]
lemma LinSols.ext {χ : ACCSystemLinear} {S T : χ.LinSols} (h : S.val = T.val) : S = T := by
  cases' S
  simp_all only

/-- An instance providng the operations and properties for `LinSols` to form an
  addative commutative monoid. -/
@[simps!]
instance linSolsAddCommMonoid (χ : ACCSystemLinear) :
    AddCommMonoid χ.LinSols where
  add S T := ⟨S.val + T.val, by
    intro i
    rw [(χ.linearACCs i).map_add, S.linearSol i, T.linearSol i]
    rfl⟩
  add_comm S T := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.add_comm _ _
  add_assoc S T L := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.add_assoc _ _ _
  zero := ⟨χ.chargesAddCommMonoid.zero, by
    intro i
    erw [(χ.linearACCs i).map_zero]⟩
  zero_add S := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.zero_add _
  add_zero S := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.add_zero _
  nsmul n S := ⟨n  • S.val, by
    intro i
    rw [nsmul_eq_smul_cast ℚ]
    erw [(χ.linearACCs i).map_smul, S.linearSol i]
    simp⟩
  nsmul_zero n := by
    rfl
  nsmul_succ n S := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.nsmul_succ _ _

/-- An instance providng the operations and properties for `LinSols` to form an
  module over `ℚ`. -/
@[simps!]
instance linSolsModule  (χ : ACCSystemLinear) : Module ℚ χ.LinSols where
  smul a S := ⟨a • S.val, by
    intro i
    rw [(χ.linearACCs i).map_smul, S.linearSol i]
    simp⟩
  one_smul one_smul := by
    apply LinSols.ext
    exact χ.chargesModule.one_smul _
  mul_smul a b S := by
    apply LinSols.ext
    exact χ.chargesModule.mul_smul _ _ _
  smul_zero a := by
    apply LinSols.ext
    exact χ.chargesModule.smul_zero _
  zero_smul S := by
    apply LinSols.ext
    exact χ.chargesModule.zero_smul _
  smul_add a S T := by
    apply LinSols.ext
    exact χ.chargesModule.smul_add _ _ _
  add_smul a b T:= by
    apply LinSols.ext
    exact χ.chargesModule.add_smul _ _ _

/-- An instance providing the operations and properties for `LinSols` to form an
  an addative community. -/
instance linSolsAddCommGroup (χ : ACCSystemLinear) : AddCommGroup χ.LinSols :=
  Module.addCommMonoidToAddCommGroup ℚ

/-- The inclusion of `LinSols` into `charges`. -/
def linSolsIncl (χ : ACCSystemLinear) : χ.LinSols →ₗ[ℚ] χ.charges where
  toFun S := S.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ACCSystemLinear

/-- The type of charges plus the linear ACCs plus the quadratic ACCs. -/
structure ACCSystemQuad extends ACCSystemLinear where
  /-- The number of quadratic ACCs. -/
  numberQuadratic : ℕ
  /-- The quadratic ACCs. -/
  quadraticACCs : Fin numberQuadratic → HomogeneousQuadratic toACCSystemCharges.charges

namespace ACCSystemQuad

/-- The type of solutions to the linear and quadratic ACCs. -/
structure QuadSols (χ : ACCSystemQuad) extends χ.LinSols where
  /-- The condition that the charge satisfies the quadratic ACCs. -/
  quadSol : ∀ i : Fin χ.numberQuadratic, (χ.quadraticACCs i) val = 0

/-- Two `QuadSols` are equal if the underlying charges are equal. -/
@[ext]
lemma QuadSols.ext {χ : ACCSystemQuad} {S T : χ.QuadSols} (h : S.val = T.val) :
    S = T := by
  have h  := ACCSystemLinear.LinSols.ext h
  cases' S
  simp_all only

/-- An instance giving the properties and structures to define an action of `ℚ` on `QuadSols`. -/
instance quadSolsMulAction (χ : ACCSystemQuad) : MulAction ℚ χ.QuadSols where
  smul a S :=  ⟨a • S.toLinSols , by
    intro i
    erw [(χ.quadraticACCs i).map_smul]
    rw [S.quadSol i]
    simp only [mul_zero]
    ⟩
  mul_smul a b S := by
    apply QuadSols.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply QuadSols.ext
    exact one_smul _ _

/-- The inclusion of quadratic solutions into linear solutions. -/
def quadSolsInclLinSols (χ : ACCSystemQuad) : χ.QuadSols →[ℚ] χ.LinSols  where
  toFun  := QuadSols.toLinSols
  map_smul' _ _ := rfl

/-- If there are no quadratic equations (i.e. no U(1)'s in the underlying gauge group. The inclusion
  of linear solutions into quadratic solutions. -/
def linSolsInclQuadSolsZero (χ : ACCSystemQuad) (h : χ.numberQuadratic = 0) :
    χ.LinSols →[ℚ] χ.QuadSols where
  toFun S := ⟨S, by intro i; rw [h] at i; exact Fin.elim0 i⟩
  map_smul' _ _ := rfl

/-- The inclusion of quadratic solutions into all charges. -/
def quadSolsIncl (χ : ACCSystemQuad) : χ.QuadSols →[ℚ] χ.charges :=
  MulActionHom.comp χ.linSolsIncl.toMulActionHom χ.quadSolsInclLinSols

end ACCSystemQuad

/-- The type of charges plus the anomaly cancellation conditions. -/
structure ACCSystem extends ACCSystemQuad where
  /-- The cubic ACC. -/
  cubicACC : HomogeneousCubic toACCSystemCharges.charges

namespace ACCSystem

/-- The type of solutions to the anomaly cancellation conditions. -/
structure Sols (χ : ACCSystem) extends χ.QuadSols where
  /-- The condition that the charge satisfies the cubic ACC. -/
  cubicSol : χ.cubicACC val = 0

/-- Two solutions are equal if the underlying charges are equal. -/
lemma Sols.ext {χ : ACCSystem} {S T : χ.Sols} (h : S.val = T.val) :
    S = T := by
  have h  := ACCSystemQuad.QuadSols.ext h
  cases' S
  simp_all only

/-- We say a charge S is a solution if it extends to a solution. -/
def isSolution (χ : ACCSystem) (S : χ.charges) : Prop :=
 ∃ (sol : χ.Sols), sol.val = S

/-- An instance giving the properties and structures to define an action of `ℚ` on `Sols`. -/
instance solsMulAction (χ : ACCSystem) : MulAction ℚ χ.Sols where
  smul a S :=  ⟨a • S.toQuadSols , by
    erw [(χ.cubicACC).map_smul]
    rw [S.cubicSol]
    simp⟩
  mul_smul a b S := by
    apply Sols.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply Sols.ext
    exact one_smul _ _

/-- The inclusion of `Sols` into `QuadSols`. -/
def solsInclQuadSols (χ : ACCSystem) : χ.Sols →[ℚ] χ.QuadSols  where
  toFun  := Sols.toQuadSols
  map_smul' _ _ := rfl

/-- The inclusion of `Sols` into `LinSols`. -/
def solsInclLinSols (χ : ACCSystem) : χ.Sols →[ℚ] χ.LinSols :=
  MulActionHom.comp χ.quadSolsInclLinSols χ.solsInclQuadSols

/-- The inclusion of `Sols` into `LinSols`. -/
def solsIncl (χ : ACCSystem) : χ.Sols →[ℚ] χ.charges :=
  MulActionHom.comp χ.quadSolsIncl χ.solsInclQuadSols

/-- The structure of a map between two ACCSystems. -/
structure Hom (χ η : ACCSystem) where
  /-- The linear map between vector spaces of charges. -/
  charges : χ.charges →ₗ[ℚ] η.charges
  /-- The map between solutions. -/
  anomalyFree : χ.Sols → η.Sols
  /-- The condition that the map commutes with the relevent inclusions. -/
  commute : charges ∘ χ.solsIncl = η.solsIncl ∘ anomalyFree

/-- The definition of composition between two ACCSystems. -/
def Hom.comp {χ η ε : ACCSystem} (g : Hom η ε) (f : Hom χ η) : Hom χ ε where
  charges := LinearMap.comp g.charges f.charges
  anomalyFree := g.anomalyFree ∘ f.anomalyFree
  commute := by
    simp only [LinearMap.coe_comp]
    rw [Function.comp.assoc]
    rw [f.commute, ← Function.comp.assoc, g.commute, Function.comp.assoc]

end ACCSystem
