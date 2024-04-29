/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.PhaseFreedom
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Matrix Complex
open ComplexConjugate
open CKMMatrix


noncomputable section
namespace Invariant


@[simps!]
def jarlskogℂCKM (V : CKMMatrix) : ℂ :=
  [V]us * [V]cb * conj [V]ub * conj [V]cs

lemma jarlskogℂCKM_equiv  (V U : CKMMatrix) (h : V ≈ U) :
    jarlskogℂCKM V = jarlskogℂCKM U := by
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  change V = phaseShiftApply U a b c e f g  at h
  rw [h]
  simp only [jarlskogℂCKM, Fin.isValue, phaseShiftApply.ub,
  phaseShiftApply.us, phaseShiftApply.cb, phaseShiftApply.cs]
  simp [← exp_conj, conj_ofReal, exp_add, exp_neg]
  have ha : cexp (↑a * I) ≠ 0 := exp_ne_zero _
  have hb : cexp (↑b * I) ≠ 0 := exp_ne_zero _
  have hf : cexp (↑f * I) ≠ 0 := exp_ne_zero _
  have hg : cexp (↑g * I) ≠ 0 := exp_ne_zero _
  field_simp
  ring

@[simp]
def jarlskogℂ : Quotient CKMMatrixSetoid → ℂ :=
  Quotient.lift jarlskogℂCKM jarlskogℂCKM_equiv

def VusVubVcdSq (V : Quotient CKMMatrixSetoid) : ℝ  :=
    VusAbs V ^ 2 * VubAbs V ^ 2  * VcbAbs V ^2 / (VudAbs V ^ 2 + VusAbs V ^2)

def mulExpδ₃ (V : Quotient CKMMatrixSetoid) : ℂ :=
  jarlskogℂ V + VusVubVcdSq V


end Invariant
end
