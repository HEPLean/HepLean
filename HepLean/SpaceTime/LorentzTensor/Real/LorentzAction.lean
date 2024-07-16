/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import HepLean.SpaceTime.LorentzGroup.Basic
/-!

# Lorentz group action on Real Lorentz Tensors

We define the action of the Lorentz group on Real Lorentz Tensors.

The Lorentz action is currently only defined for finite and decidable types `X`.

-/

namespace RealLorentzTensor

variable {d : ℕ} {X : Type} [Fintype X] [DecidableEq X] (T : RealLorentzTensor d X) (c : X → Colors)
variable (Λ Λ' : LorentzGroup d)
open LorentzGroup
open BigOperators

instance : Fintype (IndexValue d c) := Pi.fintype
variable {μ : Colors}

/-- Monoid homomorphism from the Lorentz group to matrices indexed by `ColorsIndex d μ` for a
  color `μ`.

  This can be thought of as the representation of the Lorentz group for that color index. -/
def colorMatrix (μ : Colors) : LorentzGroup d →* Matrix (ColorsIndex d μ) (ColorsIndex d μ) ℝ where
  toFun Λ := match μ with
    | .up => fun i j => Λ.1 i j
    | .down => fun i j => (LorentzGroup.transpose Λ⁻¹).1 i j
  map_one' := by
    match μ with
    | .up =>
        simp only [lorentzGroupIsGroup_one_coe]
        ext i j
        simp only [OfNat.ofNat, One.one, ColorsIndex]
        congr
    | .down =>
        simp only [transpose, inv_one, lorentzGroupIsGroup_one_coe, Matrix.transpose_one]
        ext i j
        simp only [OfNat.ofNat, One.one, ColorsIndex]
        congr
  map_mul' Λ Λ' := by
    match μ with
    | .up =>
        ext i j
        simp only [lorentzGroupIsGroup_mul_coe]
    | .down =>
        ext i j
        simp only [transpose, mul_inv_rev, lorentzGroupIsGroup_inv, lorentzGroupIsGroup_mul_coe,
          Matrix.transpose_mul, Matrix.transpose_apply]
        rfl

/-- A real number occuring in the action of the Lorentz group on Lorentz tensors. -/
@[simp]
def prodColorMatrixOnIndexValue (i j : IndexValue d c) : ℝ :=
  ∏ x, colorMatrix (c x) Λ (i x) (j x)

/-- `prodColorMatrixOnIndexValue` evaluated at `1` on the diagonal returns `1`. -/
lemma one_prodColorMatrixOnIndexValue_on_diag (i : IndexValue d c) :
    prodColorMatrixOnIndexValue c 1 i i = 1 := by
  simp only [prodColorMatrixOnIndexValue]
  rw [Finset.prod_eq_one]
  intro x _
  simp only [colorMatrix, MonoidHom.map_one, Matrix.one_apply]
  rfl

/-- `prodColorMatrixOnIndexValue` evaluated at `1` off the diagonal returns `0`. -/
lemma one_prodColorMatrixOnIndexValue_off_diag {i j : IndexValue d c} (hij : j ≠ i) :
    prodColorMatrixOnIndexValue c 1 i j = 0 := by
  simp only [prodColorMatrixOnIndexValue]
  obtain ⟨x, hijx⟩ := Function.ne_iff.mp hij
  rw [@Finset.prod_eq_zero _ _ _ _ _ x]
  exact Finset.mem_univ x
  simp only [map_one]
  exact Matrix.one_apply_ne' hijx

lemma mul_prodColorMatrixOnIndexValue (i j : IndexValue d c) :
    prodColorMatrixOnIndexValue c (Λ * Λ') i j =
    ∑ (k : IndexValue d c),
    ∏ x, (colorMatrix (c x) Λ (i x) (k x)) * (colorMatrix (c x) Λ' (k x) (j x)) := by
  have h1 : ∑ (k : IndexValue d c), ∏ x,
      (colorMatrix (c x) Λ (i x) (k x)) * (colorMatrix (c x) Λ' (k x) (j x)) =
      ∏ x, ∑ y, (colorMatrix (c x) Λ (i x) y) * (colorMatrix (c x) Λ' y (j x)) := by
    rw [Finset.prod_sum]
    simp only [Finset.prod_attach_univ, Finset.sum_univ_pi]
    apply Finset.sum_congr
    simp only [IndexValue, Fintype.piFinset_univ]
    intro x _
    rfl
  rw [h1]
  simp only [prodColorMatrixOnIndexValue, map_mul]
  exact Finset.prod_congr rfl (fun x _ => rfl)

/-- Action of the Lorentz group on `X`-indexed Real Lorentz Tensors. -/
@[simps!]
instance lorentzAction : MulAction (LorentzGroup d) (RealLorentzTensor d X) where
  smul Λ T := {color := T.color,
                coord := fun i => ∑ j, prodColorMatrixOnIndexValue T.color Λ i j * T.coord j}
  one_smul T := by
    refine ext' rfl ?_
    funext i
    simp only [HSMul.hSMul, map_one]
    erw [Finset.sum_eq_single_of_mem i]
    rw [one_prodColorMatrixOnIndexValue_on_diag]
    simp only [one_mul, IndexValue]
    rfl
    exact Finset.mem_univ i
    intro j _ hij
    rw [one_prodColorMatrixOnIndexValue_off_diag]
    simp only [zero_mul]
    exact hij
  mul_smul Λ Λ' T := by
    refine ext' rfl ?_
    simp only [HSMul.hSMul]
    funext i
    have h1 : ∑ j : IndexValue d T.color, prodColorMatrixOnIndexValue T.color (Λ * Λ') i j
        * T.coord j = ∑ j : IndexValue d T.color, ∑ (k : IndexValue d T.color),
        (∏ x, ((colorMatrix (T.color x) Λ (i x) (k x)) *
        (colorMatrix (T.color x) Λ' (k x) (j x)))) * T.coord j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_prodColorMatrixOnIndexValue, Finset.sum_mul]
    rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [prodColorMatrixOnIndexValue, IndexValue]
    rw [← mul_assoc]
    congr
    rw [Finset.prod_mul_distrib]
    rfl

@[simps!]
instance : MulAction (LorentzGroup d) (Marked d X n) := lorentzAction

end RealLorentzTensor
