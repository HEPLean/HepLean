/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.Species.Basic
public import PhyslibAlpha.Relativity.IsLorentzDeriv
/-!
# The Lorentz law of the symbols of a species

The Lorentz transformation law of the symbols of a species, for matter and the gauge field.

## i. Overview

Lorentz transformations act here through `SL(2,ℂ)` and its map `SL2C.toLorentzGroup` to the
Lorentz group. The group acts on the values of every species, on the complex value space of a
matter field through its representation `MatterField.repLorentz`, and on the real space
`CoVector ⊗ 𝔤` of the connection through `GaugeBoson.repLorentzGroup`, which moves the spacetime
index alone. The labels of symbols are covectors of the value space, so they transform
contragrediently, `ℓ ↦ ℓ ∘ ρ(Λ⁻¹)`, that is, by the dual representation.

A second Lorentz action, `repLorentz`, acts on the target algebra containing the symbols. The
Lorentz law `Species.LorentzLaw` requires transforming an algebra-valued symbol by `repLorentz` to
agree with transforming its component label and its derivative indices, the derivative indices
mixing by the Lorentz matrix. For families linear in the label the law is equivalent to
`Lorentz.IsLorentzDerivTransforms`, over `ℂ` for matter and over `ℝ` for the connection.

## ii. Key results

- `Species.lorentzLabel` : the Lorentz action on the labels of a species.
- `Species.LorentzLaw` : the Lorentz law of a symbol family of a species in any algebra.
- `Species.LorentzLaw.neg_one_apply` : at `-1` the derivative indices do not mix.
- `MatterField.lorentzLaw_iff` : for matter the law is `Lorentz.IsLorentzDerivTransforms`.
- `Species.lorentzLaw_gauge_iff` : for the gauge field the law is
  `Lorentz.IsLorentzDerivTransforms` over the reals.
- `Species.LorentzLaw.connection_components` : the Lorentz law of the connection in components.
- `Species.LorentzLaw.of_derivLaw` : the Lorentz law of the derivatives of underived symbols.

## iii. Table of contents

- A. The Lorentz action on labels
- B. The Lorentz law of a symbol family
- C. Matter fields
- D. The connection
- E. Lorentz law for ordinary derivatives

## iv. References

* None.

-/

@[expose] public section

open Lorentz MatrixGroups

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

namespace Species

/-!

## A. The Lorentz action on labels

-/

/-- The Lorentz action on the labels of a species, contragredient to its action on values. -/
noncomputable def lorentzLabel : (σ : Species jets) → SL(2,ℂ) → σ.Label → σ.Label
  | matter M, Λ, φ => M.repLorentz.dual Λ φ
  | gauge, Λ, ω => (GaugeBoson.repLorentzGroup 𝔤).dual Λ ω

@[simp] lemma lorentzLabel_matter (M : MatterField jets) (Λ : SL(2,ℂ))
    (φ : Module.Dual ℂ M.V) :
    (M : Species jets).lorentzLabel Λ φ = M.repLorentz.dual Λ φ := rfl

@[simp] lemma lorentzLabel_gauge (Λ : SL(2,ℂ)) (ω : Module.Dual ℝ (GaugeBoson 𝔤)) :
    (gauge : Species jets).lorentzLabel Λ ω = (GaugeBoson.repLorentzGroup 𝔤).dual Λ ω :=
  rfl

/-- The label action of a product is the composite of the label actions. -/
lemma lorentzLabel_mul (σ : Species jets) (Λ₁ Λ₂ : SL(2,ℂ)) (ℓ : σ.Label) :
    σ.lorentzLabel (Λ₁ * Λ₂) ℓ = σ.lorentzLabel Λ₁ (σ.lorentzLabel Λ₂ ℓ) := by
  cases σ with
  | matter M => exact LinearMap.congr_fun (map_mul M.repLorentz.dual Λ₁ Λ₂) ℓ
  | gauge => exact LinearMap.congr_fun (map_mul (GaugeBoson.repLorentzGroup 𝔤).dual Λ₁ Λ₂) ℓ

/-- The identity fixes every label. -/
lemma lorentzLabel_one (σ : Species jets) (ℓ : σ.Label) : σ.lorentzLabel 1 ℓ = ℓ := by
  cases σ with
  | matter M => exact LinearMap.congr_fun (map_one M.repLorentz.dual) ℓ
  | gauge => exact LinearMap.congr_fun (map_one (GaugeBoson.repLorentzGroup 𝔤).dual) ℓ

/-!

## B. The Lorentz law of a symbol family

An expression with `n` ordinary derivatives has `n` spacetime indices, and each index contributes
one Lorentz matrix factor. The law therefore lists the directions as an ordered tuple
`l : Fin n → Fin 1 ⊕ Fin 3`, whose entry `l i` is the direction of the `i`-th derivative. The
symbol at `l` is `F (List.ofFn l) ℓ`, which depends only on the multiset underlying `l`, as
ordinary derivatives commute. Under `Λ` it becomes a sum over all tuples `p`, weighted by the
product over `i` of the Lorentz matrix entries at `(p i, l i)`, while its label
moves by `lorentzLabel`. Iterated covariant derivatives, which need not commute, are indexed by
the ordered tuple itself, as in `GaugeAlgebraRealization.covDerivIter`.

-/

section LorentzLaw

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The Lorentz law of a symbol family, under a Lorentz action `repLorentz` on the
  algebra. -/
def LorentzLaw (σ : Species jets) (repLorentz : Representation ℂ SL(2,ℂ) B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label),
    repLorentz Λ (F (List.ofFn l) ℓ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          F (List.ofFn p) (σ.lorentzLabel Λ ℓ)

/-- At `-1`, which covers the identity Lorentz transformation, only the label moves. -/
lemma LorentzLaw.neg_one_apply {σ : Species jets} {repLorentz : Representation ℂ SL(2,ℂ) B}
    {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B} (hF : σ.LorentzLaw repLorentz F) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label) :
    repLorentz (-1) (F (List.ofFn l) ℓ) = F (List.ofFn l) (σ.lorentzLabel (-1) ℓ) := by
  rw [hF (-1) n l ℓ, SL2C.toLorentzGroup_neg_one, Finset.sum_eq_single l]
  · simp
  · intro p _ hp
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hp
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · simp [hi]
  · simp

end LorentzLaw

end Species

/-!

## C. Matter fields

-/

namespace MatterField

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- For matter the Lorentz law is `Lorentz.IsLorentzDerivTransforms` of the matter field's
  representation, for a family complex-linear in the label. -/
lemma lorentzLaw_iff (M : MatterField jets)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ M.V →ₗ[ℂ] B) :
    (M : Species jets).LorentzLaw repLorentz (fun s φ => F s φ)
      ↔ IsLorentzDerivTransforms repLorentz M.repLorentz F :=
  Iff.rfl

end MatterField

/-!

## D. The connection

Here `A_μ^a` denotes the label `GaugeBoson.componentCovector 𝔤 μ a`, the covector selecting the
`μ`-th spacetime component of the connection paired with the gauge-algebra covector `a`. Under a
Lorentz transformation this label moves by the column of the Lorentz matrix at `μ`. For a family
real-linear in the label the law therefore gives one matrix factor per derivative and one
for the spacetime index of the field, the formula of `GaugeAlgebraRealization.lorentz_apply`.

-/

namespace Species

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- For the gauge field the Lorentz law is `Lorentz.IsLorentzDerivTransforms` over the
  reals, for a family real-linear in the label. -/
lemma lorentzLaw_gauge_iff
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ (GaugeBoson 𝔤) →ₗ[ℝ] B) :
    (gauge : Species jets).LorentzLaw repLorentz (fun s ω => F s ω)
      ↔ IsLorentzDerivTransforms (k := ℝ) repLorentz (GaugeBoson.repLorentzGroup 𝔤) F :=
  Iff.rfl

/-- The Lorentz law of the connection at the component covectors `A_μ^a`. -/
lemma LorentzLaw.connection_components {F : Multiset (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ (GaugeBoson 𝔤) → B} (hF : (gauge : Species jets).LorentzLaw repLorentz F)
    (hlin : (gauge : Species jets).LabelLinear F) (Λ : SL(2,ℂ)) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (a : Module.Dual ℝ 𝔤) :
    repLorentz Λ (F (List.ofFn l) (GaugeBoson.componentCovector 𝔤 μ a)) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          ∑ b, (((SL2C.toLorentzGroup Λ).1 b μ : ℝ) : ℂ) •
            F (List.ofFn p) (GaugeBoson.componentCovector 𝔤 b a) := by
  rw [hF Λ n l, lorentzLabel_gauge, GaugeBoson.repLorentzGroup_dual_componentCovector]
  refine Finset.sum_congr rfl fun p _ => congrArg _ ?_
  have hsum := map_sum (IsLinearMap.mk' _ (hlin (List.ofFn p)))
    (fun b => (SL2C.toLorentzGroup Λ).1 b μ • GaugeBoson.componentCovector 𝔤 b a) Finset.univ
  simp only [IsLinearMap.mk'_apply] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun b _ => ((hlin _).map_smul _ _).trans (Complex.coe_smul _ _).symm

end Species

/-!

## E. Lorentz law for ordinary derivatives

-/

namespace Species

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The Lorentz law follows from that of the underived symbols when the symbols obey the
  derivative law of a Lorentz derivative with commuting components. -/
lemma LorentzLaw.of_derivLaw {σ : Species jets} {D : Fin 1 ⊕ Fin 3 → B →ₗ[ℂ] B}
    [IsLorentzDeriv repLorentz D] (hD : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ))
    {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B} (hF : σ.DerivLaw (fun μ => D μ) F)
    (h0 : ∀ Λ ℓ, repLorentz Λ (F 0 ℓ) = F 0 (σ.lorentzLabel Λ ℓ)) :
    σ.LorentzLaw repLorentz F := by
  have hit := (derivLaw_iff_eq_iteratedD hD).mp hF
  intro Λ n l ℓ
  rw [hit (List.ofFn l) ℓ, IsLorentzDeriv.rep_iteratedD_ofFn hD, h0]
  exact Finset.sum_congr rfl fun p _ => by rw [← hit]

end Species
