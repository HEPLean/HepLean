/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.RepCoeff
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.TransformsIn
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeCoeff
public import PhyslibAlpha.Relativity.IsLorentzDeriv
/-!
# Species of a gauge theory

The matter and gauge-field species of a gauge theory, and the laws of their symbols.

## i. Overview

For fixed local gauge data `jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J`, `Species jets` describes either a
matter field, given by its `MatterField` data, or the gauge field. It lets us state transformation
laws for their field components and derivatives in a common form.

Under a gauge transformation the derivatives of a matter field transform linearly, whereas those
of the gauge field also acquire an additive term from the Maurer–Cartan form. The common gauge
law therefore has coefficients acting on labels and an inhomogeneous term, zero for matter, whose
composition laws are proved here. The file also states the weight and derivative laws of a symbol
family. For a matter field the gauge law is `LocalGaugeData.TransformsIn`. The Lorentz law is in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.Species.Lorentz`.

## ii. Key results

- `Species` : the species associated with local gauge data, `matter M` for a matter field `M`
  or `gauge`.
- `Species.statistic` : the declared statistics of a matter field; bosonic for the gauge field.
- `Species.coeff`, `Species.inhomogeneousTerm` : the coefficients and the inhomogeneous term
  of the gauge law.
- `Species.coeff_mul`, `Species.coeff_one`, `Species.inhomogeneousTerm_mul`,
  `Species.inhomogeneousTerm_one` : the composition laws of the coefficients of the gauge law.
- `Species.GaugeLaw`, `Species.WeightLaw` : the gauge and weight laws of a symbol family in an
  algebra with a gauge action or a scaling.
- `Species.GaugeLaw.map` : the gauge law is carried along equivariant algebra maps.
- `Species.LabelLinear` : linearity of a symbol family in its label.
- `Species.DerivLaw` : the derivative law of a symbol family against a supplied derivative.
- `Species.derivLaw_iff_eq_iteratedD` : for commuting linear derivatives, the symbols are the
  iterated derivatives of the underived ones.
- `MatterField.gaugeLaw_iff` : for matter the gauge law is `LocalGaugeData.TransformsIn`.
- `Species.GaugeLaw.connection_components` : the gauge law of the connection in components.

## iii. Table of contents

- A. Matter fields and the gauge field
- B. Species data and transformation coefficients
- C. The composition laws of the coefficients
- D. Laws of a symbol family in an arbitrary algebra
  - D.1. The gauge and weight laws
  - D.2. Linearity in the label
  - D.3. Ordinary derivatives
- E. Matter fields as species
- F. The connection in components

## iv. References

* None.

-/

@[expose] public section

open GaugeAlgebraRealization LocalGaugeFieldAlgebra TensorProduct

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-!

## A. Matter fields and the gauge field

The matter case contains a `MatterField`, which supplies the value space, the Lorentz and gauge
representations, the infinitesimal action, the mass weight and the declared statistics. The
gauge constructor takes no parameters, since the local gauge data determine the value space
`CoVector ⊗ 𝔤` of the gauge field and its transformations, so `Species jets` has one gauge-field
species.

-/

/-- A species associated with local gauge data, a matter field or the gauge field. -/
inductive Species (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) : Type 1
  /-- A matter field, given by its `MatterField` data. -/
  | matter (M : MatterField jets)
  /-- The gauge field, whose symbols are the components of the connection. -/
  | gauge

instance : Coe (MatterField jets) (Species jets) := ⟨Species.matter⟩

namespace Species

/-!

## B. Species data and transformation coefficients

A label `ℓ : σ.Label` is a covector that selects a component or a linear combination of
components of a field of species `σ`. In a target algebra `B`, the symbol `F s ℓ` stands for the
corresponding iterated derivative, with directions recorded by `s`, written `∂^s σ^ℓ`. `DerivLaw`
of section D.3 relates these symbols to derivative operations on `B`.

Every species has a mass weight, twice its mass dimension, and declared statistics. The gauge
field has mass weight two and is bosonic. 

A derivative of the transformed field expands by the Leibniz rule into derivatives of the same or
lower order. The
coefficients `coeff` of this expansion act on labels, by `repDualCoeff` for matter and by the
dual adjoint transport for the gauge field. For the gauge field, the label evaluates the
Maurer–Cartan derivative coefficient `mcBosonCoeff`, valued in `CoVector ⊗ 𝔤`, to give the scalar
additive term in the symbol law, which `GaugeLaw` multiplies by the unit of `B`. For matter this
inhomogeneous term is zero.

-/

/-- The statistics of a species, declared by a matter field and bosonic for the gauge field. -/
def statistic : Species jets → FieldStatistic
  | matter M => M.statistic
  | gauge => .bosonic

/-- The mass weight of a species, twice its mass dimension. -/
def massWeight : Species jets → ℕ
  | matter M => M.massWeight
  | gauge => 2

/-- The value space of a species. -/
abbrev Value : Species jets → Type
  | matter M => M.V
  | gauge => GaugeBoson 𝔤

/-- The labels of the symbols of a species, the covectors of its value space. -/
abbrev Label : Species jets → Type
  | matter M => Module.Dual ℂ M.V
  | gauge => Module.Dual ℝ (GaugeBoson 𝔤)

/-- The labels of a species form an additive group. -/
noncomputable instance instAddCommGroupLabel : (σ : Species jets) → AddCommGroup σ.Label
  | matter _ => inferInstance
  | gauge => inferInstance

/-- The coefficients of the gauge law, acting on labels. -/
noncomputable def coeff : (σ : Species jets) → GJ → Multiset (Fin 1 ⊕ Fin 3) → σ.Label → σ.Label
  | matter M, U, p, φ => repDualCoeff M.repJet U p φ
  | gauge, U, p, ω => (GaugeBoson.adjointTransport jets U p).dualMap ω

/-- The inhomogeneous term of the gauge law, the component of its additive term selected by a
  label. -/
noncomputable def inhomogeneousTerm :
    (σ : Species jets) → GJ → Multiset (Fin 1 ⊕ Fin 3) → σ.Label → ℝ
  | matter _, _, _, _ => 0
  | gauge, U, s, ω => ω (mcBosonCoeff jets U s)

section ConstructorLemmas

variable (M : MatterField jets) (U : GJ) (p : Multiset (Fin 1 ⊕ Fin 3))

@[simp] lemma statistic_matter : (M : Species jets).statistic = M.statistic := rfl

@[simp] lemma statistic_gauge : (gauge : Species jets).statistic = .bosonic := rfl

@[simp] lemma massWeight_matter : (M : Species jets).massWeight = M.massWeight := rfl

@[simp] lemma massWeight_gauge : (gauge : Species jets).massWeight = 2 := rfl

@[simp] lemma coeff_matter (φ : Module.Dual ℂ M.V) :
    (M : Species jets).coeff U p φ = repDualCoeff M.repJet U p φ := rfl

@[simp] lemma coeff_gauge (ω : Module.Dual ℝ (GaugeBoson 𝔤)) :
    (gauge : Species jets).coeff U p ω = (GaugeBoson.adjointTransport jets U p).dualMap ω :=
  rfl

@[simp] lemma inhomogeneousTerm_matter (φ : Module.Dual ℂ M.V) :
    (M : Species jets).inhomogeneousTerm U p φ = 0 := rfl

@[simp] lemma inhomogeneousTerm_gauge (ω : Module.Dual ℝ (GaugeBoson 𝔤)) :
    (gauge : Species jets).inhomogeneousTerm U p ω = ω (mcBosonCoeff jets U p) := rfl

end ConstructorLemmas

/-!

## C. The composition laws of the coefficients

The following lemmas prove how the coefficients and inhomogeneous term combine under
multiplication of gauge transformations, and their values at the identity. Through the symbol law
`GaugeLaw`, these identities express agreement between successive transformations and their
product, given label linearity and preservation of the unit by the action. The coefficients of a
product are a Leibniz convolution, the sum over all ways of distributing the derivative directions
between the two factors (the splits in `Multiset.antidiagonal`), with the multiplicities of the
Leibniz rule.

-/

/-- The coefficients of a product compose by Leibniz convolution. -/
lemma coeff_mul (σ : Species jets) (W X : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label) :
    σ.coeff (W * X) x ℓ = (x.antidiagonal.map fun p => σ.coeff X p.2 (σ.coeff W p.1 ℓ)).sum := by
  cases σ with
  | matter M => exact repDualCoeff_mul M.repJet_smul W X x ℓ
  | gauge =>
    show (GaugeBoson.adjointTransport jets (W * X) x).dualMap ℓ
      = (x.antidiagonal.map fun p => (GaugeBoson.adjointTransport jets X p.2).dualMap
          ((GaugeBoson.adjointTransport jets W p.1).dualMap ℓ)).sum
    rw [GaugeBoson.adjointTransport_mul]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.dualMap_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
      map_multiset_sum, Function.comp_apply, LinearMap.comp_apply]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => rfl)

/-- At the identity the zeroth coefficient is the identity and the higher derivative
  coefficients vanish. -/
lemma coeff_one (σ : Species jets) (x : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label) :
    σ.coeff 1 x ℓ = if x = 0 then ℓ else 0 := by
  cases σ with
  | matter _ => exact repDualCoeff_one x ℓ
  | gauge =>
    show (GaugeBoson.adjointTransport jets 1 x).dualMap ℓ = if x = 0 then ℓ else 0
    rw [GaugeBoson.adjointTransport_one]
    by_cases hx : x = 0
    · rw [ite_eq_left hx, ite_eq_left hx]
      exact LinearMap.ext fun v => rfl
    · rw [ite_eq_right hx, ite_eq_right hx]
      exact LinearMap.ext fun v => map_zero ℓ

/-- The inhomogeneous term is a cocycle, the term of a product being the term of the first
  factor plus the term of the second read through the coefficients of the first. -/
lemma inhomogeneousTerm_mul (σ : Species jets) (W X : GJ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ℓ : σ.Label) :
    σ.inhomogeneousTerm (W * X) s ℓ = σ.inhomogeneousTerm W s ℓ
      + (s.antidiagonal.map fun p => σ.inhomogeneousTerm X p.2 (σ.coeff W p.1 ℓ)).sum := by
  cases σ with
  | matter _ =>
    show (0 : ℝ) = 0 + (s.antidiagonal.map fun _ => (0 : ℝ)).sum
    simp
  | gauge =>
    show ℓ (mcBosonCoeff jets (W * X) s) = ℓ (mcBosonCoeff jets W s)
      + (s.antidiagonal.map fun p =>
          ((GaugeBoson.adjointTransport jets W p.1).dualMap ℓ) (mcBosonCoeff jets X p.2)).sum
    rw [mcBosonCoeff_mul, map_add, map_multiset_sum, Multiset.map_map]
    rfl

/-- The identity has no inhomogeneous term. -/
lemma inhomogeneousTerm_one (σ : Species jets) (s : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label) :
    σ.inhomogeneousTerm 1 s ℓ = 0 := by
  cases σ with
  | matter _ => rfl
  | gauge =>
    show ℓ (mcBosonCoeff jets 1 s) = 0
    rw [mcBosonCoeff_one, map_zero]

/-!

## D. Laws of a symbol family in an arbitrary algebra

Each law below constrains a symbol family `F` in an algebra `B` relative to a gauge action, a
scaling or derivative operations supplied on `B`, in one statement for matter and the gauge field.

### D.1. The gauge and weight laws

-/

section SymbolLaws

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The gauge law of a symbol family, under which each symbol transforms by the coefficients
  and the inhomogeneous term of the inverse jet. -/
def GaugeLaw (σ : Species jets) (repGauge : Representation ℂ GJ B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B) : Prop :=
  ∀ (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label),
    repGauge U (F s ℓ) = (s.antidiagonal.map fun p => F p.2 (σ.coeff U⁻¹ p.1 ℓ)).sum
      + ((σ.inhomogeneousTerm U⁻¹ s ℓ : ℝ) : ℂ) • 1

/-- The weight law of a symbol family, under which `∂^s σ^ℓ` has the mass weight of the
  species plus two per derivative. -/
def WeightLaw (σ : Species jets) (scale : ℝ → B → B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B) : Prop :=
  ∀ (c : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label),
    scale c (F s ℓ) = ((c : ℂ) ^ (σ.massWeight + 2 * Multiset.card s)) • F s ℓ

/-- An underived symbol has the weight of its species. -/
lemma WeightLaw.zero {σ : Species jets} {scale : ℝ → B → B}
    {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B} (hF : σ.WeightLaw scale F) {w : ℕ}
    (hw : σ.massWeight = w) (c : ℝ) (ℓ : σ.Label) :
    scale c (F 0 ℓ) = ((c : ℂ) ^ w) • F 0 ℓ := by
  rw [hF c 0 ℓ, Multiset.card_zero, Nat.mul_zero, Nat.add_zero, hw]

/-- The gauge law is carried along any equivariant algebra map. -/
lemma GaugeLaw.map {B' : Type} [Ring B'] [Algebra ℂ B'] {repGauge : Representation ℂ GJ B}
    {repGauge' : Representation ℂ GJ B'} {σ : Species jets}
    {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B} (hF : σ.GaugeLaw repGauge F) (Φ : B →ₐ[ℂ] B')
    (hΦ : ∀ (U : GJ) (b : B), Φ (repGauge U b) = repGauge' U (Φ b)) :
    σ.GaugeLaw repGauge' (fun s ℓ => Φ (F s ℓ)) := by
  intro U s ℓ
  rw [← hΦ, hF U s ℓ, map_add, map_smul, map_one, map_multiset_sum, Multiset.map_map]
  rfl

/-!

### D.2. Linearity in the label

-/

/-- Linearity of a symbol family in its label, complex-linear for matter and real-linear for
  the gauge field. -/
def LabelLinear : (σ : Species jets) → (Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B) → Prop
  | matter _, F => ∀ s, IsLinearMap ℂ (F s)
  | gauge, F => ∀ s, IsLinearMap ℝ (F s)

/-- A linear family takes a sum of labels to the sum of the symbols, for every species. -/
lemma LabelLinear.map_add {σ : Species jets} {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B}
    (hF : σ.LabelLinear F) (s : Multiset (Fin 1 ⊕ Fin 3)) (x y : σ.Label) :
    F s (x + y) = F s x + F s y := by
  cases σ with
  | matter _ => exact (hF s).map_add x y
  | gauge => exact (hF s).map_add x y

end SymbolLaws

/-!

### D.3. Ordinary derivatives

The derivative law reads the index of a symbol as ordinary derivatives. Here `D μ` acts on the
target algebra `B`. Derivative indices are multisets, so the `D μ` commute on symbols obeying the
law, as partial derivatives of a smooth field do. When the supplied operations `D μ` are linear and
commute, `DerivLaw` says that `F s ℓ` is obtained by repeatedly applying them to `F 0 ℓ`. The
existing function `Lorentz.iteratedD` expresses this repeated application.

-/

section OrdinaryDerivatives

variable {B : Type} {σ : Species jets} {D : Fin 1 ⊕ Fin 3 → B → B}
  {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B}

variable (σ) in
/-- The derivative law of a symbol family, under which `D μ` takes `∂^s σ^ℓ` to
  `∂^(μ ::ₘ s) σ^ℓ`. -/
def DerivLaw (D : Fin 1 ⊕ Fin 3 → B → B) (F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B) : Prop :=
  ∀ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label), D μ (F s ℓ) = F (μ ::ₘ s) ℓ

/-- Repeated derivatives, the head of the list applied last, append the list to the derivative
  index. -/
lemma DerivLaw.foldr (hF : σ.DerivLaw D F) (L : List (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (ℓ : σ.Label) :
    L.foldr D (F s ℓ) = F ((L : Multiset (Fin 1 ⊕ Fin 3)) + s) ℓ := by
  induction L with
  | nil => rw [List.foldr_nil, Multiset.coe_nil, zero_add]
  | cons μ L ih => rw [List.foldr_cons, ih, hF, ← Multiset.cons_coe, Multiset.cons_add]

/-- The derivative law is carried along any map intertwining the derivatives. -/
lemma DerivLaw.map {B' : Type} {D' : Fin 1 ⊕ Fin 3 → B' → B'} (hF : σ.DerivLaw D F)
    (Φ : B → B') (hΦ : ∀ μ b, Φ (D μ b) = D' μ (Φ b)) :
    σ.DerivLaw D' (fun s ℓ => Φ (F s ℓ)) := fun μ s ℓ => by
  show D' μ (Φ (F s ℓ)) = Φ (F (μ ::ₘ s) ℓ)
  rw [← hΦ, hF]

/-- For commuting linear derivatives, the derivative law says every symbol is an iterated
  derivative of the underived one. -/
lemma derivLaw_iff_eq_iteratedD {B : Type} [Ring B] [Algebra ℂ B]
    {D : Fin 1 ⊕ Fin 3 → B →ₗ[ℂ] B} (hD : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ))
    {F : Multiset (Fin 1 ⊕ Fin 3) → σ.Label → B} :
    σ.DerivLaw (fun μ => D μ) F ↔ ∀ s ℓ, F s ℓ = Lorentz.iteratedD D hD s (F 0 ℓ) := by
  refine ⟨fun hF s ℓ => ?_, fun h μ s ℓ => ?_⟩
  · induction s using Multiset.induction_on with
    | empty => rw [Lorentz.iteratedD_zero, LinearMap.id_apply]
    | cons μ s ih =>
      rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ← ih]
      exact (hF μ s ℓ).symm
  · show D μ (F s ℓ) = F (μ ::ₘ s) ℓ
    rw [h s ℓ, h (μ ::ₘ s) ℓ, Lorentz.iteratedD_cons, LinearMap.comp_apply]

end OrdinaryDerivatives

end Species

/-!

## E. Matter fields as species

-/

namespace MatterField

open Species

variable {B : Type} [Ring B] [Algebra ℂ B] {repGauge : Representation ℂ GJ B}

/-- For matter the gauge law is `LocalGaugeData.TransformsIn`, for a family complex-linear
  in the label. -/
lemma gaugeLaw_iff (M : MatterField jets)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ M.V →ₗ[ℂ] B) :
    (M : Species jets).GaugeLaw repGauge (fun s φ => F s φ)
      ↔ LocalGaugeData.TransformsIn repGauge M.repJet F := by
  have key : ∀ (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ M.V),
      (((M : Species jets).inhomogeneousTerm U s φ : ℝ) : ℂ) • (1 : B) = 0 := fun _ _ _ => by
    rw [inhomogeneousTerm_matter, Complex.ofReal_zero, zero_smul]
  constructor
  · intro h U φ s
    have h' := h U s φ
    rwa [key, add_zero] at h'
  · intro h U s φ
    rw [key, add_zero]
    exact h U φ s

end MatterField

/-!

## F. The connection in components

Here `A_μ^a` denotes the label `GaugeBoson.componentCovector 𝔤 μ a`, the covector selecting the
`μ`-th spacetime component of the connection paired with the gauge-algebra covector `a`.

-/

namespace Species

variable {B : Type} [Ring B] [Algebra ℂ B] {repGauge : Representation ℂ GJ B}

/-- The gauge law of the connection at the component covectors `A_μ^a`, whose coefficients
  move only the adjoint index and whose inhomogeneous term is the Maurer–Cartan form. -/
lemma GaugeLaw.connection_components
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ (GaugeBoson 𝔤) → B}
    (hF : (gauge : Species jets).GaugeLaw repGauge F) (U : GJ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (a : Module.Dual ℝ 𝔤) :
    repGauge U (F s (GaugeBoson.componentCovector 𝔤 μ a))
      = (s.antidiagonal.map fun p =>
          F p.2 (GaugeBoson.componentCovector 𝔤 μ (jets.adjointDualCoeff U⁻¹ p.1 a))).sum
        + ((a (jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U⁻¹ μ))) : ℝ) : ℂ) • 1 := by
  rw [hF U s, inhomogeneousTerm_gauge, componentDual_dualBasis_mcBosonCoeff]
  refine congrArg (· + _) (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
  rw [coeff_gauge, GaugeBoson.dualMap_adjointTransport_componentDual]
  rfl

end Species
