/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
/-!

# Grading on the FieldOpFreeAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section

/-- The submodule of `FieldOpFreeAlgebra` spanned by lists of field statistic `f`. -/
def statisticSubmodule (f : FieldStatistic) : Submodule ℂ 𝓕.FieldOpFreeAlgebra :=
  Submodule.span ℂ {a | ∃ φs, a = ofCrAnListF φs ∧ (𝓕 |>ₛ φs) = f}

lemma ofCrAnListF_mem_statisticSubmodule_of (φs : List 𝓕.CrAnFieldOp) (f : FieldStatistic)
    (h : (𝓕 |>ₛ φs) = f) :
    ofCrAnListF φs ∈ statisticSubmodule f := by
  refine Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩

lemma ofCrAnListF_bosonic_or_fermionic (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListF φs ∈ statisticSubmodule bosonic ∨
    ofCrAnListF φs ∈ statisticSubmodule fermionic := by
  by_cases h : (𝓕 |>ₛ φs) = bosonic
  · left
    exact ofCrAnListF_mem_statisticSubmodule_of φs bosonic h
  · right
    exact ofCrAnListF_mem_statisticSubmodule_of φs fermionic (by simpa using h)

lemma ofCrAnOpF_bosonic_or_fermionic (φ : 𝓕.CrAnFieldOp) :
    ofCrAnOpF φ ∈ statisticSubmodule bosonic ∨ ofCrAnOpF φ ∈ statisticSubmodule fermionic := by
  rw [← ofCrAnListF_singleton]
  exact ofCrAnListF_bosonic_or_fermionic [φ]

/-- The projection of an element of `FieldOpFreeAlgebra` onto it's bosonic part. -/
def bosonicProjF : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statisticSubmodule (𝓕 := 𝓕) bosonic :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  if h : (𝓕 |>ₛ φs) = bosonic then
    ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩
  else
    0

lemma bosonicProjF_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    bosonicProjF (ofCrAnListF φs) = if h : (𝓕 |>ₛ φs) = bosonic then
      ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩ else 0 := by
  conv_lhs =>
    rw [← ofListBasis_eq_ofList, bosonicProjF, Basis.constr_basis]

lemma bosonicProjF_of_mem_bosonic (a : 𝓕.FieldOpFreeAlgebra) (h : a ∈ statisticSubmodule bosonic) :
    bosonicProjF a = ⟨a, h⟩ := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    bosonicProjF a = ⟨a, hx⟩
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, bosonicProjF_ofCrAnListF, h]
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma bosonicProjF_of_mem_fermionic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule fermionic) :
    bosonicProjF a = 0 := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    bosonicProjF a = 0
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, bosonicProjF_ofCrAnListF, h]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

@[simp]
lemma bosonicProjF_of_bonosic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProjF (a bosonic) = a bosonic := by
  apply bosonicProjF_of_mem_bosonic

@[simp]
lemma bosonicProjF_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProjF (a fermionic).1 = 0 := by
  apply bosonicProjF_of_mem_fermionic
  exact Submodule.coe_mem (a.toFun fermionic)

/-- The projection of an element of `FieldOpFreeAlgebra` onto it's fermionic part. -/
def fermionicProjF : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statisticSubmodule (𝓕 := 𝓕) fermionic :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  if h : (𝓕 |>ₛ φs) = fermionic then
    ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩
  else
    0

lemma fermionicProjF_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    fermionicProjF (ofCrAnListF φs) = if h : (𝓕 |>ₛ φs) = fermionic then
      ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩ else 0 := by
  conv_lhs =>
    rw [← ofListBasis_eq_ofList, fermionicProjF, Basis.constr_basis]

lemma fermionicProjF_ofCrAnListF_if_bosonic (φs : List 𝓕.CrAnFieldOp) :
    fermionicProjF (ofCrAnListF φs) = if h : (𝓕 |>ₛ φs) = bosonic then
      0 else ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl,
        by simpa using h⟩⟩⟩ := by
  rw [fermionicProjF_ofCrAnListF]
  by_cases h1 : (𝓕 |>ₛ φs) = fermionic
  · simp [h1]
  · simp only [h1, ↓reduceDIte]
    simp only [neq_fermionic_iff_eq_bosonic] at h1
    simp [h1]

lemma fermionicProjF_of_mem_fermionic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule fermionic) :
    fermionicProjF a = ⟨a, h⟩ := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    fermionicProjF a = ⟨a, hx⟩
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, fermionicProjF_ofCrAnListF, h]
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma fermionicProjF_of_mem_bosonic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule bosonic) : fermionicProjF a = 0 := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    fermionicProjF a = 0
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, fermionicProjF_ofCrAnListF, h]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

@[simp]
lemma fermionicProjF_of_bosonic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    fermionicProjF (a bosonic).1 = 0 := by
  apply fermionicProjF_of_mem_bosonic
  exact Submodule.coe_mem (a.toFun bosonic)

@[simp]
lemma fermionicProjF_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    fermionicProjF (a fermionic) = a fermionic := by
  apply fermionicProjF_of_mem_fermionic

lemma bosonicProjF_add_fermionicProjF (a : 𝓕.FieldOpFreeAlgebra) :
    a.bosonicProjF + (a.fermionicProjF).1 = a := by
  let f1 :𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra :=
    (statisticSubmodule bosonic).subtype ∘ₗ bosonicProjF
  let f2 :𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra :=
    (statisticSubmodule fermionic).subtype ∘ₗ fermionicProjF
  change (f1 + f2) a = LinearMap.id (R := ℂ) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun φs ↦ ?_) a
  simp only [ofListBasis_eq_ofList, LinearMap.add_apply, LinearMap.coe_comp, Submodule.coe_subtype,
    Function.comp_apply, LinearMap.id_coe, id_eq, f1, f2]
  rw [bosonicProjF_ofCrAnListF, fermionicProjF_ofCrAnListF_if_bosonic]
  by_cases h : (𝓕 |>ₛ φs) = bosonic
  · simp [h]
  · simp [h]

lemma coeAddMonoidHom_apply_eq_bosonic_plus_fermionic
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    DirectSum.coeAddMonoidHom statisticSubmodule a = a.1 bosonic + a.1 fermionic := by
  let C : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i)) → Prop :=
    fun a => DirectSum.coeAddMonoidHom statisticSubmodule a = a.1 bosonic + a.1 fermionic
  change C a
  apply DirectSum.induction_on
  · simp [C]
  · intro i x
    simp only [DFinsupp.toFun_eq_coe, DirectSum.coeAddMonoidHom_of, C]
    rw [DirectSum.of_apply, DirectSum.of_apply]
    match i with
    | bosonic => simp
    | fermionic => simp
  · intro x y hx hy
    simp_all only [C, DFinsupp.toFun_eq_coe, map_add, DirectSum.add_apply, Submodule.coe_add]
    abel

lemma directSum_eq_bosonic_plus_fermionic
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    a = (DirectSum.of (fun i => ↥(statisticSubmodule i)) bosonic) (a bosonic) +
    (DirectSum.of (fun i => ↥(statisticSubmodule i)) fermionic) (a fermionic) := by
  let C : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i)) → Prop :=
    fun a => a = (DirectSum.of (fun i => ↥(statisticSubmodule i)) bosonic) (a bosonic) +
    (DirectSum.of (fun i => ↥(statisticSubmodule i)) fermionic) (a fermionic)
  change C a
  apply DirectSum.induction_on
  · simp [C]
  · intro i x
    simp only [C]
    match i with
    | bosonic =>
      simp only [DirectSum.of_eq_same, self_eq_add_right]
      rw [DirectSum.of_eq_of_ne]
      simp only [map_zero]
      simp
    | fermionic =>
      simp only [DirectSum.of_eq_same, add_zero]
      rw [DirectSum.of_eq_of_ne]
      simp only [map_zero, zero_add]
      simp
  · intro x y hx hy
    simp only [DirectSum.add_apply, map_add, C] at hx hy ⊢
    conv_lhs => rw [hx, hy]
    abel

/-- For a field statistic `𝓕`, the algebra `𝓕.FieldOpFreeAlgebra` is graded by `FieldStatistic`.
  Those `ofCrAnListF φs` for which `φs` has `bosonic` statistics span one part  of the grading,
  whilst those where `φs` has `fermionic` statistics span the other part of the grading. -/
instance fieldOpFreeAlgebraGrade :
    GradedAlgebra (A := 𝓕.FieldOpFreeAlgebra) statisticSubmodule where
  one_mem := by
    simp only [statisticSubmodule]
    refine Submodule.mem_span.mpr fun p a => a ?_
    simp only [Set.mem_setOf_eq]
    use []
    simp only [ofCrAnListF_nil, ofList_empty, true_and]
    rfl
  mul_mem f1 f2 a1 a2 h1 h2 := by
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule f2) : Prop :=
      a1 * a2 ∈ statisticSubmodule (f1 + f2)
    change p a2 h2
    apply Submodule.span_induction (p := p)
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨φs, rfl, h⟩ := hx
      simp only [p]
      let p (a1 : 𝓕.FieldOpFreeAlgebra) (hx : a1 ∈ statisticSubmodule f1) : Prop :=
        a1 * ofCrAnListF φs ∈ statisticSubmodule (f1 + f2)
      change p a1 h1
      apply Submodule.span_induction (p := p)
      · intro y hy
        obtain ⟨φs', rfl, h'⟩ := hy
        simp only [p]
        rw [← ofCrAnListF_append]
        refine Submodule.mem_span.mpr fun p a => a ?_
        simp only [Set.mem_setOf_eq]
        use φs' ++ φs
        simp only [ofList_append, h', h, true_and]
        cases f1 <;> cases f2 <;> rfl
      · simp [p]
      · intro x y hx hy hx1 hx2
        simp only [add_mul, p]
        exact Submodule.add_mem _ hx1 hx2
      · intro c a hx h1
        simp only [Algebra.smul_mul_assoc, p]
        exact Submodule.smul_mem _ _ h1
      · exact h1
    · simp [p]
    · intro x y hx hy hx1 hx2
      simp only [mul_add, p]
      exact Submodule.add_mem _ hx1 hx2
    · intro c a hx h1
      simp only [Algebra.mul_smul_comm, p]
      exact Submodule.smul_mem _ _ h1
    · exact h2
  decompose' a := DirectSum.of (fun i => (statisticSubmodule (𝓕 := 𝓕) i)) bosonic (bosonicProjF a)
    + DirectSum.of (fun i => (statisticSubmodule (𝓕 := 𝓕) i)) fermionic (fermionicProjF a)
  left_inv a := by
    trans a.bosonicProjF + fermionicProjF a
    · simp
    · exact bosonicProjF_add_fermionicProjF a
  right_inv a := by
    rw [coeAddMonoidHom_apply_eq_bosonic_plus_fermionic]
    simp only [DFinsupp.toFun_eq_coe, map_add, bosonicProjF_of_bonosic_part,
      bosonicProjF_of_fermionic_part, add_zero, fermionicProjF_of_bosonic_part,
      fermionicProjF_of_fermionic_part, zero_add]
    conv_rhs => rw [directSum_eq_bosonic_plus_fermionic a]

lemma eq_zero_of_bosonic_and_fermionic {a : 𝓕.FieldOpFreeAlgebra}
    (hb : a ∈ statisticSubmodule bosonic) (hf : a ∈ statisticSubmodule fermionic) : a = 0 := by
  have ha := bosonicProjF_of_mem_bosonic a hb
  have hb := fermionicProjF_of_mem_fermionic a hf
  have hc := (bosonicProjF_add_fermionicProjF a)
  rw [ha, hb] at hc
  simpa using hc

lemma bosonicProjF_mul (a b : 𝓕.FieldOpFreeAlgebra) :
    (a * b).bosonicProjF.1 = a.bosonicProjF.1 * b.bosonicProjF.1
    + a.fermionicProjF.1 * b.fermionicProjF.1 := by
  conv_lhs =>
    rw [← bosonicProjF_add_fermionicProjF a]
    rw [← bosonicProjF_add_fermionicProjF b]
  simp only [mul_add, add_mul, map_add, Submodule.coe_add]
  rw [bosonicProjF_of_mem_bosonic]
  conv_lhs =>
    left
    right
    rw [bosonicProjF_of_mem_fermionic _
      (by
      have h1 : fermionic = fermionic + bosonic := by simp
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  conv_lhs =>
    right
    left
    rw [bosonicProjF_of_mem_fermionic _
      (by
      have h1 : fermionic = bosonic + fermionic := by simp
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  conv_lhs =>
    right
    right
    rw [bosonicProjF_of_mem_bosonic _
      (by
      have h1 : bosonic = fermionic + fermionic := by
        simp only [add_eq_mul, instCommGroup, mul_self]
        rfl
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  simp only [ZeroMemClass.coe_zero, add_zero, zero_add]
  · have h1 : bosonic = bosonic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    conv_lhs => rw [h1]
    apply fieldOpFreeAlgebraGrade.mul_mem
    simp only [SetLike.coe_mem]
    simp

lemma fermionicProjF_mul (a b : 𝓕.FieldOpFreeAlgebra) :
    (a * b).fermionicProjF.1 = a.bosonicProjF.1 * b.fermionicProjF.1
    + a.fermionicProjF.1 * b.bosonicProjF.1 := by
  conv_lhs =>
    rw [← bosonicProjF_add_fermionicProjF a]
    rw [← bosonicProjF_add_fermionicProjF b]
  simp only [mul_add, add_mul, map_add, Submodule.coe_add]
  conv_lhs =>
    left
    left
    rw [fermionicProjF_of_mem_bosonic _
      (by
      have h1 : bosonic = bosonic + bosonic := by
        simp only [add_eq_mul, instCommGroup, mul_self]
        rfl
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  conv_lhs =>
    left
    right
    rw [fermionicProjF_of_mem_fermionic _
      (by
      have h1 : fermionic = fermionic + bosonic := by simp
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  conv_lhs =>
    right
    left
    rw [fermionicProjF_of_mem_fermionic _
      (by
      have h1 : fermionic = bosonic + fermionic := by simp
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  conv_lhs =>
    right
    right
    rw [fermionicProjF_of_mem_bosonic _
      (by
      have h1 : bosonic = fermionic + fermionic := by
        simp only [add_eq_mul, instCommGroup, mul_self]
        rfl
      conv_lhs => rw [h1]
      apply fieldOpFreeAlgebraGrade.mul_mem
      simp only [SetLike.coe_mem]
      simp)]
  simp only [ZeroMemClass.coe_zero, zero_add, add_zero]
  abel

end

end FieldOpFreeAlgebra

end FieldSpecification
