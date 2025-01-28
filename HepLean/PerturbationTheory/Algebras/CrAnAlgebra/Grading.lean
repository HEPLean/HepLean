/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.Basic
import HepLean.PerturbationTheory.Koszul.KoszulSign
import Mathlib.RingTheory.GradedAlgebra.Basic
/-!

# Grading on the CrAnAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace CrAnAlgebra

noncomputable section

/-- The submodule of `CrAnAlgebra` spanned by lists of field statistic `f`. -/
def statisticSubmodule  (f : FieldStatistic) :  Submodule ℂ 𝓕.CrAnAlgebra  :=
  Submodule.span ℂ {a | ∃ φs, a = ofCrAnList φs ∧ (𝓕 |>ₛ φs) = f}

lemma ofCrAnList_mem_statisticSubmodule_of (φs : List 𝓕.CrAnStates) (f : FieldStatistic)
  (h : (𝓕 |>ₛ φs) = f) :
    ofCrAnList φs ∈ statisticSubmodule f  := by
  refine Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩

lemma ofCrAnList_bosonic_or_fermionic (φs : List 𝓕.CrAnStates) :
    ofCrAnList φs ∈ statisticSubmodule bosonic ∨ ofCrAnList φs ∈ statisticSubmodule fermionic := by
  by_cases h : (𝓕 |>ₛ φs) = bosonic
  · left
    exact ofCrAnList_mem_statisticSubmodule_of φs bosonic h
  · right
    exact ofCrAnList_mem_statisticSubmodule_of φs fermionic (by simpa using h)

/-- The projection of an element of `CrAnAlgebra` onto it's bosonic part. -/
def bosonicProj : 𝓕.CrAnAlgebra →ₗ[ℂ] statisticSubmodule (𝓕 := 𝓕) bosonic :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  if h : (𝓕 |>ₛ φs) = bosonic then
    ⟨ofCrAnList φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩
  else
    0

lemma bosonicProj_ofCrAnList (φs : List 𝓕.CrAnStates) :
    bosonicProj (ofCrAnList φs) = if h : (𝓕 |>ₛ φs) = bosonic then
      ⟨ofCrAnList φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩ else 0 := by
  conv_lhs =>
    rw [← ofListBasis_eq_ofList, bosonicProj, Basis.constr_basis]

lemma bosonicProj_of_mem_bosonic (a : 𝓕.CrAnAlgebra) (h : a ∈ statisticSubmodule bosonic) :
    bosonicProj a = ⟨a, h⟩ := by
  let p (a : 𝓕.CrAnAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    bosonicProj a = ⟨a, hx⟩
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, bosonicProj_ofCrAnList, h]
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma bosonicProj_of_mem_fermionic (a : 𝓕.CrAnAlgebra) (h : a ∈ statisticSubmodule fermionic) :
    bosonicProj a = 0 := by
  let p (a : 𝓕.CrAnAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    bosonicProj a = 0
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, bosonicProj_ofCrAnList, h]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

@[simp]
lemma bosonicProj_of_bonosic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProj (a bosonic) = a bosonic := by
  apply bosonicProj_of_mem_bosonic

@[simp]
lemma bosonicProj_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProj (a fermionic).1 = 0 := by
  apply bosonicProj_of_mem_fermionic
  exact Submodule.coe_mem (a.toFun fermionic)

/-- The projection of an element of `CrAnAlgebra` onto it's fermionic part. -/
def fermionicProj : 𝓕.CrAnAlgebra →ₗ[ℂ] statisticSubmodule (𝓕 := 𝓕) fermionic :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  if h : (𝓕 |>ₛ φs) = fermionic then
    ⟨ofCrAnList φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩
  else
    0

lemma fermionicProj_ofCrAnList (φs : List 𝓕.CrAnStates) :
    fermionicProj (ofCrAnList φs) = if h : (𝓕 |>ₛ φs) = fermionic then
      ⟨ofCrAnList φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩ else 0 := by
  conv_lhs =>
    rw [← ofListBasis_eq_ofList, fermionicProj, Basis.constr_basis]

lemma fermionicProj_ofCrAnList_if_bosonic (φs : List 𝓕.CrAnStates) :
    fermionicProj (ofCrAnList φs) = if h : (𝓕 |>ₛ φs) = bosonic then
      0 else ⟨ofCrAnList φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl,
        by simpa using h ⟩⟩⟩ := by
  rw [fermionicProj_ofCrAnList]
  by_cases h1 : (𝓕 |>ₛ φs) = fermionic
  · simp [h1]
  · simp only [h1, ↓reduceDIte]
    simp only [neq_fermionic_iff_eq_bosonic] at h1
    simp [h1]

lemma fermionicProj_of_mem_fermionic (a : 𝓕.CrAnAlgebra) (h : a ∈ statisticSubmodule fermionic) :
    fermionicProj a = ⟨a, h⟩ := by
  let p (a : 𝓕.CrAnAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    fermionicProj a = ⟨a, hx⟩
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, fermionicProj_ofCrAnList, h]
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma fermionicProj_of_mem_bosonic (a : 𝓕.CrAnAlgebra) (h : a ∈ statisticSubmodule bosonic) :
    fermionicProj a = 0 := by
  let p (a : 𝓕.CrAnAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    fermionicProj a = 0
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, fermionicProj_ofCrAnList, h]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

@[simp]
lemma fermionicProj_of_bosonic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    fermionicProj (a bosonic).1 = 0 := by
  apply fermionicProj_of_mem_bosonic
  exact Submodule.coe_mem (a.toFun bosonic)

@[simp]
lemma fermionicProj_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    fermionicProj (a fermionic) = a fermionic := by
  apply fermionicProj_of_mem_fermionic

lemma bosonicProj_add_fermionicProj (a : 𝓕.CrAnAlgebra) :
    a.bosonicProj + (a.fermionicProj).1 = a := by
  let f1 :𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra :=
    (statisticSubmodule bosonic).subtype ∘ₗ bosonicProj
  let f2 :𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra :=
    (statisticSubmodule fermionic).subtype ∘ₗ fermionicProj
  change (f1 + f2) a = LinearMap.id (R := ℂ) a
  refine LinearMap.congr_fun (ofCrAnListBasis.ext fun φs ↦ ?_) a
  simp only [ofListBasis_eq_ofList, LinearMap.add_apply, LinearMap.coe_comp, Submodule.coe_subtype,
    Function.comp_apply, LinearMap.id_coe, id_eq, f1, f2]
  rw [bosonicProj_ofCrAnList, fermionicProj_ofCrAnList_if_bosonic]
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

instance : GradedAlgebra (A := 𝓕.CrAnAlgebra) statisticSubmodule where
  one_mem := by
    simp only [statisticSubmodule]
    refine Submodule.mem_span.mpr fun p a => a ?_
    simp only [Set.mem_setOf_eq]
    use []
    simp only [ofCrAnList_nil, ofList_empty, true_and]
    rfl
  mul_mem f1 f2 a1 a2 h1 h2 := by
    let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule f2) : Prop :=
       a1 * a2 ∈ statisticSubmodule (f1 + f2)
    change p a2 h2
    apply Submodule.span_induction (p := p)
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨φs, rfl, h⟩ := hx
      simp only [p]
      let p (a1 : 𝓕.CrAnAlgebra) (hx : a1 ∈ statisticSubmodule f1) : Prop :=
        a1 * ofCrAnList φs ∈ statisticSubmodule (f1 + f2)
      change p a1 h1
      apply Submodule.span_induction (p := p)
      · intro y hy
        obtain ⟨φs', rfl, h'⟩ := hy
        simp only [p]
        rw [← ofCrAnList_append]
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
  decompose' a :=  DirectSum.of (fun i => (statisticSubmodule (𝓕 := 𝓕) i)) bosonic (bosonicProj a)
    +  DirectSum.of (fun i => (statisticSubmodule (𝓕 := 𝓕) i)) fermionic (fermionicProj a)
  left_inv a := by
    trans  a.bosonicProj + fermionicProj a
    · simp
    · exact bosonicProj_add_fermionicProj a
  right_inv a := by
    rw [coeAddMonoidHom_apply_eq_bosonic_plus_fermionic]
    simp only [DFinsupp.toFun_eq_coe, map_add, bosonicProj_of_bonosic_part,
      bosonicProj_of_fermionic_part, add_zero, fermionicProj_of_bosonic_part,
      fermionicProj_of_fermionic_part, zero_add]
    conv_rhs => rw [directSum_eq_bosonic_plus_fermionic a]

lemma eq_zero_of_bosonic_and_fermionic {a : 𝓕.CrAnAlgebra}
    (hb : a ∈ statisticSubmodule bosonic) (hf : a ∈ statisticSubmodule fermionic) : a = 0 := by
  have ha := bosonicProj_of_mem_bosonic a hb
  have hb := fermionicProj_of_mem_fermionic a hf
  have hc := (bosonicProj_add_fermionicProj a)
  rw [ha, hb] at hc
  simpa using hc


end

end CrAnAlgebra

end FieldSpecification
