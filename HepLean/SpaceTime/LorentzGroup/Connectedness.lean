/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Topology.Constructions
/-!
# Connectedness of the restricted Lorentz group

In this file we provide a proof that the restricted Lorentz group is connected.

## References

- The main argument follows: Guillem Cobos, The Lorentz Group, 2015:
  https://diposit.ub.edu/dspace/bitstream/2445/68763/2/memoria.pdf

-/
noncomputable section
namespace spaceTime

def stepFunction : ℝ → ℝ := fun t =>
  if t < -1 then -1 else
    if t < 1 then t else 1

lemma stepFunction_continuous : Continuous stepFunction := by
  apply Continuous.if ?_ continuous_const (Continuous.if ?_ continuous_id continuous_const)
  all_goals
    intro a ha
    rw [@Set.Iio_def, @frontier_Iio, @Set.mem_singleton_iff] at ha
    rw [ha]
    simp  [neg_lt_self_iff, zero_lt_one, ↓reduceIte]

def lorentzDet (Λ : lorentzGroup) : ({-1, 1} : Set ℝ) :=
  ⟨Λ.1.1.det, by
    simp
    exact Or.symm (lorentzGroup.det_eq_one_or_neg_one _)⟩

lemma lorentzDet_continuous : Continuous lorentzDet := by
  refine Continuous.subtype_mk ?_ fun x => lorentzDet.proof_1 x
  exact Continuous.matrix_det $
    Continuous.comp' Units.continuous_val continuous_subtype_val

instance set_discrete : DiscreteTopology ({-1, 1} : Set ℝ) := discrete_of_t1_of_finite

lemma lorentzDet_eq_if_joined {Λ Λ' : lorentzGroup} (h : Joined Λ Λ') :
    Λ.1.1.det = Λ'.1.1.det := by
  obtain ⟨f, hf, hf2⟩ := h
  have h1 : Joined (lorentzDet Λ) (lorentzDet Λ') :=
    ⟨ContinuousMap.comp ⟨lorentzDet, lorentzDet_continuous⟩ f, congrArg lorentzDet hf,
    congrArg lorentzDet hf2⟩
  obtain ⟨g, hg1, hg2⟩ := h1
  have h2 := (@IsPreconnected.subsingleton ({-1, 1} : Set ℝ) _ _ _ (isPreconnected_range g.2))
    (Set.mem_range_self 0) (Set.mem_range_self 1)
  rw [hg1, hg2] at h2
  simpa [lorentzDet] using h2

lemma det_on_connected_component {Λ Λ'  : lorentzGroup} (h : Λ' ∈ connectedComponent Λ) :
    Λ.1.1.det = Λ'.1.1.det := by
  obtain ⟨s, hs, hΛ'⟩ := h
  let f : ContinuousMap s ({-1, 1} : Set ℝ) :=
    ContinuousMap.restrict s ⟨lorentzDet, lorentzDet_continuous⟩
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.1
  have hf := (@IsPreconnected.subsingleton ({-1, 1} : Set ℝ) _ _ _ (isPreconnected_range f.2))
    (Set.mem_range_self ⟨Λ, hs.2⟩)  (Set.mem_range_self ⟨Λ', hΛ'⟩)
  simpa [lorentzDet, f] using hf

lemma det_of_joined {Λ Λ' : lorentzGroup} (h : Joined Λ Λ') : Λ.1.1.det = Λ'.1.1.det :=
  det_on_connected_component $ pathComponent_subset_component _ h

namespace restrictedLorentzGroup

/-- The set of spacetime points such that the time element is positive, and which are
normalised to 1. -/
def P : Set (spaceTime) := {x | x 0 > 0 ∧ ηLin x x = 1}

lemma P_time_comp (x : P) : x.1 0 = √(1 + ‖x.1.space‖ ^ 2) := by
  symm
  rw [Real.sqrt_eq_cases]
  apply Or.inl
  refine And.intro ?_ (le_of_lt  x.2.1)
  rw [← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three]
  simp only [Fin.isValue, space, Matrix.cons_val_zero, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.tail_cons]
  have h1 := x.2.2
  rw [ηLin_expand] at h1
  linear_combination h1

def oneInP : P := ⟨![1, 0, 0, 0], by simp, by
  rw [ηLin_expand]
  simp⟩

def pathToOneInP (u : P) : Path oneInP u where
  toFun t := ⟨![√(1 + t ^ 2 * ‖u.1.space‖ ^ 2), t * u.1 1, t * u.1 2, t * u.1 3],
    by
      simp
      refine Right.add_pos_of_pos_of_nonneg (Real.zero_lt_one) $
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
    , by
      rw [ηLin_expand]
      simp
      rw [Real.mul_self_sqrt, ← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three]
      simp
      ring
      refine Right.add_nonneg (zero_le_one' ℝ) $
            mul_nonneg (sq_nonneg _) (sq_nonneg _) ⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    apply (continuous_pi_iff).mpr
    intro i
    fin_cases i
      <;> continuity
  source' := by
    simp
    rfl
  target' := by
    simp
    refine SetCoe.ext ?_
    funext i
    fin_cases i
    simp
    exact (P_time_comp u).symm
    all_goals rfl



/-- P is a topological space with the subset topology. -/
instance : TopologicalSpace P := instTopologicalSpaceSubtype

lemma P_path_connected : IsPathConnected (@Set.univ P) := by
  use oneInP
  apply And.intro trivial  ?_
  intro y _
  use pathToOneInP y
  simp only [Set.mem_univ, implies_true]



lemma P_abs_space_lt_time_comp (x : P) : ‖x.1.space‖ < x.1 0 := by
  rw [P_time_comp, Real.lt_sqrt]
  exact lt_one_add (‖(x.1).space‖ ^ 2)
  exact norm_nonneg (x.1).space

lemma η_P_P_pos (u v : P) : 0 < ηLin u v :=
  lt_of_lt_of_le (sub_pos.mpr (mul_lt_mul_of_nonneg_of_pos
    (P_abs_space_lt_time_comp u) ((P_abs_space_lt_time_comp v).le)
    (norm_nonneg (u.1).space) v.2.1)) (ηLin_ge_sub_norm u v)

lemma η_P_continuous (u : spaceTime) : Continuous (fun (a : P) => ηLin u a) := by
  simp only [ηLin_expand]
  refine Continuous.add ?_ ?_
  refine Continuous.add ?_ ?_
  refine Continuous.add ?_ ?_
  refine Continuous.comp' (continuous_mul_left _) ?_
  apply (continuous_pi_iff).mp
  exact continuous_subtype_val
  all_goals apply Continuous.neg
  all_goals apply Continuous.comp' (continuous_mul_left _)
  all_goals apply (continuous_pi_iff).mp
  all_goals exact continuous_subtype_val


lemma one_plus_η_P_P (u v : P) :  1 + ηLin u v ≠ 0 := by
  linarith [η_P_P_pos u v]

def φAux₁ (u v : P) : spaceTime →ₗ[ℝ] spaceTime where
  toFun x := (2 * ηLin x u) • v
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply]
    rw [mul_add, add_smul]
  map_smul' c x := by
    simp only [LinearMapClass.map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← mul_assoc, mul_comm 2 c, mul_assoc, mul_smul]


def φAux₂ (u v : P) : spaceTime →ₗ[ℝ] spaceTime where
  toFun x := - (ηLin x (u + v) / (1 + ηLin u v)) • (u + v)
  map_add' x y := by
    simp only
    rw [ηLin.map_add, div_eq_mul_one_div]
    rw [show (ηLin x + ηLin y) (↑u + ↑v) = ηLin x (u+v) + ηLin y (u+v) from rfl]
    rw [add_mul, neg_add, add_smul, ← div_eq_mul_one_div, ← div_eq_mul_one_div]
  map_smul' c x := by
    simp only
    rw [ηLin.map_smul]
    rw [show (c • ηLin x) (↑u + ↑v) = c * ηLin x (u+v) from rfl]
    rw [mul_div_assoc, neg_mul_eq_mul_neg, smul_smul]
    rfl

def φ (u v : P) : spaceTime →ₗ[ℝ] spaceTime := LinearMap.id + φAux₁ u v + φAux₂ u v

lemma φ_u_u_eq_id (u : P) : φ u u = LinearMap.id := by
  ext x
  simp [φ]
  rw [add_assoc]
  rw [@add_right_eq_self]
  rw [@add_eq_zero_iff_eq_neg]
  rw [φAux₁, φAux₂]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, smul_add, neg_smul, neg_add_rev, neg_neg]
  rw [← add_smul]
  apply congr
  apply congrArg
  repeat rw [u.2.2]
  field_simp
  ring
  rfl

def φMat (u v : P) : Matrix (Fin 4) (Fin 4) ℝ := LinearMap.toMatrix stdBasis stdBasis (φ u v)

lemma φMat_mulVec (u v : P) (x : spaceTime) : (φMat u v).mulVec x = φ u v x :=
  LinearMap.toMatrix_mulVec_repr stdBasis stdBasis (φ u v) x


lemma φMat_element (u v : P) (i j : Fin 4) : (φMat u v) i j =
    η i i * (ηLin (stdBasis i) (stdBasis j) + 2 * ηLin (stdBasis j) u * ηLin (stdBasis i) v -
    ηLin (stdBasis i) (u + v) * ηLin (stdBasis j) (u + v) / (1 + ηLin u v)) := by
  rw [ηLin_matrix_stdBasis' j i (φMat u v), φMat_mulVec]
  simp only [φ, φAux₁, φAux₂, map_add, smul_add, neg_smul, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMapClass.map_smul, smul_eq_mul, map_neg,
    mul_eq_mul_left_iff]
  apply Or.inl
  ring


lemma φMat_continuous (u : P) : Continuous (φMat u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [φMat_element]
  refine Continuous.comp' (continuous_mul_left (η i i)) ?hf
  refine Continuous.sub ?_ ?_
  refine Continuous.comp' (continuous_add_left ((ηLin (stdBasis i)) (stdBasis j))) ?_
  refine Continuous.comp' (continuous_mul_left (2 * (ηLin (stdBasis j)) ↑u)) ?_
  exact η_P_continuous _
  refine Continuous.mul ?_ ?_
  refine Continuous.mul ?_ ?_
  simp only [(ηLin _).map_add]
  refine Continuous.comp' ?_ ?_
  exact continuous_add_left ((ηLin (stdBasis i)) ↑u)
  exact η_P_continuous _
  simp only [(ηLin _).map_add]
  refine Continuous.comp' ?_ ?_
  exact continuous_add_left _
  exact η_P_continuous _
  refine Continuous.inv₀ ?_ ?_
  refine Continuous.comp' (continuous_add_left 1) ?_
  exact η_P_continuous _
  exact fun x => one_plus_η_P_P u x


lemma φMat_in_lorentz (u v : P) (x y : spaceTime) :
    ηLin ((φMat u v).mulVec x) ((φMat u v).mulVec y) = ηLin x y := by
  rw [φMat_mulVec, φMat_mulVec, φ, φAux₁, φAux₂]
  have h1 : (1 + (ηLin ↑u) ↑v) ≠ 0 := one_plus_η_P_P u v
  simp only [map_add, smul_add, neg_smul, LinearMap.add_apply, LinearMap.id_coe,
    id_eq, LinearMap.coe_mk, AddHom.coe_mk, LinearMapClass.map_smul, map_neg, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.neg_apply]
  field_simp
  simp only [v.2.2, mul_one, u.2.2]
  rw [ηLin_symm v u, ηLin_symm u y, ηLin_symm v y]
  ring

def φLor (u v : P) : lorentzGroup :=
  preserveηLinLorentzLift (φMat_in_lorentz u v)

lemma φLor_continuous (u : P) : Continuous (φLor u) := by
  refine Continuous.subtype_mk ?_ fun x => (preserveηLinLorentzLift (φMat_in_lorentz u x)).2
  refine Units.continuous_iff.mpr (And.intro ?_ ?_)
  exact φMat_continuous u
  change Continuous fun x => (η * (φMat u x).transpose * η)
  refine Continuous.matrix_mul ?_ continuous_const
  refine Continuous.matrix_mul continuous_const ?_
  exact Continuous.matrix_transpose (φMat_continuous u)


lemma φLor_joined_to_identity (u v : P) : Joined 1 (φLor u v) := by
  obtain ⟨f, _⟩ := P_path_connected.joinedIn u trivial v trivial
  use ContinuousMap.comp ⟨φLor u, φLor_continuous u⟩ f
  · simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Path.source, ContinuousMap.coe_mk]
    rw [@Subtype.ext_iff, φLor, preserveηLinLorentzLift]
    refine Units.val_eq_one.mp ?_
    simp [preserveηLinGLnLift, φMat, φ_u_u_eq_id u ]
  · simp

end restrictedLorentzGroup



end spaceTime
end
