/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.BrillouinZone

/-!
# Symmetry reduction of the Brillouin zone

Symmetry-invariant functions correspond to functions on an irreducible zone.

## i. Overview

The translations of a crystal determine its Brillouin zone. A subgroup `H` of crystal
symmetries acts on the crystal momenta. Symmetry-invariant quantities have equal values at
momenta in the same orbit. The symmetry quotient identifies these momenta. An irreducible zone
chooses one representative of each orbit.

For a square lattice, take `H` to be the group of four rotations and four reflections. A scalar
band energy with these symmetries is determined by its values on an eighth of the square.
Restriction to an irreducible zone gives an equivalence between functions fixed by the symmetry
action and functions on the zone.

## ii. Key results

- `BrillouinZone.SymmetryQuotient` : the orbit space of the Brillouin zone under `H`.
- `BrillouinZone.littleGroup` : the symmetries in `H` that fix a point of the zone.
- `BrillouinZone.ker_pointOp_le_littleGroup` : the shifts in `H` lie in every little group.
- `BrillouinZone.orbitRel_map_pointOp` : `H` and its point operations give the same momentum orbits.
- `BrillouinZone.symmetryQuotientEquivMapPointOp` : the symmetry quotients for `H` and its point
  operations correspond.
- `BrillouinZone.IsIrreducibleZone` : a set with one representative of each momentum orbit.
- `BrillouinZone.exists_isIrreducibleZone` : every group `H` has an irreducible zone.
- `BrillouinZone.eq_of_eqOn_irreducibleZone` : a function invariant under `H` is determined on
  an irreducible zone.
- `BrillouinZone.irreducibleZoneEquiv` : an irreducible zone corresponds to the symmetry quotient.
- `BrillouinZone.invariantFunctionsEquiv` : restriction identifies invariant functions with
  functions on an irreducible zone.

## iii. Table of contents

- A. The symmetry quotient
- B. The little group
- C. Point operations
- D. Irreducible zones

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L4, Section 4.4 and lecture L5,
  Section 5.1.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

open Symmetry

namespace BrillouinZone

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]
  [TopologicalSpace G] [DiscreteTopology G] {C : Crystal G}
  {H : Subgroup (Symmetry C)} {D : Set (BrillouinZone G)} {β : Type*}

/-! ## A. The symmetry quotient -/

/-- The orbit space of the Brillouin zone under `H`. -/
abbrev SymmetryQuotient (H : Subgroup (Symmetry C)) :=
  MulAction.orbitRel.Quotient H (BrillouinZone G)

/-! ## B. The little group -/

/-- The little group of a point `k` of the zone: the symmetries in `H` that fix `k`. -/
noncomputable abbrev littleGroup (H : Subgroup (Symmetry C)) (k : BrillouinZone G) : Subgroup H :=
  MulAction.stabilizer H k

/-- A symmetry in `H` lies in the little group of `k` exactly when it fixes `k`. -/
lemma mem_littleGroup_iff {k : BrillouinZone G} (s : H) :
    s ∈ littleGroup H k ↔ (s : Symmetry C) • k = k := Iff.rfl

/-- The shifts in `H` lie in the little group of every point. -/
lemma ker_pointOp_le_littleGroup (H : Subgroup (Symmetry C)) (k : BrillouinZone G) :
    (pointOp C).ker.subgroupOf H ≤ littleGroup H k := by
  intro s hs
  rw [mem_littleGroup_iff, ← BrillouinZone.pointOp_smul]
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hs
  rw [hs, one_smul]

/-! ## C. Point operations -/

/-- `H` and the group of its point operations identify the same points of the zone. -/
lemma orbitRel_map_pointOp (H : Subgroup (Symmetry C)) (k k' : BrillouinZone G) :
    MulAction.orbitRel (H.map (pointOp C)) (BrillouinZone G) k k' ↔
      MulAction.orbitRel H (BrillouinZone G) k k' := by
  simp only [MulAction.orbitRel_apply]
  constructor
  · rintro ⟨⟨_, s, hs, rfl⟩, h⟩
    exact ⟨⟨s, hs⟩, h⟩
  · rintro ⟨⟨s, hs⟩, h⟩
    exact ⟨⟨pointOp C s, s, hs, rfl⟩, h⟩

/-- The symmetry quotients for `H` and its point operations correspond. -/
noncomputable def symmetryQuotientEquivMapPointOp (H : Subgroup (Symmetry C)) :
    SymmetryQuotient H ≃ SymmetryQuotient (H.map (pointOp C)) :=
  Quotient.congr (Equiv.refl _) fun k k' => (orbitRel_map_pointOp H k k').symm

/-! ## D. Irreducible zones

The action on momenta induces an action on functions by precomposition through
`DomMulAct H`. Invariant functions are the fixed points of this action. -/

/-- A set `D` of points of the Brillouin zone is an irreducible zone for `H` if it contains
exactly one representative of each orbit under `H`. -/
def IsIrreducibleZone (H : Subgroup (Symmetry C)) (D : Set (BrillouinZone G)) : Prop :=
  Set.BijOn (Quotient.mk'' : BrillouinZone G → SymmetryQuotient H) D Set.univ

/-- Every group `H` of symmetries has an irreducible zone. -/
lemma exists_isIrreducibleZone (H : Subgroup (Symmetry C)) :
    ∃ D : Set (BrillouinZone G), IsIrreducibleZone H D := by
  have hq : Function.Surjective (Quotient.mk'' : BrillouinZone G → SymmetryQuotient H) :=
    Quotient.mk'_surjective (s := MulAction.orbitRel H (BrillouinZone G))
  obtain ⟨D, _, hD⟩ := (hq.surjOn (t := Set.univ)).exists_bijOn_subset
  exact ⟨D, hD⟩

/-- Functions fixed by the symmetry action are determined by their values on an irreducible
zone. -/
lemma eq_of_eqOn_irreducibleZone (hD : IsIrreducibleZone H D)
    {f g : MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β)}
    (h : Set.EqOn f.val g.val D) : f = g := by
  apply Subtype.ext
  funext k
  obtain ⟨d, hd, hdk⟩ := hD.surjOn (Set.mem_univ (Quotient.mk'' k : SymmetryQuotient H))
  obtain ⟨s, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' hdk)
  calc
    f.val k = f.val (s • k) :=
      (congrFun (MulAction.mem_fixedPoints.mp f.property (DomMulAct.mk s)) k).symm
    _ = g.val (s • k) := h hd
    _ = g.val k := congrFun (MulAction.mem_fixedPoints.mp g.property (DomMulAct.mk s)) k

/-- An irreducible zone corresponds to the symmetry quotient. -/
noncomputable def irreducibleZoneEquiv (hD : IsIrreducibleZone H D) : D ≃ SymmetryQuotient H :=
  (Set.BijOn.equiv _ hD).trans (Equiv.Set.univ _)

/-- Restriction to an irreducible zone identifies functions fixed by the symmetry action with
functions on that zone. -/
noncomputable def invariantFunctionsEquiv (hD : IsIrreducibleZone H D) :
    MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β) ≃ (D → β) := by
  refine Equiv.ofBijective (fun f d => f.val d) ⟨?_, ?_⟩
  · intro f g h
    exact eq_of_eqOn_irreducibleZone hD (fun _ hd => congrFun h ⟨_, hd⟩)
  · intro φ
    let e := irreducibleZoneEquiv hD
    refine ⟨⟨fun k => φ (e.symm (Quotient.mk'' k)), ?_⟩, ?_⟩
    · rw [MulAction.mem_fixedPoints]
      intro s
      funext k
      change φ (e.symm (Quotient.mk'' (DomMulAct.mk.symm s • k))) =
        φ (e.symm (Quotient.mk'' k))
      exact congrArg (φ ∘ e.symm) (MulAction.orbitRel.Quotient.quotient_smul_eq
        (G := H) (g := DomMulAct.mk.symm s) (a := k))
    · funext d
      change φ (e.symm (e d)) = φ d
      rw [e.symm_apply_apply]

/-- The equivalence with functions on an irreducible zone acts by restriction. -/
@[simp] lemma invariantFunctionsEquiv_apply (hD : IsIrreducibleZone H D)
    (f : MulAction.fixedPoints (DomMulAct H) (BrillouinZone G → β)) (d : D) :
    invariantFunctionsEquiv hD f d = f.val d := rfl

/-- The inverse equivalence extends a function from the irreducible zone. -/
@[simp] lemma invariantFunctionsEquiv_symm_apply (hD : IsIrreducibleZone H D) (φ : D → β)
    (d : D) : ((invariantFunctionsEquiv hD).symm φ).val d = φ d :=
  congrFun ((invariantFunctionsEquiv hD).apply_symm_apply φ) d

end BrillouinZone

end Physlib.CondensedMatter.Crystal
