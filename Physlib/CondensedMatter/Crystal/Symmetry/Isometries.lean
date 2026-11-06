/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetry.Basic

/-!
# Isometries of an embedded crystal

An isometry preserves the distances between the positions of all crystal sites.

## i. Overview

An embedding assigns a position in space to each site. These positions determine the distance
between every pair of sites. The isometries form the stabilizer of this distance function.

The standard square lattice illustrates the geometric restriction. The shear
`(n, m) ↦ (n + m, m)` preserves the periodic site pattern. It sends a vertical unit step to a
longer diagonal step. The isometry subgroup selects transformations preserving every distance.
Every lattice translation belongs to this subgroup.

Distances from all sites to the reference cell determine the isometry condition. Translation
invariance extends this check to every pair of sites.

## ii. Key results

- `Embedding.isometries`: crystal symmetries that preserve distances between site positions.
- `Embedding.translations_le_isometries`: every translation is an isometry.
- `Embedding.mem_isometries_iff_reference`: it suffices to check distances to the sites of the
  reference cell.

## iii. Table of contents

- A. Distance-preserving symmetries
- B. Distances to the reference cell

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E) {φ : Symmetry C}

/-! ## A. Distance-preserving symmetries -/

/-- The distance between the positions of two sites. -/
def sitesDist (x : C.Site × C.Site) : ℝ := dist (R.position x.1) (R.position x.2)

/-- The pullback action on pair functions induced by the diagonal action on sites. -/
local instance : MulAction (Symmetry C) (C.Site × C.Site → ℝ) := arrowAction

/-- The stabilizer of the embedding's pairwise distance function. -/
def isometries : Subgroup (Symmetry C) :=
  MulAction.stabilizer (Symmetry C) R.sitesDist

/-- Membership in `isometries` is equivalent to preservation of all pairwise distances. -/
lemma mem_isometries_iff : φ ∈ R.isometries ↔
    ∀ x y, dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y) := by
  rw [← inv_mem_iff, isometries, MulAction.mem_stabilizer_iff, funext_iff, Prod.forall]
  show (∀ a b, R.sitesDist ((φ⁻¹)⁻¹ • a, (φ⁻¹)⁻¹ • b) = R.sitesDist (a, b)) ↔ _
  rw [inv_inv]
  rfl

/-- The translation subgroup is contained in the isometry subgroup. -/
lemma translations_le_isometries : Symmetry.translations C ≤ R.isometries := by
  rintro _ ⟨a, rfl⟩
  exact R.mem_isometries_iff.2 (R.dist_position_vadd _)

/-! ## B. Distances to the reference cell -/

/-- A site is the lattice translate of the site with the same label in the reference cell. -/
lemma site_eq_vadd (x : C.Site) : x = x.cell +ᵥ (Site.ref x.label) :=
  Site.ext (by simp) rfl

/-- Distance preservation can be checked on pairs `⟨d, i⟩` and `⟨0, j⟩`
for all lattice vectors `d` and unit-cell labels `i` and `j`. -/
lemma mem_isometries_iff_reference : φ ∈ R.isometries ↔ ∀ (i j : C.UnitCell) (d : G),
    dist (R.position (φ ⟨d, i⟩)) (R.position (φ (Site.ref j))) =
      dist (R.position ⟨d, i⟩) (R.position (Site.ref j)) := by
  rw [mem_isometries_iff]
  constructor
  · intro h i j d
    exact h _ _
  · intro h ⟨n, i⟩ ⟨m, j⟩
    have hx : (⟨n, i⟩ : C.Site) = m +ᵥ ⟨n - m, i⟩ := Site.ext (by simp) rfl
    rw [hx, site_eq_vadd ⟨m, j⟩, Symmetry.map_vadd, Symmetry.map_vadd, R.dist_position_vadd,
      R.dist_position_vadd]
    exact h _ _ _

end Embedding

end Physlib.CondensedMatter.Crystal
