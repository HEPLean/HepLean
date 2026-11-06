/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.PeriodicGraph
public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations

/-!
# Space group of a periodic graph

The space group consists of crystal symmetries preserving the bonds of a periodic graph.

## i. Overview

Consider a square lattice with horizontal bonds. A quarter-turn sends these bonds to vertical
pairs of sites. The horizontal bond pattern therefore selects a smaller group of symmetries.

The space group consists of the symmetries preserving the graph's bonds. Periodicity allows the
bonds to be specified relative to one reference cell. Every lattice translation preserves this
structure. The space group is the stabilizer of the reference-cell bond set.

The point group is the image of the space group under the point-operation homomorphism. It
records lattice automorphisms and unit-cell label permutations. Each full space-group symmetry
also carries label-dependent shifts. Bond preservation applies to this full symmetry.

## ii. Key results

- `PeriodicGraph.spaceGroup`: The crystal symmetries preserving adjacency.
- `PeriodicGraph.pointGroup`: The point operations of the space group.
- `PeriodicGraph.mem_spaceGroup_iff_preservesBonds`: A crystal symmetry belongs to the space
  group exactly when it preserves the finite bond set.
- `PeriodicGraph.spaceGroup_eq_stabilizer`: The space group is the stabilizer of the bond set.

## iii. Table of contents

- A. Space group and translations
- B. Point group
- C. The bond set

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L3, Section 3.1.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

open Pointwise

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G] {C : Crystal G}

namespace PeriodicGraph

variable {g : PeriodicGraph C} {φ ψ : Symmetry C}

/-! ## A. Space group and translations -/

/-- The adjacency-preserving subgroup of `Symmetry C`. -/
def spaceGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.graphAutomorphisms.comap (Symmetry.toPerm C)

/-- A crystal symmetry belongs to the space group exactly when it preserves adjacency. -/
lemma mem_spaceGroup_iff :
    φ ∈ g.spaceGroup ↔ ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y := by
  rfl

/-- Every lattice translation belongs to the space group. -/
lemma translation_mem_spaceGroup (a : G) : Symmetry.translation C a ∈ g.spaceGroup := by
  intro x y
  exact g.adj_vadd a x y

/-- The translation subgroup is contained in the space group. -/
lemma translations_le_spaceGroup : Symmetry.translations C ≤ g.spaceGroup := by
  rintro _ ⟨a, rfl⟩
  exact translation_mem_spaceGroup _

/-! ## B. Point group -/

/-- The image of the space group under `Symmetry.pointOp`. -/
def pointGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.spaceGroup.map (Symmetry.pointOp C)

/-- Membership in the point group is equivalent to being the point operation of a space-group
element. -/
lemma mem_pointGroup_iff :
    ψ ∈ g.pointGroup ↔ ∃ φ ∈ g.spaceGroup, Symmetry.pointOp C φ = ψ :=
  Subgroup.mem_map

/-! ## C. The bond set -/

section BondSet

variable [DecidableEq G] [DecidableEq C.UnitCell] [Fintype C.UnitCell]

/-- Every space-group symmetry preserves the reference-cell bonds. -/
lemma PreservesBonds.of_mem_spaceGroup (hφ : φ ∈ g.spaceGroup) : g.PreservesBonds φ := by
  intro b hb
  have hl := b.links_reference
  have hadj := (g.mem_bonds b).1 hb
  have hmap := (hφ _ _).2 hadj
  exact (g.adj_iff_mem_bonds (φ.mapBond_links hl)).1 hmap

/-- A crystal symmetry preserves adjacency exactly when it preserves the reference-cell bonds. -/
lemma mem_spaceGroup_iff_preservesBonds : φ ∈ g.spaceGroup ↔ g.PreservesBonds φ := by
  constructor
  · exact PreservesBonds.of_mem_spaceGroup
  · intro h
    rw [mem_spaceGroup_iff]
    intro x y
    constructor
    · intro hxy
      simpa using h.inv.map_adj hxy
    · exact h.map_adj

/-- The space group is the stabilizer of the set of reference-cell bonds. -/
lemma spaceGroup_eq_stabilizer :
    g.spaceGroup = MulAction.stabilizer (Symmetry C) g.bonds := by
  ext φ
  rw [mem_spaceGroup_iff_preservesBonds, preservesBonds_iff_smul_eq, MulAction.mem_stabilizer_iff]

end BondSet

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
