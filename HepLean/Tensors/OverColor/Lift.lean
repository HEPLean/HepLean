/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
/-!

## Lifting functors.

There is a functor from functors `Discrete C ⥤ Rep k G` to
monoidal functors `MonoidalFunctor (OverColor C) (Rep k G)`.
We call this functor `lift`. It is a lift in the
sense that it is a section of the forgetful functor
`MonoidalFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G)`.

Functors in `Discrete C ⥤ Rep k G` form the basic building blocks of tensor structures.
The fact that they extend to monoidal functors `OverColor C ⥤ Rep k G` allows us to
interfact more generally with tensors.

-/

namespace IndexNotation
namespace OverColor
open CategoryTheory
open MonoidalCategory

variable {C k : Type} [CommRing k] {G : Type} [Group G]

namespace Discrete

/-- Takes a homorphism in `Discrete C` to an isomorphism built on the same objects. -/
def homToIso {c1 c2 : Discrete C} (h : c1 ⟶ c2) : c1 ≅ c2 :=
  Discrete.eqToIso (Discrete.eq_of_hom h)

end Discrete

namespace lift
noncomputable section
variable (F : Discrete C ⥤ Rep k G)

/-- Takes a homorphisms of `Discrete C` to an isomorphism `F.obj c1 ≅ F.obj c2`. -/
def discreteFunctorMapIso {c1 c2 : Discrete C} (h : c1 ⟶ c2) :
    F.obj c1 ≅ F.obj c2 := F.mapIso (Discrete.homToIso h)

/-- Given a object in `OverColor Color` the correpsonding tensor product of representations. -/
def objObj' (f : OverColor C) : Rep k G := Rep.of {
  toFun := fun M => PiTensorProduct.map (fun x =>
    (F.obj (Discrete.mk (f.hom x))).ρ M),
  map_one' := by
    simp only [Functor.id_obj, map_one, PiTensorProduct.map_one]
  map_mul' := fun M N => by
    simp only [CategoryTheory.Functor.id_obj, _root_.map_mul]
    ext x : 2
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.mul_apply]}

lemma objObj'_ρ (f : OverColor C) (M : G) : (objObj' F f).ρ M =
    PiTensorProduct.map (fun x => (F.obj (Discrete.mk (f.hom x))).ρ M) := rfl

lemma objObj'_ρ_tprod (f : OverColor C) (M : G) (x : (i : f.left) → F.obj (Discrete.mk (f.hom i))) :
    (objObj' F f).ρ M (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k fun i => (F.obj (Discrete.mk (f.hom i))).ρ M (x i) := by
  rw [objObj'_ρ]
  change (PiTensorProduct.map fun x => _) ((PiTensorProduct.tprod k) x) =_
  rw [PiTensorProduct.map_tprod]
  rfl

end
end lift

end OverColor
end IndexNotation
