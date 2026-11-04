/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Contraction
/-!

# Complex conjugation of tensors

The conjugate of a tensor conjugates its components and moves each index to the conjugate color.

## i. Overview

Complex conjugation takes a left-handed Weyl spinor `ψ_α` to a right-handed one `ψ̄_α̇`, and a
Lorentz vector `v^μ` to the Lorentz vector `(v^μ)*`. It changes the kind of an index and keeps its
variance. It is not duality. For `SL(2, ℂ)` the dotted index of `ψ̄_α̇` is not the lowered
undotted index of `ψ_α`. So `bar` and `dual` are separate operations, and they commute.

A kind `κ : ConjKind O isReal` has an orbit `o : O`, which is the kind together with its
conjugate. The orbit fixes the basis labels. An orbit is real or complex, as `isReal o` says. A
real orbit has one kind, its own conjugate. A complex orbit has two kinds, conjugate to each other.
The flags `left` and `right` of a kind say which it is, and the conjugate kind `κ.bar` swaps them.
The conjugate color `c.bar` has the kind `c.kind.bar` and the variance of `c`. Because `bar` swaps
two flags, `c.bar.bar = c` (`Color.bar_bar`) and `c.dual.bar = c.bar.dual` (`Color.bar_dual`) hold
by `rfl` for every color, so a statement that conjugates twice needs no cast.

For example, a species of complex Lorentz tensors, over `ℂ` with `G = SL(2, ℂ)`, would have the
complex orbit `weyl`, the real orbit `vec`, and three kinds. The left-handed kind is
`⟨weyl, true, false, _⟩`, its conjugate is the right-handed kind `⟨weyl, false, true, _⟩`, and the
vector kind `⟨vec, true, true, _⟩` is its own conjugate. The last field `_` is the proof of
`valid`. The space `S.V ⟨⟨vec, true, true, _⟩, up⟩ = ℂ⁴` would hold the vectors `v^μ`, with
basis labels `I vec = Fin 4`, and both Weyl kinds would have the basis labels `I weyl = Fin 2`.
This file defines no such species.

In a conjugate species `S : ConjSpecies k G O isReal I` the basis labels `I o` of a color depend
only on the orbit `o` of its kind, so `c` and `c.bar` have the same basis labels by `rfl`. The
scalars `k` have a conjugation `star`, as `ℂ` does. The conjugate `S.conjEquiv c v` of a vector
`v` of color `c` is the vector `v̄` of color `c.bar` with components `(v̄)^μ = (v^μ)*` in the bases
of the species. The conjugate `Tensor.conj T` of a tensor `T` is the tensor `T̄` with components
`(T̄)^μν = (T^μν)*` and every index moved to the conjugate color. Both are conjugate-linear.
`Tensor.conj` is an involution (`Tensor.conj_conj`) and conjugates each factor of a pure tensor
(`Tensor.conj_pure`).

The class `Species.HasConjugation` states two laws. Conjugation commutes with the action `Λ` of
each `g : G`, `(Λv)‾ = Λ v̄`, so the representation at `c.bar` is the conjugate of the one at `c`.
Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`. On tensors it follows that
conjugation commutes with the group action (`Tensor.conj_smul`) and with contraction
(`Tensor.conj_contr`).

## ii. Key results

- `ConjKind` : a kind of index, its own conjugate on a real orbit, or one of two conjugate kinds
  on a complex orbit.
- `Color.bar` : the conjugate color, with `Color.bar_bar` and `Color.bar_dual` by `rfl`.
- `ConjSpecies` : a species on conjugate kinds, with basis labels fixed by the orbit.
- `Species.conjEquiv` : the conjugate of a vector, `(v̄)^μ = (v^μ)*`.
- `Species.HasConjugation` : conjugation commutes with the group action and preserves the
  contraction.
- `Species.Tensor.conj` : the conjugate of a tensor, `(T̄)^μν = (T^μν)*`, with
  `Species.Tensor.conj_conj`, `Species.Tensor.conj_pure`, `Species.Tensor.conj_smul` and
  `Species.Tensor.conj_contr`.

## iii. Table of contents

- A. Conjugate kinds and colors
- B. Conjugate species and the conjugation of vectors
- C. Species with a conjugation
- D. Conjugation of tensors
  - D.1. The group action and contraction

## iv. References

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

/-!

## A. Conjugate kinds and colors

-/

/-- A kind of index with a conjugate. Its orbit is the kind together with its conjugate and fixes
the basis labels. A real orbit (`isReal o = true`) has one kind, its own conjugate, such as the
Lorentz vector index. A complex orbit has two kinds, conjugate to each other, such as the indices
of `ψ_α` and `ψ̄_α̇`. A real kind has both flags `left` and `right`, and a kind of a complex orbit
has one of them. -/
structure ConjKind (O : Type) (isReal : O → Bool) where
  /-- The orbit, shared with the conjugate kind. It fixes the basis labels. -/
  orbit : O
  /-- The kind is left-handed, as `ψ_α`, or real. -/
  left : Bool
  /-- The kind is right-handed, as `ψ̄_α̇`, or real. -/
  right : Bool
  /-- A real orbit has only the kind with both flags, and a complex orbit only the two kinds with
  one flag each. -/
  valid : if isReal orbit then left ∧ right else left ≠ right

variable {O : Type} {isReal : O → Bool}

/-- The conjugate kind, with `left` and `right` swapped and the same orbit. -/
abbrev ConjKind.bar (κ : ConjKind O isReal) : ConjKind O isReal :=
  ⟨κ.orbit, κ.right, κ.left, by simpa [and_comm, ne_comm] using κ.valid⟩

/-- The conjugate color, with the conjugate kind and the same variance, as in `ψ_α ↦ ψ̄_α̇`. -/
abbrev Color.bar (c : Color (ConjKind O isReal)) : Color (ConjKind O isReal) :=
  ⟨c.kind.bar, c.variance⟩

/-- Conjugating twice gives back the color, by `rfl`. -/
lemma Color.bar_bar (c : Color (ConjKind O isReal)) : c.bar.bar = c := rfl

/-- Conjugation commutes with duality, by `rfl`. -/
lemma Color.bar_dual (c : Color (ConjKind O isReal)) : c.dual.bar = c.bar.dual := rfl

/-!

## B. Conjugate species and the conjugation of vectors

-/

/-- A species on conjugate kinds whose basis labels `I o` depend only on the orbit `o`, so that
`c` and `c.bar` have the same basis labels by `rfl`. A species declared with this type keeps `I`
visible, which lets the lemmas below find the labels. -/
abbrev ConjSpecies (k : Type) [CommRing k] (G : Type) [Group G] (O : Type) (isReal : O → Bool)
    (I : O → Type) [∀ o, Fintype (I o)] [∀ o, DecidableEq (I o)] : Type 1 :=
  Species k G (ConjKind O isReal) fun κ => I κ.orbit

namespace Species

variable {k : Type} [CommRing k] [StarRing k] {G : Type} [Group G] {I : O → Type}
    [∀ o, Fintype (I o)] [∀ o, DecidableEq (I o)] {S : ConjSpecies k G O isReal I}

variable (S) in
/-- The conjugate `v̄` of a vector `v` of color `c`, the vector of color `c.bar` with components
`(v̄)^μ = (v^μ)*`. It is conjugate-linear. The components are taken in the bases of the species,
so the conjugate of the basis vector `e_μ` of `c` is the basis vector `e_μ` of `c.bar`
(`conjEquiv_basis`). The laws of `HasConjugation` therefore constrain the bases at `c` and `c.bar`
together. -/
noncomputable def conjEquiv (c : Color (ConjKind O isReal)) : S.V c ≃ₗ⋆[k] S.V c.bar :=
  (S.basis c).repr.trans <| (Finsupp.mapRange.linearEquiv (starLinearEquiv k)).trans
    (S.basis c.bar).repr.symm

/-- The components of the conjugate are the conjugates of the components, `(v̄)^μ = (v^μ)*`. -/
@[simp]
lemma basis_repr_conjEquiv (c : Color (ConjKind O isReal)) (v : S.V c) (μ : I c.kind.orbit) :
    (S.basis c.bar).repr (S.conjEquiv c v) μ = star ((S.basis c).repr v μ) := by
  simp [conjEquiv]

/-- The conjugate of the basis vector `e_μ` of `c` is the basis vector `e_μ` of `c.bar`. -/
@[simp]
lemma conjEquiv_basis (c : Color (ConjKind O isReal)) (μ : I c.kind.orbit) :
    S.conjEquiv c (S.basis c μ) = S.basis c.bar μ := by
  simp [conjEquiv, Finsupp.mapRange_single]

/-!

## C. Species with a conjugation

-/

variable (S) in
/-- A conjugate species has a conjugation when conjugating components commutes with the action
`Λ` of each `g : G`, `(Λv)‾ = Λ v̄`, and preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`. Then
the representation at `c.bar` is the conjugate of the one at `c`. At a real kind, its own
conjugate, the matrices `Λ^μ_ν` are therefore real. -/
class HasConjugation : Prop where
  /-- Conjugation commutes with the group action, `(Λv)‾ = Λ v̄`. -/
  conjEquiv_rep (c : Color (ConjKind O isReal)) (g : G) (v : S.V c) :
    S.conjEquiv c (S.rep c g v) = S.rep c.bar g (S.conjEquiv c v)
  /-- Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`, for `u` of color `c` and
  `α` of color `c.dual`. -/
  star_contr (c : Color (ConjKind O isReal)) (u : S.V c) (α : S.V c.dual) :
    star (S.contr c (u ⊗ₜ[k] α)) = S.contr c.bar (S.conjEquiv c u ⊗ₜ[k] S.conjEquiv c.dual α)

/-!

## D. Conjugation of tensors

-/

namespace Tensor

variable {ι : Type} [Fintype ι] {c : ι → Color (ConjKind O isReal)}

/-- The conjugate `T̄` of a tensor `T`, with components `(T̄)^μν = (T^μν)*` and every index moved
to the conjugate color. It is conjugate-linear. -/
noncomputable def conj : S.Tensor c ≃ₗ⋆[k] S.Tensor fun i => (c i).bar :=
  (S.tensorBasis c).repr.trans <| (Finsupp.mapRange.linearEquiv (starLinearEquiv k)).trans
    (S.tensorBasis fun i => (c i).bar).repr.symm

/-- The components of the conjugate are the conjugates of the components, `(T̄)^μν = (T^μν)*`. -/
@[simp]
lemma tensorBasis_repr_conj (t : S.Tensor c) (μ : Π i, I (c i).kind.orbit) :
    (S.tensorBasis _).repr (conj t) μ = star ((S.tensorBasis c).repr t μ) := by
  simp [conj]

/-- Conjugating twice gives back the tensor. No relabeling is needed, since `c.bar.bar = c` holds
by `rfl`. -/
lemma conj_conj (t : S.Tensor c) : conj (conj t) = t :=
  (S.tensorBasis c).repr.injective <| Finsupp.ext fun μ =>
    (tensorBasis_repr_conj (conj t) μ).trans (by rw [tensorBasis_repr_conj, star_star])

/-- The conjugate of a pure tensor conjugates each factor, `(u ⊗ α)‾ = ū ⊗ ᾱ`. -/
@[simp]
lemma conj_pure (f : Π i, S.V (c i)) :
    conj (S.pure f) = S.pure fun i => S.conjEquiv (c i) (f i) :=
  (S.tensorBasis _).repr.injective <| Finsupp.ext fun μ => by
    simp [tensorBasis_repr_pure, star_prod]

/-!

### D.1. The group action and contraction

-/

variable [S.HasConjugation]

/-- Conjugation commutes with the action `Λ` of `g : G`, `(ΛT)‾ = Λ T̄`. -/
lemma conj_smul (g : G) (t : S.Tensor c) : conj (g • t) = g • conj t :=
  map_smul_of_pure conj g (fun f => by simp [HasConjugation.conjEquiv_rep]) t

variable {κ J : Type} [Fintype κ] [Fintype J] {c' : κ → Color (ConjKind O isReal)}
    {a : J → Color (ConjKind O isReal)}

/-- Conjugating a contraction is contracting the conjugate along the same pairs of slots,
`(T^ρμ_μ)‾ = T̄^ρμ_μ`. The relabeling of `T̄` is `σ` with its colors conjugated. -/
lemma conj_contr (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c) :
    conj (contr σ t) = contr (c' := fun x => (c' x).bar) (a := fun j => (a j).bar)
      -- The colors are checked slot by slot: the conjugates of `contrColors c' a` and the
      -- `contrColors` of the conjugates agree at each slot but not as functions.
      ⟨σ.toEquiv, by rintro (_ | _ | _) <;> exact congrArg Color.bar (σ.color_eq _)⟩ (conj t) := by
  -- Conjugating a vector commutes with moving it along an equality of colors.
  have hcast : ∀ {b b' : Color (ConjKind O isReal)} (p : b = b') (x : S.V b),
      S.conjEquiv b' (LinearEquiv.cast (R := k) (M := S.V) p x) =
        LinearEquiv.cast (R := k) (M := S.V) (congrArg Color.bar p) (S.conjEquiv b x) := by
    intro b b' p x
    subst p
    rfl
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [map_smul, LinearEquiv.map_smulₛₗ, ht, LinearEquiv.map_smulₛₗ, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | h f =>
    simp only [contr_pure, conj_pure, LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_prod,
      HasConjugation.star_contr, hcast]

end Tensor

end Species

end Tensors
