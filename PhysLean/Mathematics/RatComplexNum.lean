/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Complex.Basic
/-!
# Rational complex numbers

-/

namespace PhysLean

structure RatComplexNum where
  fst : ℚ
  snd : ℚ

namespace RatComplexNum

@[ext]
lemma ext {x y : RatComplexNum} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x
  cases y
  simp at h1 h2
  subst h1 h2
  rfl

def equivToProd : RatComplexNum ≃ ℚ × ℚ where
  toFun := fun x => (x.1, x.2)
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

instance : DecidableEq RatComplexNum := Equiv.decidableEq equivToProd

instance : AddCommGroup RatComplexNum where
  add := fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩
  add_assoc := by
    intro a b c
    match a, b, c with
    | ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩ =>
      ext
      · change a1 + b1 + c1 = a1 + (b1 + c1)
        ring
      · change a2 + b2 + c2 = a2 + (b2 + c2)
        ring
  zero := ⟨0, 0⟩
  zero_add := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change 0 + a1 = a1
        simp
      · change 0 + a2 = a2
        simp
  add_zero := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change a1 + 0 = a1
        simp
      · change a2 + 0 = a2
        simp
  nsmul := fun n x => ⟨n • x.fst, n • x.snd⟩
  neg := fun x => ⟨-x.fst, -x.snd⟩
  zsmul := fun n x => ⟨n • x.1, n • x.2⟩
  neg_add_cancel := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change -a1 + a1 = 0
        simp
      · change -a2 + a2 = 0
        simp
  add_comm := by
    intro x y
    match x, y with
    | ⟨x1, x2⟩, ⟨y1, y2⟩ =>
      ext
      · change x1 + y1 = y1 + x1
        simp [add_comm]
      · change x2 + y2 = y2 + x2
        simp [add_comm]

instance : Ring RatComplexNum where
  mul := fun x y => ⟨x.fst * y.fst - x.snd * y.snd, x.fst * y.snd + x.snd * y.fst⟩
  one := ⟨1, 0⟩
  mul_assoc := by
    intro x y z
    match x, y, z with
    | ⟨x1, x2⟩, ⟨y1, y2⟩, ⟨z1, z2⟩ =>
      ext
      · change (x1 * y1 - x2 * y2) * z1 - (x1 * y2 + x2 * y1) * z2 =
          x1 * (y1 * z1 - y2 * z2) - x2 * (y1 * z2 + y2 * z1)
        ring
      · change (x1 * y1 - x2 * y2) * z2 + (x1 * y2 + x2 * y1) * z1 =
          x1 * (y1 * z2 + y2 * z1) + x2 * (y1 * z1 - y2 * z2)
        ring
  one_mul := by
    intro x
    match x with
    | ⟨x1, x2⟩ =>
      ext
      · change 1 * x1 - 0 * x2 = x1
        simp
      · change 1 * x2 + 0 * x1 = x2
        simp
  mul_one := by
    intro x
    match x with
    | ⟨x1, x2⟩ =>
      ext
      · change x1 * 1 - x2 * 0 = x1
        simp
      · change x1 * 0 + x2 * 1 = x2
        simp

  left_distrib := by
    intro a b c
    match a, b, c with
    | ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩ =>
      ext
      · change a1 * (b1 + c1) - a2 * (b2 + c2) =
          (a1 * b1 - a2 * b2) + (a1 * c1 - a2 * c2)
        ring
      · change a1 * (b2 + c2) + a2 * (b1 + c1) =
          (a1 * b2 + a2 * b1) + (a1 * c2 + a2 * c1)
        ring
  right_distrib := by
    intro a b c
    match a, b, c with
    | ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨a1, a2⟩ =>
      ext
      · change (b1 + c1) * a1 - (b2 + c2) * a2 =
          (b1 * a1 - b2 * a2) + (c1 * a1 - c2 * a2)
        ring
      · change (b1 + c1) * a2 + (b2 + c2) * a1 =
          (b1 * a2 + b2 * a1) + (c1 * a2 + c2 * a1)
        ring
  zero_mul := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change 0 * a1 - 0 * a2 = 0
        simp
      · change 0 * a2 + 0 * a1 = 0
        simp
  mul_zero := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change a1 * 0 - a2 * 0 = 0
        simp
      · change a1 * 0 + a2 * 0 = 0
        simp
  zsmul := fun n x => ⟨n • x.1, n • x.2⟩
  neg_add_cancel := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change -a1 + a1 = 0
        simp
      · change -a2 + a2 = 0
        simp

@[simp]
lemma one_fst : (1 : RatComplexNum).fst = 1 := rfl

@[simp]
lemma one_snd : (1 : RatComplexNum).snd = 0 := rfl

@[simp]
lemma add_fst (x y : RatComplexNum) : (x + y).fst = x.fst + y.fst := rfl

@[simp]
lemma add_snd (x y : RatComplexNum) : (x + y).snd = x.snd + y.snd := rfl

@[simp]
lemma mul_fst (x y : RatComplexNum) : (x * y).fst = x.fst * y.fst - x.snd * y.snd := rfl

@[simp]
lemma mul_snd (x y : RatComplexNum) : (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl

@[simp]
lemma zero_fst : (0 : RatComplexNum).fst = 0 := rfl

@[simp]
lemma zero_snd : (0 : RatComplexNum).snd = 0 := rfl

open Complex

noncomputable def toComplexNum : RatComplexNum →+* ℂ where
  toFun := fun x => x.fst + x.snd * I
  map_one' := by
    simp
  map_add' a b := by
    simp
    ring
  map_mul' a b := by
    simp only [mul_fst, Rat.cast_sub, Rat.cast_mul, mul_snd, Rat.cast_add]
    ring_nf
    simp only [I_sq, mul_neg, mul_one]
    ring
  map_zero' := by
    simp

@[simp]
lemma I_mul_toComplexNum (a : RatComplexNum) : I * toComplexNum a = toComplexNum (⟨0, 1⟩ * a) := by
  simp [toComplexNum]
  ring_nf
  simp only [I_sq, neg_mul, one_mul]
  ring

lemma ofNat_mul_toComplexNum (n : ℕ) (a : RatComplexNum) :
    n * toComplexNum a = toComplexNum (n * a) := by
  simp only [map_mul, map_natCast]

lemma toComplexNum_injective : Function.Injective toComplexNum := by
  intro a b ha
  simp [toComplexNum] at ha
  rw [@Complex.ext_iff] at ha
  simp at ha
  ext
  · exact ha.1
  · exact ha.2

end RatComplexNum
end PhysLean
