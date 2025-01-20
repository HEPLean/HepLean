/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStatistics.Basic
/-!

# Exchange sign

-/

namespace FieldStatistic

variable {𝓕 : Type}


/-- The echange sign of two field statistics.
  Defined to be `-1` if both field statistics are `fermionic` and `1` otherwise. -/
def exchangeSign : FieldStatistic →* FieldStatistic →* ℂ where
  toFun a :=
    {
      toFun := fun b =>
        match a, b with
        | bosonic, _ => 1
        | _, bosonic => 1
        | fermionic, fermionic => -1
      map_one' := by
        fin_cases a
        <;> simp
      map_mul' := fun c b => by
        fin_cases a <;>
          fin_cases b <;>
          fin_cases c <;>
          simp
    }
  map_one' := by
    ext b
    fin_cases b
    <;> simp
  map_mul' c b := by
    ext a
    fin_cases a
    <;> fin_cases b <;> fin_cases c
    <;> simp

/-- The echange sign of two field statistics.
  Defined to be `-1` if both field statistics are `fermionic` and `1` otherwise. -/
scoped[FieldStatistic] notation "𝓢(" a "," b ")" => exchangeSign a b

@[simp]
lemma exchangeSign_bosonic (a : FieldStatistic) : 𝓢(a, bosonic) = 1 := by
  fin_cases a <;> rfl

@[simp]
lemma bosonic_exchangeSign (a : FieldStatistic) : 𝓢(bosonic, a) = 1 := by
  fin_cases a <;> rfl

lemma exchangeSign_symm (a b : FieldStatistic) : 𝓢(a, b) = 𝓢(b, a) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma exchangeSign_eq_if (a b : FieldStatistic) :
    𝓢(a, b) = if a = fermionic ∧ b = fermionic then - 1 else 1 := by
  fin_cases a <;> fin_cases b <;> rfl

@[simp]
lemma exchangeSign_mul_self (a b : FieldStatistic) : 𝓢(a, b) * 𝓢(a, b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [exchangeSign]

@[simp]
lemma exchangeSign_mul_self_swap (a b : FieldStatistic) : 𝓢(a, b) * 𝓢(b, a) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [exchangeSign]

lemma exchangeSign_ofList_cons (a : FieldStatistic)
      (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    𝓢(a, ofList s (φ :: φs)) = 𝓢(a, s φ) * 𝓢(a, ofList s φs) := by
  rw [ofList_cons_eq_mul, map_mul]

lemma exchangeSign_cocycle (a b c : FieldStatistic) :
    𝓢(a, b * c) * 𝓢(b, c) = 𝓢(a, b) * 𝓢(a * b, c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

end FieldStatistic
