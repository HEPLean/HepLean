/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
/-!

# Feynman rules for a two complex scalar fields

This file serves as a demonstration of a new approach to Feynman rules.

-/

namespace TwoComplexScalar
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

/-- The colors of edges which one can associate with a vertex for a theory
  with two complex scalar fields. -/
inductive 𝓔 where
  /-- Corresponds to the first complex scalar field flowing out of a vertex. -/
  | complexScalarOut₁ : 𝓔
  /-- Corresponds to the first complex scalar field flowing into a vertex. -/
  | complexScalarIn₁ : 𝓔
  /-- Corresponds to the second complex scalar field flowing out of a vertex. -/
  | complexScalarOut₂ : 𝓔
  /-- Corresponds to the second complex scalar field flowing into a vertex. -/
  | complexScalarIn₂ : 𝓔

/-- The map taking each color to it's dual, specifying how we can contract edges. -/
def ξ : 𝓔 → 𝓔
  | 𝓔.complexScalarOut₁ => 𝓔.complexScalarIn₁
  | 𝓔.complexScalarIn₁ => 𝓔.complexScalarOut₁
  | 𝓔.complexScalarOut₂ => 𝓔.complexScalarIn₂
  | 𝓔.complexScalarIn₂ => 𝓔.complexScalarOut₂

/-- The function `ξ` is an involution. -/
lemma ξ_involutive : Function.Involutive ξ := by
  intro x
  match x with
  | 𝓔.complexScalarOut₁ => rfl
  | 𝓔.complexScalarIn₁ => rfl
  | 𝓔.complexScalarOut₂ => rfl
  | 𝓔.complexScalarIn₂ => rfl

/-- The vertices associated with two complex scalars.
  We call this type, the type of vertex colors. -/
inductive 𝓥 where
  | φ₁φ₁φ₂φ₂ : 𝓥
  | φ₁φ₁φ₁φ₁ : 𝓥
  | φ₂φ₂φ₂φ₂ : 𝓥

/-- To each vertex, the association of the number of edges. -/
@[nolint unusedArguments]
def 𝓥NoEdges : 𝓥 → ℕ := fun _ => 4

/-- To each vertex, associates the indexing map of half-edges associated with that edge. -/
def 𝓥Edges (v : 𝓥) : Fin (𝓥NoEdges v) → 𝓔 :=
  match v with
  | 𝓥.φ₁φ₁φ₂φ₂ => fun i =>
    match i with
    | (0 : Fin 4)=> 𝓔.complexScalarOut₁
    | (1 : Fin 4) => 𝓔.complexScalarIn₁
    | (2 : Fin 4) => 𝓔.complexScalarOut₂
    | (3 : Fin 4) => 𝓔.complexScalarIn₂
  | 𝓥.φ₁φ₁φ₁φ₁ => fun i =>
    match i with
    | (0 : Fin 4)=> 𝓔.complexScalarOut₁
    | (1 : Fin 4) => 𝓔.complexScalarIn₁
    | (2 : Fin 4) => 𝓔.complexScalarOut₁
    | (3 : Fin 4) => 𝓔.complexScalarIn₁
  | 𝓥.φ₂φ₂φ₂φ₂ => fun i =>
    match i with
    | (0 : Fin 4)=> 𝓔.complexScalarOut₂
    | (1 : Fin 4) => 𝓔.complexScalarIn₂
    | (2 : Fin 4) => 𝓔.complexScalarOut₂
    | (3 : Fin 4) => 𝓔.complexScalarIn₂

inductive WickStringLast where
  | incoming : WickStringLast
  | vertex : WickStringLast
  | outgoing : WickStringLast
  | final : WickStringLast

open WickStringLast

def FieldString (n : ℕ) : Type := Fin n → 𝓔

inductive WickString : {n : ℕ} → (c : FieldString n) → WickStringLast → Type where
  | empty : WickString Fin.elim0 incoming
  | incoming {n : ℕ} {c : Fin n → 𝓔} (w : WickString c incoming) (e : 𝓔) :
      WickString (Fin.cons e c) incoming
  | endIncoming {n : ℕ} {c : Fin n → 𝓔} (w : WickString c incoming) : WickString c vertex
  | vertex {n : ℕ} {c : Fin n → 𝓔} (w : WickString c vertex) (v : 𝓥) :
      WickString (Fin.append (𝓥Edges v) c) vertex
  | endVertex {n : ℕ} {c : Fin n → 𝓔} (w : WickString c vertex) : WickString c outgoing
  | outgoing {n : ℕ} {c : Fin n → 𝓔} (w : WickString c outgoing) (e : 𝓔) :
      WickString (Fin.cons e c) outgoing
  | endOutgoing {n : ℕ} {c : Fin n → 𝓔} (w : WickString c outgoing) : WickString c final

inductive WickContract : {n : ℕ} → (f : FieldString n) → {m : ℕ} → (ub : Fin m → Fin n) →
    {k : ℕ} → (b1 : Fin k → Fin n) → Type where
  | string {n : ℕ} {c : Fin n → 𝓔} : WickContract c id Fin.elim0
  | contr {n : ℕ} {c : Fin n → 𝓔} {m : ℕ} {ub : Fin m.succ.succ → Fin n} {k : ℕ}
    {b1 : Fin k → Fin n} : (i : Fin m.succ.succ) →
    (j : Fin m.succ) → (h : c (ub (i.succAbove j)) = ξ (c (ub i))) →
    (hilej : i < i.succAbove j) → (hlastlej : (hk : 0 < k) → b1 ⟨k - 1,Nat.sub_one_lt_of_lt hk⟩ < ub i) →
    (w : WickContract c ub b1) → WickContract c (ub ∘ i.succAbove ∘ j.succAbove) (Fin.snoc b1 (ub i))

namespace WickContract
variable {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n}

/-- The number of nodes of a Wick contraction. -/
def size {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    WickContract c ub b1 → ℕ := fun
  | string => 1
  | contr _ _ _ _ _ w => w.size + 1

def unbound {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    WickContract c ub b1 → Fin m → Fin n := fun _ => ub

@[simp]
lemma unbound_contr {n : ℕ} {c : Fin n → 𝓔} {m : ℕ} {ub : Fin m.succ.succ → Fin n} {k : ℕ}
    {b1 : Fin k → Fin n} (i : Fin m.succ.succ)
    (j : Fin m.succ)
    (h : c (ub (i.succAbove j)) = ξ (c (ub i)))
    (hilej : i < i.succAbove j)
    (hlastlej : (hk : 0 < k) → b1 ⟨k - 1,Nat.sub_one_lt_of_lt hk⟩ < ub i)
    (w : WickContract c ub b1) (r : Fin m) :
    (contr i j h hilej hlastlej w).unbound r = w.unbound (i.succAbove (j.succAbove r)) := rfl

lemma unbound_strictMono {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    (w : WickContract c ub b1) → StrictMono w.unbound := fun
  | string => by exact fun ⦃a b⦄ a => a
  | contr i j hij hilej hi w => by
    intro r s hrs
    refine w.unbound_strictMono ?_
    refine Fin.strictMono_succAbove _ ?_
    refine Fin.strictMono_succAbove _ hrs

def boundFst {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    WickContract c ub b1 → Fin k → Fin n := fun _ => b1

@[simp]
lemma boundFst_contr_castSucc {n : ℕ} {c : Fin n → 𝓔} {m : ℕ} {ub : Fin m.succ.succ → Fin n} {k : ℕ}
    {b1 : Fin k → Fin n} (i : Fin m.succ.succ)
    (j : Fin m.succ)
    (h : c (ub (i.succAbove j)) = ξ (c (ub i)))
    (hilej : i < i.succAbove j)
    (hlastlej : (hk : 0 < k) → b1 ⟨k - 1,Nat.sub_one_lt_of_lt hk⟩ < ub i)
    (w : WickContract c ub b1) (r : Fin k) :
    (contr i j h hilej hlastlej w).boundFst r.castSucc = w.boundFst r := by
  simp only [boundFst, Fin.snoc_castSucc]

@[simp]
lemma boundFst_contr_last {n : ℕ} {c : Fin n → 𝓔} {m : ℕ} {ub : Fin m.succ.succ → Fin n} {k : ℕ}
    {b1 : Fin k → Fin n} (i : Fin m.succ.succ)
    (j : Fin m.succ)
    (h : c (ub (i.succAbove j)) = ξ (c (ub i)))
    (hilej : i < i.succAbove j)
    (hlastlej : (hk : 0 < k) → b1 ⟨k - 1,Nat.sub_one_lt_of_lt hk⟩ < ub i)
    (w : WickContract c ub b1) :
    (contr i j h hilej hlastlej w).boundFst (Fin.last k) = ub i := by
  simp only [boundFst, Fin.snoc_last]

lemma boundFst_strictMono {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    (w : WickContract c ub b1) → StrictMono w.boundFst := fun
  | string => fun k => Fin.elim0 k
  | contr i j hij hilej hi w => by
    intro r s hrs
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        simp
        apply w.boundFst_strictMono _
        simpa using hrs
      · subst hs
        simp
        refine Fin.lt_of_le_of_lt ?_ (hi (Nat.zero_lt_of_lt hrs))
        · refine (StrictMono.monotone w.boundFst_strictMono) ?_
          rw [Fin.le_def]
          simp
          rw [Fin.lt_def] at hrs
          omega
    · subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        have hsp := s.prop
        rw [Fin.lt_def] at hrs
        simp at hrs
        omega
      · subst hs
        simp at hrs

def boundSnd {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    WickContract c ub b1 → Fin k → Fin n := fun
  | string => Fin.elim0
  | contr i j _  _ _ w => Fin.snoc w.boundSnd (w.unbound (i.succAbove j))

lemma boundFst_lt_boundSnd {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    (w : WickContract c ub b1) → (i : Fin k) → w.boundFst i < w.boundSnd i := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi w => fun r  => by
    simp only [boundFst, boundSnd, Nat.succ_eq_add_one]
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simpa using w.boundFst_lt_boundSnd r
    · subst hr
      simp
      change w.unbound _ < _
      apply w.unbound_strictMono hilej

lemma boundFst_dual_eq_boundSnd {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    (w : WickContract c ub b1) → (i : Fin k) → ξ (c (w.boundFst i)) = c (w.boundSnd i) := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi w => fun r => by
    simp only [boundFst, boundSnd, Nat.succ_eq_add_one]
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simpa using w.boundFst_dual_eq_boundSnd r
    · subst hr
      simp only [Fin.snoc_last]
      erw [hij]

@[simp]
lemma boundSnd_neq_unbound {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} : (w : WickContract c ub b1) →  (i : Fin k) →  (j : Fin m) →
     w.boundSnd i ≠ ub j := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi w => fun r s => by
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simp [boundSnd]
      exact w.boundSnd_neq_unbound _ _
    · subst hr
      simp [boundSnd]
      apply (StrictMono.injective w.unbound_strictMono).eq_iff.mp.mt
      apply Fin.succAbove_right_injective.eq_iff.mp.mt
      exact Fin.ne_succAbove j s

lemma boundSnd_injective {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n}: (w : WickContract c ub b1) → Function.Injective w.boundSnd := fun
  | string => by
    intro i j _
    exact Fin.elim0 i
  | contr i j hij hilej hi w => by
    intro r s hrs
    simp [boundSnd] at hrs
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        simp at hrs
        simpa using w.boundSnd_injective hrs
      · subst hs
        simp at hrs
        exact False.elim (w.boundSnd_neq_unbound r (i.succAbove j) hrs)
    · subst hr
      simp at hrs
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        simp at hrs
        exact False.elim (w.boundSnd_neq_unbound s (i.succAbove j) hrs.symm)
      · subst hs
        rfl

lemma no_fields_eq_unbound_plus_two_bound {n m k : ℕ} {c : Fin n → 𝓔} {ub : Fin m → Fin n} {b1 : Fin k → Fin n} :
    (w : WickContract c ub b1) → n = m + 2 * k := fun
  | string => rfl
  | contr i j hij hilej hi w => by
    rw [w.no_fields_eq_unbound_plus_two_bound]
    omega

end WickContract

end TwoComplexScalar
