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

inductive WickContract : {n : ℕ} → (f : FieldString n) →
    {k : ℕ} → (b1 : Fin k → Fin n) → (b2 : Fin k → Fin n) → Type where
  | string {n : ℕ} {c : Fin n → 𝓔} : WickContract c Fin.elim0 Fin.elim0
  | contr {n : ℕ} {c : Fin n → 𝓔}  {k : ℕ}
    {b1 : Fin k → Fin n}  {b2 : Fin k → Fin n}: (i : Fin n) →
    (j : Fin n) → (h : c j = ξ (c i)) →
    (hilej : i < j) → (hb1 : ∀ r, b1 r < i) → (hb2i : ∀ r, b2 r ≠ i) → (hb2j : ∀ r, b2 r ≠ j) →
    (w : WickContract c b1 b2) →
    WickContract c (Fin.snoc b1 i) (Fin.snoc b2 j)

namespace WickContract

/-- The number of nodes of a Wick contraction. -/
def size {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    WickContract c b1 b2 → ℕ := fun
  | string => 1
  | contr _ _ _ _ _ _ _ w => w.size + 1

def boundFst {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    WickContract c b1 b2 → Fin k → Fin n := fun _ => b1

@[simp]
lemma boundFst_contr_castSucc {n k : ℕ} {c : Fin n → 𝓔}
    {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract c b1 b2) (r : Fin k) :
    (contr i j h hilej hb1 hb2i hb2j w).boundFst r.castSucc = w.boundFst r := by
  simp only [boundFst, Fin.snoc_castSucc]

@[simp]
lemma boundFst_contr_last {n k : ℕ} {c : Fin n → 𝓔}
    {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract c b1 b2) :
    (contr i j h hilej hb1 hb2i hb2j w).boundFst (Fin.last k) = i := by
  simp only [boundFst, Fin.snoc_last]

lemma boundFst_strictMono {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    (w : WickContract c b1 b2) → StrictMono w.boundFst := fun
  | string => fun k => Fin.elim0 k
  | contr i j _ _ hb1 _ _  w => by
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
        exact hb1 r
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

def boundSnd {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    WickContract c b1 b2 → Fin k → Fin n := fun _ => b2

@[simp]
lemma boundSnd_contr_castSucc {n k : ℕ} {c : Fin n → 𝓔}
    {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract c b1 b2) (r : Fin k) :
    (contr i j h hilej hb1 hb2i hb2j w).boundSnd r.castSucc = w.boundSnd r := by
  simp only [boundSnd, Fin.snoc_castSucc]

@[simp]
lemma boundSnd_contr_last {n k : ℕ} {c : Fin n → 𝓔}
    {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract c b1 b2) :
    (contr i j h hilej hb1 hb2i hb2j w).boundSnd (Fin.last k) = j := by
  simp only [boundSnd, Fin.snoc_last]

lemma boundSnd_injective {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    (w : WickContract c b1 b2) → Function.Injective w.boundSnd := fun
  | string => by
    intro i j _
    exact Fin.elim0 i
  | contr i j hij hilej hi h2i h2j w => by
    intro r s hrs
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
        exact False.elim (h2j r hrs)
    · subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        simp at hrs
        exact False.elim (h2j s hrs.symm)
      · subst hs
        rfl

lemma color_boundSnd_eq_dual_boundFst {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    (w : WickContract c b1 b2) → (i : Fin k) → c (w.boundSnd i) = ξ (c (w.boundFst i)) := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi _ _ w => fun r => by
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simpa using w.color_boundSnd_eq_dual_boundFst r
    · subst hr
      simpa using hij

lemma boundFst_lt_boundSnd {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    (w : WickContract c b1 b2) → (i : Fin k) → w.boundFst i < w.boundSnd i := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi _ _ w => fun r => by
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simpa using w.boundFst_lt_boundSnd r
    · subst hr
      simp
      exact hilej

lemma boundFst_neq_boundSnd {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    (w : WickContract c b1 b2) → (r1 r2 : Fin k) → b1 r1 ≠ b2 r2 := fun
  | string => fun i => Fin.elim0 i
  | contr i j _ hilej h1 h2i h2j w => fun r s => by
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
      <;> rcases Fin.eq_castSucc_or_eq_last s with hs | hs
    · obtain ⟨r, hr⟩ := hr
      obtain ⟨s, hs⟩ := hs
      subst hr hs
      simpa using w.boundFst_neq_boundSnd r s
    · obtain ⟨r, hr⟩ := hr
      subst hr hs
      simp
      have hn := h1 r
      omega
    · obtain ⟨s, hs⟩ := hs
      subst hr hs
      simp
      exact (h2i s).symm
    · subst hr hs
      simp
      omega

def castMaps {n k k' : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} {b1' b2' : Fin k' → Fin n}
    (hk : k = k')
    (hb1 : b1 = b1' ∘ Fin.cast hk) (hb2 : b2 = b2' ∘ Fin.cast hk) (w : WickContract c b1 b2) :
    WickContract c b1' b2' :=
  cast (by subst hk; rfl) (hb2 ▸ hb1 ▸ w)

@[simp]
lemma castMaps_rfl {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} (w : WickContract c b1 b2) :
    castMaps rfl rfl rfl w = w := rfl

lemma mem_snoc' {n k : ℕ} {c : Fin n → 𝓔} {b1' b2' : Fin k → Fin n} :
    (w : WickContract c b1' b2') →
    {k' : ℕ} → (hk' : k'.succ = k ) →
    (b1 b2 : Fin k' → Fin n) → (i j : Fin n) → (h : c j = ξ (c i)) →
    (hilej : i < j) → (hb1 : ∀ r, b1 r < i) → (hb2i : ∀ r, b2 r ≠ i) → (hb2j : ∀ r, b2 r ≠ j) →
    (hb1' : Fin.snoc b1 i  =  b1' ∘ Fin.cast hk') →
    (hb2' : Fin.snoc b2 j  = b2' ∘ Fin.cast hk') →
     ∃ (w' : WickContract c b1 b2), w = castMaps hk' hb1' hb2' (contr i j h hilej hb1 hb2i hb2j w')
     := fun
  | string => fun hk'  => by
    simp at hk'
  | contr i' j' h' hilej' hb1' hb2i' hb2j' w' => by
    intro hk b1 b2 i j h hilej hb1 hb2i hb2j hb1' hb2'
    rename_i k' k b1' b2' f
    have hk2 : k' = k := Nat.succ_inj'.mp hk
    subst hk2
    simp_all
    have hb2'' : b2 = b2' := by
      funext k
      trans (@Fin.snoc k' (fun _ => Fin n) b2 j) (Fin.castSucc k)
      · simp
      · rw [hb2']
        simp
    have hb1'' : b1 = b1' := by
      funext k
      trans (@Fin.snoc k' (fun _ => Fin n) b1 i) (Fin.castSucc k)
      · simp
      · rw [hb1']
        simp
    have hi : i = i' := by
      trans  (@Fin.snoc k' (fun _ => Fin n) b1 i) (Fin.last k')
      · simp
      · rw [hb1']
        simp
    have hj : j = j' := by
      trans  (@Fin.snoc k' (fun _ => Fin n) b2 j) (Fin.last k')
      · simp
      · rw [hb2']
        simp
    subst hb1'' hb2'' hi hj
    simp


lemma mem_snoc {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract c (Fin.snoc b1 i) (Fin.snoc b2 j)) :
    ∃ (w' : WickContract c b1 b2), w = contr i j h hilej hb1 hb2i hb2j w' := by
  exact mem_snoc' w rfl b1 b2 i j h hilej hb1 hb2i hb2j rfl rfl

lemma is_subsingleton {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n} :
    Subsingleton (WickContract c b1 b2) := Subsingleton.intro fun w1 w2  => by
  induction k with
  | zero =>
    have hb1 : b1 = Fin.elim0 := Subsingleton.elim _ _
    have hb2 : b2 = Fin.elim0 := Subsingleton.elim _ _
    subst hb1 hb2
    match w1, w2 with
    | string, string => rfl
  | succ k hI =>
    match w1, w2 with
    | contr i j h hilej hb1 hb2i hb2j w, w2 =>
      let ⟨w', hw'⟩ := mem_snoc i j h hilej hb1 hb2i hb2j w2
      rw [hw']
      apply congrArg (contr i j _ _ _ _ _) (hI w w')

lemma eq_snoc_castSucc {k n : ℕ} (b1 : Fin k.succ → Fin n) :
  b1 = Fin.snoc (b1 ∘ Fin.castSucc) (b1 (Fin.last k)) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with h1 | h1
  · obtain ⟨i, rfl⟩ := h1
    simp
  · subst h1
    simp

def fromMaps {n k : ℕ} (c : Fin n → 𝓔) (b1 b2 : Fin k → Fin n)
    (hi : ∀ i, c (b2 i) = ξ (c (b1 i)))
    (hb1ltb2 : ∀ i, b1 i < b2 i)
    (hb1 : StrictMono b1)
    (hb1neb2 : ∀ r1 r2, b1 r1 ≠ b2 r2)
    (hb2 : Function.Injective b2) :
    WickContract c b1 b2 := by
  match k with
  | 0 =>
    refine castMaps ?_ ?_ ?_ string
    · rfl
    · exact funext (fun i => Fin.elim0 i)
    · exact funext (fun i => Fin.elim0 i)
  | Nat.succ k =>
    refine castMaps rfl (eq_snoc_castSucc b1).symm (eq_snoc_castSucc b2).symm
      (contr (b1 (Fin.last k)) (b2 (Fin.last k)) (hi (Fin.last k)) (hb1ltb2 (Fin.last k)) (fun r => hb1 (Fin.castSucc_lt_last r)) ?_ ?_
      (fromMaps c (b1 ∘ Fin.castSucc) (b2 ∘ Fin.castSucc) (fun i => hi (Fin.castSucc i))
        (fun i => hb1ltb2 (Fin.castSucc i)) (StrictMono.comp hb1 Fin.strictMono_castSucc)
        ?_ ?_
      ))
    · exact fun r a => hb1neb2 (Fin.last k) r.castSucc a.symm
    · exact fun r => hb2.eq_iff.mp.mt (Fin.ne_last_of_lt (Fin.castSucc_lt_last r ))
    · exact fun r1 r2 => hb1neb2 r1.castSucc r2.castSucc
    · exact Function.Injective.comp hb2 (Fin.castSucc_injective k)

lemma eq_from_maps {n k : ℕ} {c : Fin n → 𝓔} {b1 b2 : Fin k → Fin n}
    (w : WickContract c b1 b2) :
    w = fromMaps c w.boundFst w.boundSnd w.color_boundSnd_eq_dual_boundFst
      w.boundFst_lt_boundSnd w.boundFst_strictMono w.boundFst_neq_boundSnd w.boundSnd_injective := by
  exact is_subsingleton.allEq w _

structure struc {n : ℕ} (c : Fin n → 𝓔) where
  k : ℕ
  b1 : Fin k ↪o Fin n
  b2 : Fin k ↪ Fin n
  b2_color_eq_dual_b1 : ∀ i, c (b2 i) = ξ (c (b1 i))
  b1_lt_b2 : ∀ i, b1 i < b2 i
  b1_neq_b2 : ∀ r1 r2, b1 r1 ≠ b2 r2

def strucEquivSigma {n : ℕ} (c : Fin n → 𝓔) :
    struc c ≃ Σ (k : ℕ) (b1 : Fin k → Fin n) (b2 : Fin k → Fin n), WickContract c b1 b2 where
  toFun s := ⟨s.k, s.b1, s.b2, fromMaps c s.b1 s.b2 s.b2_color_eq_dual_b1
    s.b1_lt_b2 s.b1.strictMono s.b1_neq_b2 s.b2.inj'⟩
  invFun x :=
    match x with
    | ⟨k, b1, b2, w⟩ => ⟨k, OrderEmbedding.ofStrictMono b1 w.boundFst_strictMono,
      ⟨b2, w.boundSnd_injective⟩,
      w.color_boundSnd_eq_dual_boundFst, w.boundFst_lt_boundSnd, w.boundFst_neq_boundSnd⟩
  left_inv s := rfl
  right_inv w := by
    match w with
    | ⟨k, b1, b2, w⟩ =>
      simp only [OrderEmbedding.coe_ofStrictMono, Function.Embedding.coeFn_mk, Sigma.mk.inj_iff,
        heq_eq_eq, true_and]
      exact (eq_from_maps w).symm


end WickContract

end TwoComplexScalar
