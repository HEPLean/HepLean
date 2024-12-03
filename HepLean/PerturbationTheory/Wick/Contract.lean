/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.String
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin
/-!

# Wick Contract

Currently this file is only for an example of Wick contracts, correpsonding to a
theory with two complex scalar fields. The concepts will however generalize.

## Further reading

- https://www.imperial.ac.uk/media/imperial-college/research-centres-and-groups/theoretical-physics/msc/current/qft/handouts/qftwickstheorem.pdf

-/

namespace TwoComplexScalar

/-- A Wick contraction for a Wick string is a series of pairs `i` and `j` of indices
  to be contracted, subject to ordering and subject to the condition that they can
  be contracted. -/
inductive WickContract : {ni : ℕ} → {i : Fin ni → 𝓔} → {n : ℕ} → {c : Fin n → 𝓔} →
    {no : ℕ} → {o : Fin no → 𝓔} →
    (str : WickString i c o final) →
    {k : ℕ} → (b1 : Fin k → Fin n) → (b2 : Fin k → Fin n) → Type where
  | string {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final} : WickContract str Fin.elim0 Fin.elim0
  | contr {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final} {k : ℕ}
    {b1 : Fin k → Fin n} {b2 : Fin k → Fin n} : (i : Fin n) →
    (j : Fin n) → (h : c j = ξ (c i)) →
    (hilej : i < j) → (hb1 : ∀ r, b1 r < i) → (hb2i : ∀ r, b2 r ≠ i) → (hb2j : ∀ r, b2 r ≠ j) →
    (w : WickContract str b1 b2) →
    WickContract str (Fin.snoc b1 i) (Fin.snoc b2 j)

namespace WickContract

/-- The number of nodes of a Wick contraction. -/
def size {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final} {k : ℕ} {b1 b2 : Fin k → Fin n} :
    WickContract str b1 b2 → ℕ := fun
  | string => 0
  | contr _ _ _ _ _ _ _ w => w.size + 1

/-- The number of nodes in a wick contraction tree is the same as `k`. -/
lemma size_eq_k {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final} {k : ℕ} {b1 b2 : Fin k → Fin n} :
    (w : WickContract str b1 b2) → w.size = k := fun
  | string => rfl
  | contr _ _ _ _ _ _ _ w => by
    simpa [size] using w.size_eq_k

/-- The map giving the vertices on the left-hand-side of a contraction. -/
@[nolint unusedArguments]
def boundFst {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} :
    WickContract str b1 b2 → Fin k → Fin n := fun _ => b1

@[simp]
lemma boundFst_contr_castSucc {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract str b1 b2) (r : Fin k) :
    (contr i j h hilej hb1 hb2i hb2j w).boundFst r.castSucc = w.boundFst r := by
  simp only [boundFst, Fin.snoc_castSucc]

@[simp]
lemma boundFst_contr_last {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract str b1 b2) :
    (contr i j h hilej hb1 hb2i hb2j w).boundFst (Fin.last k) = i := by
  simp only [boundFst, Fin.snoc_last]

lemma boundFst_strictMono {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} : (w : WickContract str b1 b2) → StrictMono w.boundFst := fun
  | string => fun k => Fin.elim0 k
  | contr i j _ _ hb1 _ _ w => by
    intro r s hrs
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        simp only [boundFst_contr_castSucc]
        apply w.boundFst_strictMono _
        simpa using hrs
      · subst hs
        simp only [boundFst_contr_castSucc, boundFst_contr_last]
        exact hb1 r
    · subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        rw [Fin.lt_def] at hrs
        simp only [Fin.val_last, Fin.coe_castSucc] at hrs
        omega
      · subst hs
        simp at hrs

/-- The map giving the vertices on the right-hand-side of a contraction. -/
@[nolint unusedArguments]
def boundSnd {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} :
    WickContract str b1 b2 → Fin k → Fin n := fun _ => b2

@[simp]
lemma boundSnd_contr_castSucc {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract str b1 b2) (r : Fin k) :
    (contr i j h hilej hb1 hb2i hb2j w).boundSnd r.castSucc = w.boundSnd r := by
  simp only [boundSnd, Fin.snoc_castSucc]

@[simp]
lemma boundSnd_contr_last {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (i j : Fin n)
    (h : c j = ξ (c i))
    (hilej : i < j)
    (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i)
    (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract str b1 b2) :
    (contr i j h hilej hb1 hb2i hb2j w).boundSnd (Fin.last k) = j := by
  simp only [boundSnd, Fin.snoc_last]

lemma boundSnd_injective {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} :
    (w : WickContract str b1 b2) → Function.Injective w.boundSnd := fun
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
        simp only [boundSnd_contr_castSucc] at hrs
        simpa using w.boundSnd_injective hrs
      · subst hs
        simp only [boundSnd_contr_castSucc, boundSnd_contr_last] at hrs
        exact False.elim (h2j r hrs)
    · subst hr
      rcases Fin.eq_castSucc_or_eq_last s with hs | hs
      · obtain ⟨s, hs⟩ := hs
        subst hs
        simp only [boundSnd_contr_last, boundSnd_contr_castSucc] at hrs
        exact False.elim (h2j s hrs.symm)
      · subst hs
        rfl

lemma color_boundSnd_eq_dual_boundFst {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} :
    (w : WickContract str b1 b2) → (i : Fin k) → c (w.boundSnd i) = ξ (c (w.boundFst i)) := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi _ _ w => fun r => by
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simpa using w.color_boundSnd_eq_dual_boundFst r
    · subst hr
      simpa using hij

lemma boundFst_lt_boundSnd {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} : (w : WickContract str b1 b2) → (i : Fin k) →
    w.boundFst i < w.boundSnd i := fun
  | string => fun i => Fin.elim0 i
  | contr i j hij hilej hi _ _ w => fun r => by
    rcases Fin.eq_castSucc_or_eq_last r with hr | hr
    · obtain ⟨r, hr⟩ := hr
      subst hr
      simpa using w.boundFst_lt_boundSnd r
    · subst hr
      simp only [boundFst_contr_last, boundSnd_contr_last]
      exact hilej

lemma boundFst_neq_boundSnd {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} :
    (w : WickContract str b1 b2) → (r1 r2 : Fin k) → b1 r1 ≠ b2 r2 := fun
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
      simp only [Fin.snoc_castSucc, Fin.snoc_last, ne_eq]
      have hn := h1 r
      omega
    · obtain ⟨s, hs⟩ := hs
      subst hr hs
      simp only [Fin.snoc_last, Fin.snoc_castSucc, ne_eq]
      exact (h2i s).symm
    · subst hr hs
      simp only [Fin.snoc_last, ne_eq]
      omega

/-- Casts a Wick contraction from `WickContract str b1 b2` to `WickContract str b1' b2'` with a
  proof that `b1 = b1'` and `b2 = b2'`, and that they are defined from the same `k = k'`. -/
def castMaps {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k k' : ℕ} {b1 b2 : Fin k → Fin n} {b1' b2' : Fin k' → Fin n}
    (hk : k = k')
    (hb1 : b1 = b1' ∘ Fin.cast hk) (hb2 : b2 = b2' ∘ Fin.cast hk) (w : WickContract str b1 b2) :
    WickContract str b1' b2' :=
  cast (by subst hk; rfl) (hb2 ▸ hb1 ▸ w)

@[simp]
lemma castMaps_rfl {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (w : WickContract str b1 b2) :
    castMaps rfl rfl rfl w = w := rfl

lemma mem_snoc' {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1' b2' : Fin k → Fin n} :
    (w : WickContract str b1' b2') →
    {k' : ℕ} → (hk' : k'.succ = k) →
    (b1 b2 : Fin k' → Fin n) → (i j : Fin n) → (h : c j = ξ (c i)) →
    (hilej : i < j) → (hb1 : ∀ r, b1 r < i) → (hb2i : ∀ r, b2 r ≠ i) → (hb2j : ∀ r, b2 r ≠ j) →
    (hb1' : Fin.snoc b1 i = b1' ∘ Fin.cast hk') →
    (hb2' : Fin.snoc b2 j = b2' ∘ Fin.cast hk') →
    ∃ (w' : WickContract str b1 b2), w = castMaps hk' hb1' hb2'
      (contr i j h hilej hb1 hb2i hb2j w') := fun
  | string => fun hk' => by
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
      trans (@Fin.snoc k' (fun _ => Fin n) b1 i) (Fin.last k')
      · simp
      · rw [hb1']
        simp
    have hj : j = j' := by
      trans (@Fin.snoc k' (fun _ => Fin n) b2 j) (Fin.last k')
      · simp
      · rw [hb2']
        simp
    subst hb1'' hb2'' hi hj
    simp

lemma mem_snoc {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (i j : Fin n) (h : c j = ξ (c i)) (hilej : i < j) (hb1 : ∀ r, b1 r < i)
    (hb2i : ∀ r, b2 r ≠ i) (hb2j : ∀ r, b2 r ≠ j)
    (w : WickContract str (Fin.snoc b1 i) (Fin.snoc b2 j)) :
    ∃ (w' : WickContract str b1 b2), w = contr i j h hilej hb1 hb2i hb2j w' := by
  exact mem_snoc' w rfl b1 b2 i j h hilej hb1 hb2i hb2j rfl rfl

lemma is_subsingleton {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} :
    Subsingleton (WickContract str b1 b2) := Subsingleton.intro fun w1 w2 => by
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

/-- The construction of a Wick contraction from maps `b1 b2 : Fin k → Fin n`, with the former
  giving the first index to be contracted, and the latter the second index. These
  maps must satisfy a series of conditions. -/
def fromMaps {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} (b1 b2 : Fin k → Fin n)
    (hi : ∀ i, c (b2 i) = ξ (c (b1 i)))
    (hb1ltb2 : ∀ i, b1 i < b2 i)
    (hb1 : StrictMono b1)
    (hb1neb2 : ∀ r1 r2, b1 r1 ≠ b2 r2)
    (hb2 : Function.Injective b2) :
    WickContract str b1 b2 := by
  match k with
  | 0 =>
    refine castMaps ?_ ?_ ?_ string
    · rfl
    · exact funext (fun i => Fin.elim0 i)
    · exact funext (fun i => Fin.elim0 i)
  | Nat.succ k =>
    refine castMaps rfl (eq_snoc_castSucc b1).symm (eq_snoc_castSucc b2).symm
      (contr (b1 (Fin.last k)) (b2 (Fin.last k))
        (hi (Fin.last k))
        (hb1ltb2 (Fin.last k))
        (fun r => hb1 (Fin.castSucc_lt_last r))
        (fun r a => hb1neb2 (Fin.last k) r.castSucc a.symm)
        (fun r => hb2.eq_iff.mp.mt (Fin.ne_last_of_lt (Fin.castSucc_lt_last r)))
      (fromMaps (b1 ∘ Fin.castSucc) (b2 ∘ Fin.castSucc) (fun i => hi (Fin.castSucc i))
        (fun i => hb1ltb2 (Fin.castSucc i)) (StrictMono.comp hb1 Fin.strictMono_castSucc)
        ?_ ?_))
    · exact fun r1 r2 => hb1neb2 r1.castSucc r2.castSucc
    · exact Function.Injective.comp hb2 (Fin.castSucc_injective k)

/-- Given a Wick contraction with `k.succ` contractions, returns the Wick contraction with
  `k` contractions by dropping the last contraction (defined by the first index contracted). -/
def dropLast {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k.succ → Fin n}
    (w : WickContract str b1 b2) : WickContract str (b1 ∘ Fin.castSucc) (b2 ∘ Fin.castSucc) :=
  fromMaps (b1 ∘ Fin.castSucc) (b2 ∘ Fin.castSucc)
    (fun i => color_boundSnd_eq_dual_boundFst w i.castSucc)
    (fun i => boundFst_lt_boundSnd w i.castSucc)
    (StrictMono.comp w.boundFst_strictMono Fin.strictMono_castSucc)
    (fun r1 r2 => boundFst_neq_boundSnd w r1.castSucc r2.castSucc)
    (Function.Injective.comp w.boundSnd_injective (Fin.castSucc_injective k))

lemma eq_from_maps {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) :
    w = fromMaps w.boundFst w.boundSnd w.color_boundSnd_eq_dual_boundFst
      w.boundFst_lt_boundSnd w.boundFst_strictMono w.boundFst_neq_boundSnd
      w.boundSnd_injective := is_subsingleton.allEq w _

lemma eq_dropLast_contr {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k.succ → Fin n} (w : WickContract str b1 b2) :
  w = castMaps rfl (eq_snoc_castSucc b1).symm (eq_snoc_castSucc b2).symm
    (contr (b1 (Fin.last k)) (b2 (Fin.last k))
      (w.color_boundSnd_eq_dual_boundFst (Fin.last k))
      (w.boundFst_lt_boundSnd (Fin.last k))
      (fun r => w.boundFst_strictMono (Fin.castSucc_lt_last r))
      (fun r a => w.boundFst_neq_boundSnd (Fin.last k) r.castSucc a.symm)
      (fun r => w.boundSnd_injective.eq_iff.mp.mt (Fin.ne_last_of_lt (Fin.castSucc_lt_last r)))
    (dropLast w)) := by
  rw [eq_from_maps w]
  rfl

/-- Wick contractions of a given Wick string with `k` different contractions. -/
def Level {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} (str : WickString i c o final) (k : ℕ) : Type :=
  Σ (b1 : Fin k → Fin n) (b2 : Fin k → Fin n), WickContract str b1 b2

/-- There is a finite number of Wick contractions with no contractions. In particular,
  this is just the original Wick string. -/
instance levelZeroFintype {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} (str : WickString i c o final) :
    Fintype (Level str 0) where
  elems := {⟨Fin.elim0, Fin.elim0, WickContract.string⟩}
  complete := by
    intro x
    match x with
    | ⟨b1, b2, w⟩ =>
      have hb1 : b1 = Fin.elim0 := Subsingleton.elim _ _
      have hb2 : b2 = Fin.elim0 := Subsingleton.elim _ _
      subst hb1 hb2
      simp only [Finset.mem_singleton]
      rw [is_subsingleton.allEq w string]

/-- The pairs of additional indices which can be contracted given a Wick contraction. -/
structure ContrPair {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) where
  /-- The first index in the contraction pair. -/
  i : Fin n
  /-- The second index in the contraction pair. -/
  j : Fin n
  h : c j = ξ (c i)
  hilej : i < j
  hb1 : ∀ r, b1 r < i
  hb2i : ∀ r, b2 r ≠ i
  hb2j : ∀ r, b2 r ≠ j

/-- The pairs of additional indices which can be contracted, given an existing wick contraction,
  is equivalent to the a subtype of `Fin n × Fin n` defined by certain conditions equivalent
  to the conditions appearing in `ContrPair`. -/
def contrPairEquivSubtype {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (w : WickContract str b1 b2) :
    ContrPair w ≃ {x : Fin n × Fin n // c x.2 = ξ (c x.1) ∧ x.1 < x.2 ∧
      (∀ r, b1 r < x.1) ∧ (∀ r, b2 r ≠ x.1) ∧ (∀ r, b2 r ≠ x.2)} where
  toFun cp := ⟨⟨cp.i, cp.j⟩, ⟨cp.h, cp.hilej, cp.hb1, cp.hb2i, cp.hb2j⟩⟩
  invFun x :=
    match x with
    | ⟨⟨i, j⟩, ⟨h, hilej, hb1, hb2i, hb2j⟩⟩ => ⟨i, j, h, hilej, hb1, hb2i, hb2j⟩
  left_inv x := by rfl
  right_inv x := by
    simp_all only [ne_eq]
    obtain ⟨val, property⟩ := x
    obtain ⟨fst, snd⟩ := val
    obtain ⟨left, right⟩ := property
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    obtain ⟨left_3, right⟩ := right
    simp_all only [ne_eq]

lemma heq_eq {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 b1' b2' : Fin k → Fin n}
    (w : WickContract str b1 b2)
    (w' : WickContract str b1' b2') (h1 : b1 = b1') (h2 : b2 = b2') : HEq w w':= by
  subst h1 h2
  simp only [heq_eq_eq]
  exact is_subsingleton.allEq w w'

/-- The equivalence between Wick contractions consisting of `k.succ` contractions and
  those with `k` contractions paired with a suitable contraction pair. -/
def levelSuccEquiv {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} (str : WickString i c o final) (k : ℕ) :
    Level str k.succ ≃ (w : Level str k) × ContrPair w.2.2 where
  toFun w :=
    match w with
    | ⟨b1, b2, w⟩ =>
    ⟨⟨b1 ∘ Fin.castSucc, b2 ∘ Fin.castSucc, dropLast w⟩,
      ⟨b1 (Fin.last k), b2 (Fin.last k),
      w.color_boundSnd_eq_dual_boundFst (Fin.last k),
      w.boundFst_lt_boundSnd (Fin.last k),
      fun r => w.boundFst_strictMono (Fin.castSucc_lt_last r),
      fun r a => w.boundFst_neq_boundSnd (Fin.last k) r.castSucc a.symm,
      fun r => w.boundSnd_injective.eq_iff.mp.mt (Fin.ne_last_of_lt (Fin.castSucc_lt_last r))⟩⟩
  invFun w :=
    match w with
    | ⟨⟨b1, b2, w⟩, cp⟩ => ⟨Fin.snoc b1 cp.i, Fin.snoc b2 cp.j,
      contr cp.i cp.j cp.h cp.hilej cp.hb1 cp.hb2i cp.hb2j w⟩
  left_inv w := by
    match w with
    | ⟨b1, b2, w⟩ =>
      simp only [Nat.succ_eq_add_one, Function.comp_apply]
      congr
      · exact Eq.symm (eq_snoc_castSucc b1)
      · funext b2
        congr
        exact Eq.symm (eq_snoc_castSucc b1)
      · exact Eq.symm (eq_snoc_castSucc b2)
      · rw [eq_dropLast_contr w]
        simp only [castMaps, Nat.succ_eq_add_one, cast_eq, heq_eqRec_iff_heq, heq_eq_eq,
          contr.injEq]
        rfl
  right_inv w := by
    match w with
    | ⟨⟨b1, b2, w⟩, cp⟩ =>
      simp only [Nat.succ_eq_add_one, Fin.snoc_last, Sigma.mk.inj_iff]
      apply And.intro
      · congr
        · exact Fin.snoc_comp_castSucc
        · funext b2
          congr
          exact Fin.snoc_comp_castSucc
        · exact Fin.snoc_comp_castSucc
        · exact heq_eq _ _ Fin.snoc_comp_castSucc Fin.snoc_comp_castSucc
      · congr
        · exact Fin.snoc_comp_castSucc
        · exact Fin.snoc_comp_castSucc
        · exact heq_eq _ _ Fin.snoc_comp_castSucc Fin.snoc_comp_castSucc
        · simp
        · simp
        · simp

/-- The sum of `boundFst` and `boundSnd`, giving on `Sum.inl k` the first index
  in the `k`th contraction, and on `Sum.inr k` the second index in the `k`th contraction. -/
def bound {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) : Fin k ⊕ Fin k → Fin n :=
  Sum.elim w.boundFst w.boundSnd

/-- On `Sum.inl k` the map `bound` acts via `boundFst`. -/
@[simp]
lemma bound_inl {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) (i : Fin k) : w.bound (Sum.inl i) = w.boundFst i := rfl

/-- On `Sum.inr k` the map `bound` acts via `boundSnd`. -/
@[simp]
lemma bound_inr {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) (i : Fin k) : w.bound (Sum.inr i) = w.boundSnd i := rfl

lemma bound_injection {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) : Function.Injective w.bound := by
  intro x y h
  match x, y with
  | Sum.inl x, Sum.inl y =>
    simp only [bound_inl] at h
    simpa using (StrictMono.injective w.boundFst_strictMono).eq_iff.mp h
  | Sum.inr x, Sum.inr y =>
    simp only [bound_inr] at h
    simpa using w.boundSnd_injective h
  | Sum.inl x, Sum.inr y =>
    simp only [bound_inl, bound_inr] at h
    exact False.elim (w.boundFst_neq_boundSnd x y h)
  | Sum.inr x, Sum.inl y =>
    simp only [bound_inr, bound_inl] at h
    exact False.elim (w.boundFst_neq_boundSnd y x h.symm)

lemma bound_le_total {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) : 2 * k ≤ n := by
  refine Fin.nonempty_embedding_iff.mp ⟨w.bound ∘ finSumFinEquiv.symm ∘ Fin.cast (Nat.two_mul k),
    ?_⟩
  apply Function.Injective.comp (Function.Injective.comp _ finSumFinEquiv.symm.injective)
  · exact Fin.cast_injective (Nat.two_mul k)
  · exact bound_injection w

/-- The list of fields (indexed by `Fin n`) in a Wick contraction which are not bound,
  i.e. which do not appear in any contraction. -/
def unboundList {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) : List (Fin n) :=
  List.filter (fun i => decide (∀ r, w.bound r ≠ i)) (List.finRange n)

/-- THe list of field positions which are not contracted has no duplicates. -/
lemma unboundList_nodup {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) : (w.unboundList).Nodup :=
    List.Nodup.filter _ (List.nodup_finRange n)

/-- The length of the `unboundList` is equal to `n - 2 * k`. That is
  the total number of fields minus the number of contracted fields. -/
lemma unboundList_length {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (w : WickContract str b1 b2) :
    w.unboundList.length = n - 2 * k := by
  rw [← List.Nodup.dedup w.unboundList_nodup]
  rw [← List.card_toFinset, unboundList]
  rw [List.toFinset_filter, List.toFinset_finRange]
  have hn := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
    (fun (i : Fin n) => i ∈ Finset.image w.bound Finset.univ)
  have hn' :(Finset.filter (fun i => i ∈ Finset.image w.bound Finset.univ) Finset.univ).card =
      (Finset.image w.bound Finset.univ).card := by
    refine Finset.card_equiv (Equiv.refl _) fun i => ?_
    simp
  rw [hn'] at hn
  rw [Finset.card_image_of_injective] at hn
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    Finset.mem_univ, true_and, Sum.exists, bound_inl, bound_inr, not_or, not_exists] at hn
  have hn'' : (Finset.filter (fun a => a ∉ Finset.image w.bound Finset.univ) Finset.univ).card =
      n - 2 * k := by
    omega
  rw [← hn'']
  congr
  funext x
  simp only [ne_eq, Sum.forall, bound_inl, bound_inr, Bool.decide_and, Bool.and_eq_true,
    decide_eq_true_eq, Finset.mem_image, Finset.mem_univ, true_and, Sum.exists, not_or, not_exists]
  exact bound_injection w

lemma unboundList_sorted {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n} (w : WickContract str b1 b2) :
    List.Sorted (fun i j => i < j) w.unboundList :=
  List.Pairwise.sublist (List.filter_sublist (List.finRange n)) (List.pairwise_lt_finRange n)

/-- The ordered embedding giving the fields which are not bound in a contraction. These
  are the fields that will appear in a normal operator in Wick's theorem. -/
def unbound {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔}
    {no : ℕ} {o : Fin no → 𝓔} {str : WickString i c o final}
    {k : ℕ} {b1 b2 : Fin k → Fin n}
    (w : WickContract str b1 b2) : Fin (n - 2 * k) ↪o Fin n where
  toFun := w.unboundList.get ∘ Fin.cast w.unboundList_length.symm
  inj' := by
    apply Function.Injective.comp
    · rw [← List.nodup_iff_injective_get]
      exact w.unboundList_nodup
    · exact Fin.cast_injective _
  map_rel_iff' := by
    refine fun {a b} => StrictMono.le_iff_le ?_
    rw [Function.Embedding.coeFn_mk]
    apply StrictMono.comp
    · exact List.Sorted.get_strictMono w.unboundList_sorted
    · exact fun ⦃a b⦄ a => a

informal_lemma level_fintype where
  math :≈ "Level is a finite type, as there are only finitely many ways to contract a Wick string."
  deps :≈ [``Level]

informal_definition HasEqualTimeContractions where
  math :≈ "The condition for a Wick contraction to have two fields contracted
    which are of equal time, i.e. come from the same vertex."
  deps :≈ [``WickContract]

informal_definition IsConnected where
  math :≈ "The condition for a full Wick contraction that for any two vertices
    (including external vertices) are connected by contractions."
  deps :≈ [``WickContract]

informal_definition HasVacuumContributions where
  math :≈ "The condition for a full Wick contraction to have a vacuum contribution."
  deps :≈ [``WickContract]

informal_definition IsOneParticleIrreducible where
  math :≈ "The condition for a full Wick contraction to be one-particle irreducible."
  deps :≈ [``WickContract]

end WickContract

end TwoComplexScalar
