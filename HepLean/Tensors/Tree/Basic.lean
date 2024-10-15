/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Iso
import HepLean.Tensors.OverColor.Discrete
import HepLean.Tensors.OverColor.Lift
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
/-!

## Tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

/-- The sturcture of a type of tensors e.g. Lorentz tensors, Einstien tensors,
  complex Lorentz tensors.
  Note: This structure is not fully defined yet. -/
structure TensorStruct where
  /-- The colors of indices e.g. up or down. -/
  C : Type
  /-- The symmetry group acting on these tensor e.g. the Lorentz group or SL(2,ℂ). -/
  G : Type
  /-- An instance of `G` as a group. -/
  G_group : Group G
  /-- The field over which we want to consider the tensors to live in, usually `ℝ` or `ℂ`. -/
  k : Type
  /-- An instance of `k` as a commutative ring. -/
  k_commRing : CommRing k
  /-- A `MonoidalFunctor` from `OverColor C` giving the rep corresponding to a map of colors
    `X → C`. -/
  FDiscrete : Discrete C ⥤ Rep k G
  /-- A map from `C` to `C`. An involution. -/
  τ : C → C
  τ_involution : Function.Involutive τ
  /-- The natural transformation describing contraction. -/
  contr : OverColor.Discrete.pairτ F τ ⟶ 𝟙_ (Discrete C ⥤ Rep k G)
  /-- The natural transformation describing the metric. -/
  metricNat : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.pair FDiscrete
  /-- The natural transformation describing the unit. -/
  unit : 𝟙_ (Discrete C ⥤ Rep k G) ⟶ OverColor.Discrete.τPair FDiscrete τ
  /-- A specification of the dimension of each color in C. This will be used for explicit
    evaluation of tensors. -/
  evalNo : C → ℕ

noncomputable section

namespace TensorStruct

variable (S : TensorStruct)

instance : CommRing S.k := S.k_commRing

instance : Group S.G := S.G_group

/-- The lift of the functor `S.F` to a monoidal functor. -/
def F : MonoidalFunctor (OverColor S.C) (Rep S.k S.G) := (OverColor.lift).obj S.FDiscrete

def metric (c : S.C) : S.F.obj (OverColor.mk ![c, c]) :=
  (OverColor.Discrete.pairIso S.FDiscrete c).hom.hom <|
  (S.metricNat.app (Discrete.mk c)).hom (1 : S.k)

def contrNLE {n : ℕ} {i j : Fin n} (h : i ≠ j) : 2 ≤ n := by
  omega

def contrNPred {n : ℕ} {i j : Fin n} (h : i ≠ j) : n.pred.pred.succ.succ = n := by
  simp_all only [ne_eq, Nat.pred_eq_sub_one, Nat.succ_eq_add_one]
  have hi : i < n := i.isLt
  have hj : j < n := j.isLt
  by_contra hn
  have hn : n  = 0 ∨ n =1 := by omega
  cases hn
  · omega
  · omega

def contrFstSucc {n : ℕ} {i j : Fin n} (hineqj : i ≠ j) :
    Fin n.pred.pred.succ.succ := Fin.castOrderIso (contrNPred hineqj).symm i

def contrSndSucc {n : ℕ} {i j : Fin n} (hineqj : i ≠ j) :
    Fin n.pred.pred.succ := (Fin.predAbove 0 (contrFstSucc hineqj)).predAbove
    (Fin.castOrderIso (contrNPred hineqj).symm j)

@[simp]
lemma contrSndSucc_succAbove {n : ℕ} {i j : Fin n} (hineqj : i ≠ j) :
    (contrFstSucc hineqj).succAbove (contrSndSucc hineqj) =
    Fin.castOrderIso (contrNPred hineqj).symm j := by
  simp [contrFstSucc, contrSndSucc, Fin.succAbove,
    Fin.predAbove]
  split_ifs
  · rename_i h1 h2
    rw [Fin.lt_def] at h1 h2
    simp_all [Fin.lt_def, Fin.ext_iff]
    intro h
    omega
  · rename_i h1 h2
    rw [Fin.lt_def] at h1 h2
    simp_all [Fin.ext_iff]
    rw [Fin.lt_def]
    simp only [Fin.coe_cast, Fin.val_fin_lt]
    rw [Fin.lt_def]
    omega
  · rename_i h1 h2
    rw [Fin.lt_def] at h1 h2
    simp_all [Fin.ext_iff]
    rw [Fin.lt_def]
    simp only [Fin.coe_cast, Fin.val_fin_lt]
    omega
  · rename_i h1 h2
    rw [Fin.lt_def] at h1 h2
    simp_all [Fin.ext_iff]
    rw [Fin.lt_def]
    simp only [Fin.coe_cast, Fin.val_fin_lt]
    omega


def contrIso {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ≅ ((OverColor.Discrete.pairτ S.FDiscrete S.τ).obj (Discrete.mk (c i))) ⊗
      (OverColor.lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (S.F.mapIso (OverColor.equivToIso (OverColor.finExtractTwo i j))).trans <|
  (S.F.mapIso (OverColor.mkSum (c ∘ (OverColor.finExtractTwo i j).symm))).trans <|
  (S.F.μIso _ _).symm.trans <| by
  refine tensorIso ?_ (S.F.mapIso (OverColor.mkIso (by ext x; simp)))
  apply (S.F.mapIso (OverColor.mkSum (((c ∘ ⇑(OverColor.finExtractTwo i j).symm) ∘ Sum.inl)))).trans
  apply (S.F.μIso _ _).symm.trans
  apply tensorIso ?_ ?_
  · symm
    apply (OverColor.forgetLiftApp S.FDiscrete (c i)).symm.trans
    apply S.F.mapIso
    apply OverColor.mkIso
    funext x
    fin_cases x
    rfl
  · symm
    apply (OverColor.forgetLiftApp S.FDiscrete (S.τ (c i))).symm.trans
    apply S.F.mapIso
    apply OverColor.mkIso
    funext x
    fin_cases x
    simp [h]

def contrMap' {n : ℕ} (c : Fin n.succ.succ → S.C)
    (i : Fin n.succ.succ) (j : Fin n.succ) (h : c (i.succAbove j) = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ⟶
    (OverColor.lift.obj S.FDiscrete).obj (OverColor.mk (c ∘ i.succAbove ∘ j.succAbove)) :=
  (S.contrIso c i j h).hom ≫
  (tensorHom (S.contr.app (Discrete.mk (c i))) (𝟙 _)) ≫
  (MonoidalCategory.leftUnitor _).hom

def contrMap {n : ℕ} (c : Fin n → S.C)
    (i j : Fin n) (hij : i ≠ j) (h : c j = S.τ (c i)) :
    S.F.obj (OverColor.mk c) ⟶
    (OverColor.lift.obj S.FDiscrete).obj
    (OverColor.mk ((c ∘ Fin.cast (contrNPred hij)) ∘ Fin.succAbove (contrFstSucc hij) ∘
    Fin.succAbove (contrSndSucc hij))) := by
  refine (S.F.mapIso (OverColor.equivToIso (Fin.castOrderIso (contrNPred hij)).toEquiv.symm)).hom ≫
    S.contrMap' (c ∘ Fin.cast (contrNPred hij)) (contrFstSucc hij) (contrSndSucc hij) ?_
  simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, contrSndSucc_succAbove,
    Fin.castOrderIso_apply, Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self]
  simpa [contrFstSucc] using h


end TensorStruct

/-- A syntax tree for tensor expressions. -/
inductive TensorTree (S : TensorStruct) : ∀ {n : ℕ}, (Fin n → S.C) → Type where
  | tensorNode {n : ℕ} {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) : TensorTree S c
  | add {n : ℕ} {c : Fin n → S.C} : TensorTree S c → TensorTree S c → TensorTree S c
  | perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) : TensorTree S c1
  | prod {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t : TensorTree S c) (t1 : TensorTree S c1) : TensorTree S (Sum.elim c c1 ∘ finSumFinEquiv.symm)
  | smul {n : ℕ} {c : Fin n → S.C} : S.k → TensorTree S c → TensorTree S c
  | contr {n : ℕ} {c : Fin n → S.C} : (i j : Fin n) →
    (hij : i ≠ j) → (h : c j = S.τ (c i)) → TensorTree S c →
    TensorTree S ((c ∘ Fin.cast (TensorStruct.contrNPred hij)) ∘
      Fin.succAbove (TensorStruct.contrFstSucc hij) ∘
      Fin.succAbove (TensorStruct.contrSndSucc hij))
  | jiggle {n : ℕ} {c : Fin n → S.C} : (i : Fin n) → TensorTree S c →
    TensorTree S (Function.update c i (S.τ (c i)))
  | eval {n : ℕ} {c : Fin n.succ → S.C} :
    (i : Fin n.succ) → (x : Fin (S.evalNo (c i))) → TensorTree S c →
    TensorTree S (c ∘ Fin.succAbove i)

namespace TensorTree

variable {S : TensorStruct} {n : ℕ} {c : Fin n → S.C} (T : TensorTree S c)

def metric : TensorTree S ![]
open MonoidalCategory
open TensorProduct

/-- The number of nodes in a tensor tree. -/
def size : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → ℕ := fun
  | tensorNode _ => 1
  | add t1 t2 => t1.size + t2.size + 1
  | perm _ t => t.size + 1
  | smul _ t => t.size + 1
  | prod t1 t2 => t1.size + t2.size + 1
  | contr _ _ _ _ t => t.size + 1
  | jiggle _ t => t.size + 1
  | eval _ _ t => t.size + 1

noncomputable section

/-- The underlying tensor a tensor tree corresponds to.
  Note: This function is not fully defined yet. -/
def tensor : ∀ {n : ℕ} {c : Fin n → S.C}, TensorTree S c → S.F.obj (OverColor.mk c) := fun
  | tensorNode t => t
  | add t1 t2 => t1.tensor + t2.tensor
  | perm σ t => (S.F.map σ).hom t.tensor
  | smul a t => a • t.tensor
  | prod t1 t2 => (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
    ((S.F.μ _ _).hom (t1.tensor ⊗ₜ t2.tensor))
  | contr i j hij h t  => (S.contrMap _ i j hij h).hom t.tensor
  | jiggle i t => by
    rename_i n c'
    let T := (tensorNode (S.metric (S.τ (c' i))))
    let T2 := (S.F.map (OverColor.equivToIso finSumFinEquiv).hom).hom
      ((S.F.μ _ _).hom (T.tensor ⊗ₜ t.tensor))
    let e1 : Fin (2 + n) ≃ Fin (2 + n) :=
      (Equiv.swap (Fin.castAdd n (0 : Fin 2)) (Fin.natAdd 2 i))
    let T3 := (S.F.map ((OverColor.equivToIso e1).hom)).hom  T2
    let T4 := (S.contrMap _  (Fin.castAdd n (0 : Fin 2)) (Fin.castAdd n (1 : Fin 2))
       (by
      simp only [Fin.isValue, ne_eq,
      Fin.ext_iff, Fin.coe_castAdd, Fin.val_zero, Fin.coe_natAdd]
      omega)
      (by
        simp [e1]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [Fin.ext_iff]
          rfl
        · simp [Fin.ext_iff]
        · simp [Fin.ext_iff]
          omega)).hom T3
    refine (S.F.map ?_).hom T4
    refine (OverColor.equivToIso (Fin.castOrderIso (by simp : (2 + n).pred.pred = n)).toEquiv).hom ≫  ?_
    refine (OverColor.mkIso ?_).hom
    funext x
    simp
    trans Sum.elim ![S.τ (c' i), S.τ (c' i)] c' (finSumFinEquiv.symm
      (e1.symm (Fin.natAdd 2 x)))
    congr
    simp [Fin.ext_iff]
    simp [Fin.succAbove]
    split_ifs
    · rename_i h1 h2
      rw [Fin.lt_def] at h1 h2
      simp_all [TensorStruct.contrSndSucc, TensorStruct.contrFstSucc]
    · rename_i h1 h2
      rw [Fin.lt_def] at h1 h2
      simp_all [TensorStruct.contrSndSucc, TensorStruct.contrFstSucc]
      simp [Fin.predAbove, Fin.lt_def] at h1
    · rename_i h1 h2
      rw [Fin.lt_def] at h1 h2
      simp_all [TensorStruct.contrSndSucc, TensorStruct.contrFstSucc]
    · simp
      omega
    simp [e1]
    by_cases hi: x= i
    · subst hi
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · simp
        rw [Function.update]
        simp [hi]
      · simp [Fin.ext_iff]
      · simp [Fin.ext_iff]
        omega

  | _ => 0

lemma tensor_tensorNode {c : Fin n → S.C} (T : S.F.obj (OverColor.mk c)) :
    (tensorNode T).tensor = T := rfl

end

end TensorTree

end
