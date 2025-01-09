import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Spectrum
open scoped InnerProductSpace

namespace Fin
variable {i : Fin (m + n)}

def toSigmaBool_neg (h : ¬ i < m) : Fin n := ⟨i - m, Nat.sub_lt_left_of_lt_add (Nat.ge_of_not_lt h) i.isLt⟩
def toSigmaBool (i : Fin (m + n)) : Σ b, cond b (Fin m) (Fin n) :=
  if h : i < m then ⟨true, i, h⟩ else ⟨false, toSigmaBool_neg h⟩
theorem toSigmaBool_fst (h : i < m) : i.toSigmaBool = ⟨true, i, h⟩ := dif_pos h
theorem toSigmaBool_snd (h : ¬ i < m) : i.toSigmaBool = ⟨false, toSigmaBool_neg h⟩ := dif_neg h

def ofSigmaBool : (Σ b, cond b (Fin m) (Fin n)) → Fin (m + n)
  | ⟨true, i⟩ => Fin.castAdd n i
  | ⟨false, i⟩ => Fin.natAdd m i

end Fin

def Equiv.finAddEquivSigmaBool : Fin (m + n) ≃ Σ b, cond b (Fin m) (Fin n) where
  toFun := Fin.toSigmaBool
  invFun := Fin.ofSigmaBool
  left_inv i :=
    if h : i < m
    then congrArg Fin.ofSigmaBool (dif_pos h)
    else
      calc  Fin.ofSigmaBool i.toSigmaBool
        _ = ⟨m + (i - m), _⟩ := congrArg Fin.ofSigmaBool (dif_neg h)
        _ = i := Fin.ext <| Nat.add_sub_of_le (Nat.le_of_not_gt h)
  right_inv
    | ⟨true, i⟩ => dif_pos i.isLt
    | ⟨false, (i : Fin n)⟩ =>
      calc  (Fin.natAdd m i).toSigmaBool
        _ = ⟨false, m + i - m, _⟩ := dif_neg <| Nat.not_lt_of_le (Nat.le_add_right ..)
        _ = ⟨false, i⟩ := Sigma.eq rfl <| Fin.ext (Nat.add_sub_cancel_left ..)

instance [M : Fintype m] [N : Fintype n] (b : Bool) : Fintype (cond b m n) := b.rec N M

instance [DecidableEq m] [DecidableEq n] : DecidableEq (Σ b, cond b m n)
  | ⟨true, _⟩, ⟨false, _⟩
  | ⟨false, _⟩, ⟨true, _⟩ => isFalse nofun
  | ⟨false, i⟩, ⟨false, j⟩
  | ⟨true, i⟩, ⟨true, j⟩ => if h : i = j then isTrue (Sigma.eq rfl h) else isFalse fun | rfl => h rfl

namespace Matrix

abbrev IsUpperTriangular [LT n] [CommRing R] (A : Matrix n n R) := A.BlockTriangular id
abbrev UpperTriangular (n R) [LT n] [CommRing R] := { A : Matrix n n R // A.IsUpperTriangular }

end Matrix

namespace LinearMap
variable [RCLike 𝕜]

section
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section
variable [FiniteDimensional 𝕜 E] [Fintype n] [DecidableEq n]

theorem toMatrixOrthonormal_apply_apply (b : OrthonormalBasis n 𝕜 E) (f : Module.End 𝕜 E) (i j : n)
    : toMatrixOrthonormal b f i j = ⟪b i, f (b j)⟫_𝕜 :=
  calc
    _ = b.repr (f (b j)) i := f.toMatrix_apply ..
    _ = ⟪b i, f (b j)⟫_𝕜 := b.repr_apply_apply ..

theorem toMatrixOrthonormal_reindex [Fintype m] [DecidableEq m]
    (b : OrthonormalBasis m 𝕜 E) (e : m ≃ n) (f : Module.End 𝕜 E)
    : toMatrixOrthonormal (b.reindex e) f = Matrix.reindex e e (toMatrixOrthonormal b f) :=
  Matrix.ext fun i j => let c := b.toBasis
    show toMatrix (b.reindex e).toBasis (b.reindex e).toBasis f i j = toMatrix c c f (e.symm i) (e.symm j) by
    rw [b.reindex_toBasis, f.toMatrix_apply, c.repr_reindex_apply, c.reindex_apply, f.toMatrix_apply]

end

structure SchurTriangulationAux (f : Module.End 𝕜 E) where
  dim : ℕ
  hdim : Module.finrank 𝕜 E = dim
  basis : OrthonormalBasis (Fin dim) 𝕜 E
  upperTriangular : (toMatrix basis.toBasis basis.toBasis f).IsUpperTriangular

end

variable [IsAlgClosed 𝕜]

protected noncomputable def SchurTriangulationAux.of
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (f : Module.End 𝕜 E)
    : SchurTriangulationAux f :=
  haveI : Decidable (Nontrivial E) := Classical.propDecidable _
  if hE : Nontrivial E then
    let μ : f.Eigenvalues := default
    let V : Submodule 𝕜 E := f.eigenspace μ
    let W : Submodule 𝕜 E := Vᗮ
    let m := Module.finrank 𝕜 V
    have hdim : m + Module.finrank 𝕜 W = Module.finrank 𝕜 E := V.finrank_add_finrank_orthogonal
    let g : Module.End 𝕜 W := orthogonalProjection W ∘ₗ f.domRestrict W
    let ⟨n, hn, bW, hg⟩ := SchurTriangulationAux.of g

    have bV : OrthonormalBasis (Fin m) 𝕜 V := stdOrthonormalBasis 𝕜 V
    have hV := V.orthogonalFamily_self
    have int : DirectSum.IsInternal (cond · V W) :=
      suffices ⨆ b, cond b V W = ⊤ from (hV.decomposition this).isInternal _
      (sup_eq_iSup V W).symm.trans Submodule.sup_orthogonal_of_completeSpace
    let B (b : Bool) : OrthonormalBasis (cond b (Fin m) (Fin n)) 𝕜 ↥(cond b V W) := b.rec bW bV
    let bE : OrthonormalBasis (Σ b, cond b (Fin m) (Fin n)) 𝕜 E := int.collectedOrthonormalBasis hV B
    let e := Equiv.finAddEquivSigmaBool.symm
    let basis := bE.reindex e
    {
      basis
      dim := m + n
      hdim := hn ▸ hdim.symm
      upperTriangular := fun i j (hji : j < i) => show toMatrixOrthonormal basis f i j = 0 from
        have hB : ∀ s, bE s = B s.1 s.2
          | ⟨true, i⟩ => show bE ⟨true, i⟩ = bV i from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨true, i⟩ = bV i by simp
          | ⟨false, j⟩ => show bE ⟨false, j⟩ = bW j from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨false, j⟩ = bW j by simp
        have hf {bi i' bj j'} (hi : i.toSigmaBool = ⟨bi, i'⟩) (hj : j.toSigmaBool = ⟨bj, j'⟩) :=
          calc  toMatrixOrthonormal basis f i j
            _ = toMatrixOrthonormal bE f i.toSigmaBool j.toSigmaBool := by rw [f.toMatrixOrthonormal_reindex] ; rfl
            _ = ⟪bE i.toSigmaBool, f (bE j.toSigmaBool)⟫_𝕜 := f.toMatrixOrthonormal_apply_apply ..
            _ = ⟪(B bi i' : E), f (B bj j')⟫_𝕜 := by rw [hB, hB, hi, hj]

        if hj : j < m then
          let j' : Fin m := ⟨j, hj⟩
          have hf' {bi i'} (hi : i.toSigmaBool = ⟨bi, i'⟩) (h0 : ⟪(B bi i' : E), bV j'⟫_𝕜 = 0) :=
            calc  toMatrixOrthonormal basis f i j
              _ = ⟪(B bi i' : E), f _⟫_𝕜 := hf hi (Fin.toSigmaBool_fst hj)
              _ = ⟪_, f (bV j')⟫_𝕜 := rfl
              _ = 0 :=
                suffices f (bV j') = μ.val • bV j' by rw [this, inner_smul_right, h0, mul_zero]
                suffices f.HasEigenvector μ (bV j') from this.apply_eq_smul
                ⟨(bV j').property, fun h => bV.toBasis.ne_zero j' (Subtype.ext h)⟩

          if hi : i < m then
            let i' : Fin m := ⟨i, hi⟩
            suffices ⟪(bV i' : E), bV j'⟫_𝕜 = 0 from hf' (Fin.toSigmaBool_fst hi) this
            bV.orthonormal.right (Fin.ne_of_gt hji)
          else
            let i' : Fin n := Fin.toSigmaBool_neg hi
            suffices ⟪(bW i' : E), bV j'⟫_𝕜 = 0 from hf' (Fin.toSigmaBool_snd hi) this
            V.inner_left_of_mem_orthogonal (bV j').property (bW i').property
        else
          have hi (h : i < m) : False := hj (Nat.lt_trans hji h)
          let i' : Fin n := Fin.toSigmaBool_neg hi
          let j' : Fin n := Fin.toSigmaBool_neg hj
          calc  toMatrixOrthonormal basis f i j
            _ = ⟪(bW i' : E), f (bW j')⟫_𝕜 := hf (Fin.toSigmaBool_snd hi) (Fin.toSigmaBool_snd hj)
            _ = ⟪bW i', g (bW j')⟫_𝕜 := by simp [g]
            _ = toMatrixOrthonormal bW g i' j' := (g.toMatrixOrthonormal_apply_apply ..).symm
            _ = 0 := hg (Nat.sub_lt_sub_right (Nat.le_of_not_lt hj) hji)
    }
  else
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    {
      dim := 0
      hdim := Module.finrank_zero_of_subsingleton
      basis := (Basis.empty E).toOrthonormalBasis ⟨nofun, nofun⟩
      upperTriangular := nofun
    }
termination_by Module.finrank 𝕜 E
decreasing_by exact
  calc  Module.finrank 𝕜 W
    _ < m + Module.finrank 𝕜 W := Nat.lt_add_of_pos_left (Submodule.one_le_finrank_iff.mpr μ.property)
    _ = Module.finrank 𝕜 E := hdim

end LinearMap

namespace Matrix
/- IMPORTANT: existing `DecidableEq n` should take precedence over `LinearOrder.decidableEq`,
a.k.a., `instDecidableEq_mathlib`. -/
variable [RCLike 𝕜] [IsAlgClosed 𝕜] [Fintype n] [DecidableEq n] [LinearOrder n] (A : Matrix n n 𝕜)

noncomputable def schurTriangulationAux : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) × UpperTriangular n 𝕜 :=
  let f := toEuclideanLin A
  let ⟨d, hd, b, hut⟩ := LinearMap.SchurTriangulationAux.of f
  let e : Fin d ≃o n := Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm.trans hd)
  let b' := b.reindex e
  let B := LinearMap.toMatrixOrthonormal b' f
  suffices B.IsUpperTriangular from ⟨b', B, this⟩
  fun i j (hji : j < i) =>
    calc  LinearMap.toMatrixOrthonormal b' f i j
      _ = LinearMap.toMatrixOrthonormal b f (e.symm i) (e.symm j) := by rw [f.toMatrixOrthonormal_reindex] ; rfl
      _ = 0 := hut (e.symm.lt_iff_lt.mpr hji)

noncomputable def schurTriangulationBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  A.schurTriangulationAux.1

noncomputable def schurTriangulationUnitary : unitaryGroup n 𝕜 where
  val := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix A.schurTriangulationBasis
  property := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary ..

noncomputable def schurTriangulation : UpperTriangular n 𝕜 :=
  A.schurTriangulationAux.2

/-- **Schur triangulation**, **Schur decomposition** for matrices over an algebraically closed
field. In particular, a complex matrix can be converted to upper-triangular form by a change of
basis. In other words, any complex matrix is unitarily similar to an upper triangular matrix. -/
theorem schur_triangulation
    : A = A.schurTriangulationUnitary * A.schurTriangulation * star A.schurTriangulationUnitary :=
  let U := A.schurTriangulationUnitary
  have h : U * A.schurTriangulation.val = A * U :=
    let b := A.schurTriangulationBasis.toBasis
    let c := (EuclideanSpace.basisFun n 𝕜).toBasis
    calc  c.toMatrix b * LinearMap.toMatrix b b (toEuclideanLin A)
      _ = LinearMap.toMatrix c c (toEuclideanLin A) * c.toMatrix b := by simp
      _ = LinearMap.toMatrix c c (toLin c c A) * U := rfl
      _ = A * U := by simp
  calc  A
    _ = A * U * star U := by simp [mul_assoc]
    _ = U * A.schurTriangulation * star U := by rw [←h]

end Matrix
