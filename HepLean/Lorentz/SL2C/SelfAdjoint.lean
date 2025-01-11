import Mathlib.LinearAlgebra.Matrix.SchurComplement
import HepLean.Mathematics.SchurTriangulation

namespace Lorentz

open scoped Matrix
open scoped ComplexConjugate

/-- A notation for the type of complex 2-by-2 matrices. It would have been better to make it an
abbreviation if it wasn't for Lean's inability to recognize `ℂ²ˣ²` as an identifier. -/
scoped notation "ℂ²ˣ²" => Matrix (Fin 2) (Fin 2) ℂ

/-- A convenient abbreviation for the type of self-adjoint complex 2-by-2 matrices. -/
noncomputable abbrev ℍ₂ := selfAdjoint ℂ²ˣ²

namespace SL2C

/-- Definitially equal to `Lorentz.SL2C.toSelfAdjointMap` but dropping the requirement that `M` be
special linear. -/
noncomputable def toSelfAdjointMap' (M : ℂ²ˣ²) : ℍ₂ →ₗ[ℝ] ℍ₂ where
  toFun | ⟨A, hA⟩ => ⟨M * A * Mᴴ, hA.conjugate M⟩
  map_add' | ⟨A, _⟩, ⟨B, _⟩ => Subtype.ext <|
    show M * (A + B) * Mᴴ = M * A * Mᴴ + M * B * Mᴴ by noncomm_ring
  map_smul' | r, ⟨A, _⟩ => Subtype.ext <| by simp

open Complex (I normSq) in
theorem toSelfAdjointMap_det_one' {M : ℂ²ˣ²} (hM : M.IsUpperTriangular) (detM : M.det = 1)
    : LinearMap.det (toSelfAdjointMap' M) = 1 :=
  let b : Basis (Fin 2 ⊕ Fin 2) ℝ ℍ₂ := Basis.ofEquivFun {
    toFun := fun ⟨A, _⟩ => ![(A 0 0).re, (A 1 1).re] ⊕ᵥ ![(A 0 1).re, (A 0 1).im]
    map_add' := fun _ _ => funext fun | .inl 0 | .inl 1 | .inr 0 | .inr 1 => rfl
    map_smul' := fun _ _ => funext fun | .inl 0 | .inl 1 | .inr 0 | .inr 1 => by simp
    invFun := fun p => {
      val := let z : ℂ := ⟨p (.inr 0), p (.inr 1)⟩ ; !![p (.inl 0), z; conj z, p (.inl 1)]
      property := Matrix.ext fun | 0, 0 | 0, 1 | 1, 0 | 1, 1 => by simp
    }
    left_inv := fun ⟨A, hA⟩ => Subtype.ext <| Matrix.ext fun
      | 0, 1 => rfl
      | 1, 0 => show conj (A 0 1) = A 1 0 from congrFun₂ hA 1 0
      | 0, 0 => show (A 0 0).re = A 0 0 from Complex.conj_eq_iff_re.mp (congrFun₂ hA 0 0)
      | 1, 1 => show (A 1 1).re = A 1 1 from Complex.conj_eq_iff_re.mp (congrFun₂ hA 1 1)
    right_inv := fun _ => funext fun | .inl 0 | .inl 1 | .inr 0 | .inr 1 => rfl
  }
  let E₀ : ℂ²ˣ² := !![1, 0; conj 0, 0] -- b (.inl 0)
  let E₁ : ℂ²ˣ² := !![0, 0; conj 0, 1] -- b (.inl 1)
  let E₂ : ℂ²ˣ² := !![0, 1; conj 1, 0] -- b (.inr 0)
  let E₃ : ℂ²ˣ² := !![0, I; conj I, 0] -- b (.inr 1)
  let F : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := LinearMap.toMatrix b b (toSelfAdjointMap' M)
  let A := F.toBlocks₁₁ ; let B := F.toBlocks₁₂ ; let C := F.toBlocks₂₁ ; let D := F.toBlocks₂₂
  let x := M 0 0 ; let y := M 1 1 ; have hM10 : M 1 0 = 0 := hM <| show 0 < 1 by decide
  have he : M = !![x, _; 0, y] := Matrix.ext fun | 0, 0 | 0, 1 | 1, 1 => rfl | 1, 0 => hM10
  have he' : Mᴴ = !![conj x, 0; _, conj y] :=
    Matrix.ext fun | 0, 0 | 1, 0 | 1, 1 => rfl | 0, 1 => by simp [hM10]

  have detA_one : normSq x * normSq y = 1 := congrArg Complex.re <|
    calc ↑(normSq x * normSq y)
      _ = x * conj x * (y * conj y) := by simp [Complex.mul_conj]
      _ = x * y * (conj y * conj x) := by ring
      _ = x * y * conj (x * y) := congrArg _ (star_mul ..).symm
      _ = 1 := suffices x * y = 1 by simp [this]
        calc x * y
          _ = !![x, _; 0, y].det := by simp
          _ = M.det := congrArg _ he.symm
          _ = 1 := detM
  have detD_one : D.det = 1 :=
    let z := x * conj y
    have k₀ : (M * E₂ * Mᴴ) 0 1 = z := by rw [he', he] ; simp [E₂]
    have k₁ : (M * E₃ * Mᴴ) 0 1 = ⟨-z.im, z.re⟩ :=
      calc
        _ = x * I * conj y := by rw [he', he] ; simp [E₃]
        _ = Complex.I * z := by ring
        _ = ⟨-z.im, z.re⟩ := z.I_mul
    have hD : D = !![z.re, -z.im; z.im, z.re] := Matrix.ext fun
      | 0, 0 => congrArg Complex.re k₀ | 1, 0 => congrArg Complex.im k₀
      | 0, 1 => congrArg Complex.re k₁ | 1, 1 => congrArg Complex.im k₁
    calc D.det
      _ = normSq z := by simp [hD, z.normSq_apply]
      _ = normSq x * normSq y := by simp [x.normSq_mul]
      _ = 1 := detA_one

  letI : Invertible D.det := detD_one ▸ invertibleOne
  letI : Invertible D := D.invertibleOfDetInvertible
  have hE : A - B * ⅟D * C = !![normSq x, _; 0, normSq y] :=
    have k : (M * E₀ * Mᴴ) 0 1 = 0 := by rw [he', he] ; simp [E₀]
    have hC00 : C 0 0 = 0 := congrArg Complex.re k
    have hC10 : C 1 0 = 0 := congrArg Complex.im k
    Matrix.ext fun
      | 0, 1 => rfl
      | 1, 0 =>
        have hA10 : A 1 0 = 0 := congrArg Complex.re <|
          show (M * E₀ * Mᴴ) 1 1 = 0 by rw [he', he] ; simp [E₀]
        show A 1 0 - (B * ⅟D) 1 ⬝ᵥ (C · 0) = 0 by simp [hC00, hC10, hA10]
      | 0, 0 =>
        have hA00 : A 0 0 = normSq x := congrArg Complex.re <|
          show (M * E₀ * Mᴴ) 0 0 = normSq x by rw [he', he] ; simp [E₀, x.mul_conj]
        show A 0 0 - (B * ⅟D) 0 ⬝ᵥ (C · 0) = normSq x by simp [hC00, hC10, hA00]
      | 1, 1 =>
        have hA11 : A 1 1 = normSq y := congrArg Complex.re <|
          show (M * E₁ * Mᴴ) 1 1 = normSq y by rw [he', he] ; simp [E₁, y.mul_conj]
        have hB10 : B 1 0 = 0 := congrArg Complex.re <|
          show (M * E₂ * Mᴴ) 1 1 = 0 by rw [he', he] ; simp [E₂]
        have hB11 : B 1 1 = 0 := congrArg Complex.re <|
          show (M * E₃ * Mᴴ) 1 1 = 0 by rw [he', he] ; simp [E₃]
        calc A 1 1 - (B * ⅟D * C) 1 1
          _ = A 1 1 - B 1 ⬝ᵥ ((⅟D * C) · 1) := by noncomm_ring
          _ = normSq y := by simp [hB10, hB11, hA11]
  calc LinearMap.det (toSelfAdjointMap' M)
    _ = F.det := (LinearMap.det_toMatrix ..).symm
    _ = D.det * (A - B * ⅟D * C).det := F.fromBlocks_toBlocks ▸ Matrix.det_fromBlocks₂₂ ..
    _ = 1 := by rw [hE] ; simp [detD_one, detA_one]

/-- This promotes `Lorentz.SL2C.toSelfAdjointMap M` and its definitional equivalence,
`Lorentz.SL2C.toSelfAdjointMap' M`, to a linear equivalence by recognising the linear inverse to be
`Lorentz.SL2C.toSelfAdjointMap M⁻¹`, i.e., `Lorentz.SL2C.toSelfAdjointMap' M⁻¹`. -/
noncomputable def toSelfAdjointEquiv (M : ℂ²ˣ²) [Invertible M] : ℍ₂ ≃ₗ[ℝ] ℍ₂ where
  toLinearMap := toSelfAdjointMap' M
  invFun := toSelfAdjointMap' M⁻¹
  left_inv | ⟨A, _⟩ => Subtype.ext <|
    calc M⁻¹ * (M * A * Mᴴ) * M⁻¹ᴴ
      _ = M⁻¹ * ↑M * A * (M⁻¹ * M)ᴴ := by noncomm_ring [Matrix.conjTranspose_mul]
      _ = A := by simp
  right_inv | ⟨A, _⟩ => Subtype.ext <|
    calc M * (M⁻¹ * A * M⁻¹ᴴ) * Mᴴ
      _ = M * M⁻¹ * A * (M * M⁻¹)ᴴ := by noncomm_ring [Matrix.conjTranspose_mul]
      _ = A := by simp

theorem toSelfAdjointMap_mul (M N : ℂ²ˣ²)
    : toSelfAdjointMap' (M * N) = toSelfAdjointMap' M ∘ₗ toSelfAdjointMap' N :=
  LinearMap.ext fun A => Subtype.ext <|
    show M * N * A * (M * N)ᴴ = M * (N * A * Nᴴ) * Mᴴ by noncomm_ring [Matrix.conjTranspose_mul]

theorem toSelfAdjointMap_similar_det (M N : ℂ²ˣ²) [Invertible M]
    : LinearMap.det (toSelfAdjointMap' (M * N * M⁻¹)) = LinearMap.det (toSelfAdjointMap' N) :=
  let e := toSelfAdjointEquiv M
  let f := toSelfAdjointMap' N
  suffices toSelfAdjointMap' (M * N * M⁻¹) = e ∘ₗ f ∘ₗ e.symm from this ▸ f.det_conj e
  by rw [toSelfAdjointMap_mul, toSelfAdjointMap_mul] ; rfl

end SL2C
end Lorentz
