/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Polyrith
import LeanCopilot
/-!

# Rank of matrices

This field contains addiational lemmas and results about the rank of matrices beyond
those which appear in Mathlib.

Our method is to provide a certificate checker for the rank of the matrix.

## TODO

- Automate, following the method of `polyrith`, the process of finding the
  row-reduced form of a matrix.

-/

namespace Mathematics
variable {n m : ℕ}
open Matrix

/-- The proposition on a matrix for it to be in row echelon form. -/
def IsRowEchelonForm (M : Matrix (Fin n) (Fin m) ℚ) : Prop :=
  ∀ i j, i < j →
    match Fin.find (fun k => M i k ≠ 0), Fin.find (fun k => M j k ≠ 0) with
    | some i', some j' => i' < j'
    | some _, none => true
    | none, some _ => false
    | none, none => true

instance (M : Matrix (Fin n) (Fin m) ℚ) : Decidable (IsRowEchelonForm M) := by
  refine @Fintype.decidableForallFintype _ _ (fun i => ?_) _
  refine @Fintype.decidableForallFintype _ _ (fun j => ?_) _
  refine @instDecidableForall _  _ (i.decLt j) ?_
  match  Fin.find (fun k => M i k ≠ 0), Fin.find (fun k => M j k ≠ 0) with
  | some i', some j'  => exact i'.decLt j'
  | some _, none => exact true.decEq true
  | none, some _ => exact false.decEq true
  | none, none => exact true.decEq true

example : IsRowEchelonForm !![1, 2, 3; 0, 1, 3; 0, 0, 1] := by
  decide

example :  ¬ IsRowEchelonForm !![1, 2, 3; 0, 1, 3; 0, 2, 1] := by
  decide

/-- `M` is a row echelon form of `N`. -/
structure RowEchelonFormOf (M : Matrix (Fin n) (Fin m) ℚ) where
  rowEchelonForm : Matrix (Fin n) (Fin m) ℚ
  transform : Matrix (Fin n) (Fin n) ℚ
  transformInv : Matrix (Fin n) (Fin n) ℚ
  transform_invert : transform * transformInv = 1 := by norm_num <;> decide
  transform_mul : transform * M = rowEchelonForm := by norm_num
  rowEchelonForm_isRowEchelonForm : IsRowEchelonForm rowEchelonForm := by decide

def sageRowEchelonFormQuery (M : Matrix (Fin n) (Fin m) ℚ) : IO Unit :=
  let M := List.map (fun i =>
    String.intercalate ", " (List.map (fun j => toString (M i j)) (Fin.list m))) (Fin.list n)
  let echelonForm :=
"M = Matrix([[" ++ String.intercalate "],[" M ++ "]])
REF, P = M.echelon_form(transformation=True)
def format(matrix):
  rows = []
  for row in matrix.rows():
      rows.append(', '.join(map(str, row)))
  return \"!![\" + \"; \".join(rows) + \"]\"
print(f\"rowEchelonForm := {format(REF)}\")
print(f\"transform := {format(P)}\")
print(f\"transformInv := {format(P.inverse())}\")"
  IO.println (echelonForm)

def myTestMatrix : RowEchelonFormOf !![1, 2, 3; 4, 5, 6; 7, 8, 9; 10, 11, 12] where
  rowEchelonForm := !![1, 2, 3; 0, 3, 6; 0, 0, 0; 0, 0, 0]
  transform := !![0, 0, 3, -2; 0, 0, 10, -7; 1, 0, -3, 2; 0, 1, -2, 1]
  transformInv := !![1, 0, 1, 0; 4, -1, 0, 1; 7, -2, 0, 0; 10, -3, 0, 0]

end Mathematics
