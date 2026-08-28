import Wikipedia.HopfProblem.LocalSystemMatrices

/-!
# Exterior minors of the lattice monodromy matrices

These six matrices are defined by the actual ordered minors of `A₁`, `A₂`,
and `M₀`. Their literal entries and their two-sided inverse-transpose identities
with the corresponding minors of `T₁`, `T₂`, and `T₀` are checked over the integers.
This file makes no singular-homology identification.
-/

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior

open scoped Matrix
open LocalSystemMatrices

def squareA₁ : Matrix (Fin 6) (Fin 6) ℤ := exteriorSquare A₁
def squareA₂ : Matrix (Fin 6) (Fin 6) ℤ := exteriorSquare A₂
def squareM₀ : Matrix (Fin 6) (Fin 6) ℤ := exteriorSquare M₀

def cubeA₁ : LatticeMatrix := exteriorCube A₁
def cubeA₂ : LatticeMatrix := exteriorCube A₂
def cubeM₀ : LatticeMatrix := exteriorCube M₀

theorem squareA₁_eq : squareA₁ =
    !![0, 1, 0, 0, 0, 0;
      -1, -1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0;
      -6, 0, 0, 1, 0, 0;
      6, 2, 6, -1, 0, 1;
      -8, -2, -6, 1, -1, -1] := by decide

theorem squareA₂_eq : squareA₂ =
    !![0, -1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0;
      0, -6, 0, 1, 0, 0;
      0, 3, 0, 0, 0, -1;
      -3, -6, -6, 1, 1, 0] := by decide

theorem squareM₀_eq : squareM₀ =
    !![1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      1, 0, 0, 0, 1, 0;
      1, 1, 0, 0, 1, 1] := by decide

theorem cubeA₁_eq : cubeA₁ =
    !![1, 0, 0, 0;
      -1, 0, 1, 0;
      1, -1, -1, 0;
      -2, -6, 0, 1] := by decide

theorem cubeA₂_eq : cubeA₂ =
    !![1, 0, 0, 0;
      0, 0, -1, 0;
      1, 1, 0, 0;
      3, 0, -6, 1] := by decide

theorem cubeM₀_eq : cubeM₀ =
    !![1, 0, 0, 0;
      0, 1, 0, 0;
      0, 1, 1, 0;
      -1, 0, 0, 1] := by decide

theorem squareA₁_mul_squareT₁_transpose : squareA₁ * squareT₁.transpose = 1 := by
  rw [squareA₁_eq, squareT₁_eq]
  decide

theorem squareT₁_transpose_mul_squareA₁ : squareT₁.transpose * squareA₁ = 1 := by
  rw [squareT₁_eq, squareA₁_eq]
  decide

theorem squareA₂_mul_squareT₂_transpose : squareA₂ * squareT₂.transpose = 1 := by
  rw [squareA₂_eq, squareT₂_eq]
  decide

theorem squareT₂_transpose_mul_squareA₂ : squareT₂.transpose * squareA₂ = 1 := by
  rw [squareT₂_eq, squareA₂_eq]
  decide

theorem squareM₀_mul_squareT₀_transpose : squareM₀ * squareT₀.transpose = 1 := by
  rw [squareM₀_eq, squareT₀_eq]
  decide

theorem squareT₀_transpose_mul_squareM₀ : squareT₀.transpose * squareM₀ = 1 := by
  rw [squareT₀_eq, squareM₀_eq]
  decide

theorem cubeA₁_mul_cubeT₁_transpose : cubeA₁ * cubeT₁.transpose = 1 := by
  rw [cubeA₁_eq, cubeT₁_eq]
  decide

theorem cubeT₁_transpose_mul_cubeA₁ : cubeT₁.transpose * cubeA₁ = 1 := by
  rw [cubeT₁_eq, cubeA₁_eq]
  decide

theorem cubeA₂_mul_cubeT₂_transpose : cubeA₂ * cubeT₂.transpose = 1 := by
  rw [cubeA₂_eq, cubeT₂_eq]
  decide

theorem cubeT₂_transpose_mul_cubeA₂ : cubeT₂.transpose * cubeA₂ = 1 := by
  rw [cubeT₂_eq, cubeA₂_eq]
  decide

theorem cubeM₀_mul_cubeT₀_transpose : cubeM₀ * cubeT₀.transpose = 1 := by
  rw [cubeM₀_eq, cubeT₀_eq]
  decide

theorem cubeT₀_transpose_mul_cubeM₀ : cubeT₀.transpose * cubeM₀ = 1 := by
  rw [cubeT₀_eq, cubeM₀_eq]
  decide

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior
