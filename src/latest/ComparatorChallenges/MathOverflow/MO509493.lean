import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.Matrix.Hadamard

namespace MO509493

open Matrix Finset BigOperators

def IsOrthProj {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) : Prop :=
  P * P = P ∧ Pᵀ = P

def IsUnitEquiv {n : Type*} [Fintype n] [DecidableEq n]
    {𝕜 : Type*} [CommSemiring 𝕜] [StarRing 𝕜]
    (A B : Matrix n n 𝕜) : Prop :=
  ∃ U : Matrix n n 𝕜,
    U * star U = 1 ∧ star U * U = 1 ∧ B = U * A * star U

noncomputable def hadamardSquare {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) : Matrix n n ℝ :=
  (P₁ * P₂).hadamard (P₂ * P₁)

def IsCounterexample (n : ℕ) (k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
    IsOrthProj P₁ ∧ IsOrthProj P₂ ∧ IsUnitEquiv P₁ P₂ ∧
    A = hadamardSquare P₁ P₂ ∧ ¬(0 ≤ (A ^ k).trace)

def P₁_example : Matrix (Fin 4) (Fin 4) ℚ :=
  !![3/5, -1/5, 1/5, -2/5;
     -1/5, 2/5, -2/5, -1/5;
     1/5, -2/5, 2/5, 1/5;
     -2/5, -1/5, 1/5, 3/5]

def P₂_example : Matrix (Fin 4) (Fin 4) ℚ :=
  !![7/20, 9/20, -1/20, 3/20;
     9/20, 13/20, 3/20, 1/20;
     -1/20, 3/20, 13/20, -9/20;
     3/20, 1/20, -9/20, 7/20]

theorem A_example_isCounterexample :
    IsCounterexample 4 3 (hadamardSquare
      (Matrix.of (fun i j => (P₁_example i j : ℝ)))
      (Matrix.of (fun i j => (P₂_example i j : ℝ)))) := by
  sorry

theorem min_counterexample_dim_CE :
    (∃ A, IsCounterexample 4 3 A) ∧
    (∀ n (_ : n ≤ 3) k (A : Matrix (Fin n) (Fin n) ℝ),
      ¬IsCounterexample n k A) := by
  sorry

theorem min_counterexample_exp_CE :
    (∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      IsCounterexample n 3 A) ∧
    (∀ (n k : ℕ), k ≤ 2 →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ), ¬IsCounterexample n k A) := by
  sorry

end MO509493
