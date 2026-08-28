import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Literal ordered-chain expansion of the triangular prism

The recursive edge product cones its signed boundary. Its product with an
ordered triangle consists of the three usual prism tetrahedra and nine
additional tetrahedra with repeated vertices. This identity retains every
term of the original formal chain; no normalization quotient is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision

open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

variable {V W : Type*}

private theorem formalEdgeCrossProduct_one_expansion
    (v : Fin 2 → V) (w : Fin 2 → W) :
    formalEdgeCrossProduct 1 (formalSimplex v) (formalSimplex w) =
      formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1)] -
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1)] -
        formalSimplex ![(v 0, w 0), (v 0, w 1), (v 1, w 1)] +
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 1, w 0)] := by
  rw [formalEdgeCrossProduct_simplex_succ, formalPointCrossProduct_edge_boundary,
    formalBoundary_edge_simplex]
  simp only [map_sub, formalEdgeCrossProduct_zero_simplex_right, formalMap_simplex,
    formalCone_simplex]
  have hv₀ : (fun i : Fin 2 => (v 0, w i)) = ![(v 0, w 0), (v 0, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun i : Fin 2 => (v 1, w i)) = ![(v 1, w 0), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hw₀ : (fun i : Fin 2 => (v i, w 0)) = ![(v 0, w 0), (v 1, w 0)] := by
    funext i
    fin_cases i <;> rfl
  have hw₁ : (fun i : Fin 2 => (v i, w 1)) = ![(v 0, w 1), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv₀, hv₁, hw₀, hw₁]
  abel

/-- The literal three-face boundary of an ordered triangle. -/
theorem formalBoundary_triangle_simplex (w : Fin 3 → W) :
    formalBoundary 2 (formalSimplex w) =
      formalSimplex ![w 1, w 2] - formalSimplex ![w 0, w 2] +
        formalSimplex ![w 0, w 1] := by
  have h₀ : w ∘ (0 : Fin 3).succAbove = ![w 1, w 2] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : w ∘ (1 : Fin 3).succAbove = ![w 0, w 2] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : w ∘ (2 : Fin 3).succAbove = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [formalBoundary_simplex]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val • formalSimplex (w ∘ i.succAbove)) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num only [Fin.val_zero, Fin.val_succ, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_smul]
  change formalSimplex (w ∘ (0 : Fin 3).succAbove) +
    (-formalSimplex (w ∘ (1 : Fin 3).succAbove) +
      formalSimplex (w ∘ (2 : Fin 3).succAbove)) = _
  rw [h₀, h₁, h₂]
  abel

/-- The full recursive `1 × 2` product, including all nine cone-degenerate terms. -/
theorem formalEdgeCrossProduct_two_expansion (v : Fin 2 → V) (w : Fin 3 → W) :
    formalEdgeCrossProduct 2 (formalSimplex v) (formalSimplex w) =
      formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1), (v 1, w 2)] -
        formalSimplex ![(v 0, w 0), (v 0, w 1), (v 1, w 1), (v 1, w 2)] +
        formalSimplex ![(v 0, w 0), (v 0, w 1), (v 0, w 2), (v 1, w 2)] -
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1), (v 0, w 2)] +
        formalSimplex ![(v 0, w 0), (v 0, w 1), (v 0, w 1), (v 0, w 2)] -
        formalSimplex ![(v 0, w 0), (v 0, w 1), (v 0, w 1), (v 1, w 1)] +
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 1, w 0), (v 1, w 2)] -
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 0), (v 0, w 2)] -
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 2), (v 1, w 2)] -
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 1, w 0), (v 1, w 1)] +
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 0), (v 0, w 1)] +
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1), (v 1, w 1)] := by
  rw [formalEdgeCrossProduct_simplex_succ, formalPointCrossProduct_edge_boundary,
    formalBoundary_triangle_simplex]
  simp only [map_add, map_sub, formalEdgeCrossProduct_one_expansion,
    formalMap_simplex, formalCone_simplex]
  have hv₀ : (fun i : Fin 3 => (v 0, w i)) =
      ![(v 0, w 0), (v 0, w 1), (v 0, w 2)] := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun i : Fin 3 => (v 1, w i)) =
      ![(v 1, w 0), (v 1, w 1), (v 1, w 2)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv₀, hv₁, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.Fin.cons_vecCons]
  abel

end Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision
