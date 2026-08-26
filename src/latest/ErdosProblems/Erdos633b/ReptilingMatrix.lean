import ErdosProblems.Erdos633b.ReptilingScale
import ErdosProblems.Erdos633b.ReptilingAlgebra
import ErdosProblems.Erdos633b.BoundaryLength

/-! The integer boundary matrix comes from complete sides of actual placed tiles.
For nonsquare reptilings its characteristic determinant has the two roots ±√n. -/

namespace Erdos633b.Tiling

open Matrix

noncomputable def boundaryMatrix {T : Triangle} {n : ℕ} (d : Tiling T n) :
    Matrix (Fin 3) (Fin 3) ℤ := fun i j => d.boundarySideCount i j

theorem boundaryMatrix_nonneg {T : Triangle} {n : ℕ} (d : Tiling T n) (i j : Fin 3) :
    0 ≤ d.boundaryMatrix i j := Int.natCast_nonneg _

theorem boundaryMatrix_mul_side {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) :
    ThreeMatrix.toReal d.boundaryMatrix *ᵥ d.tile.side = Real.sqrt n • d.tile.side := by
  ext i
  change (∑ j, ((d.boundarySideCount i j : ℤ) : ℝ) * d.tile.side j) =
    Real.sqrt n * d.tile.side i
  simp only [Int.cast_natCast]
  rw [← d.side_eq_sum_counts, d.side_eq_sqrt_mul_of_angles h]

theorem tile_side_ne_zero {T : Triangle} {n : ℕ} (d : Tiling T n) : d.tile.side ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  exact (d.tile.side_pos 0).ne' h0

theorem boundaryMatrix_nonsquare_coefficients {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i) :
    ThreeMatrix.secondInt d.boundaryMatrix = -(n : ℤ) ∧
      d.boundaryMatrix.det = -ThreeMatrix.traceInt d.boundaryMatrix * n :=
  ThreeMatrix.nonsquare_coefficients hn d.tile_side_ne_zero (d.boundaryMatrix_mul_side h)

theorem boundaryMatrix_nonsquare_shifted_det {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i) (x : ℝ) :
    (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - ThreeMatrix.toReal d.boundaryMatrix).det =
      (x ^ 2 - n) * (x - ThreeMatrix.traceInt d.boundaryMatrix) :=
  ThreeMatrix.nonsquare_shifted_det hn d.tile_side_ne_zero (d.boundaryMatrix_mul_side h) x

theorem boundaryMatrix_negative_eigenvector {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      ThreeMatrix.toReal d.boundaryMatrix *ᵥ w = -Real.sqrt n • w :=
  ThreeMatrix.exists_negative_eigenvector hn d.tile_side_ne_zero (d.boundaryMatrix_mul_side h)

end Erdos633b.Tiling
