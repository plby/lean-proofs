import ErdosProblems.Erdos633b.TriquadraticCoordinates

/-! Actual Euclidean triangles from a nonzero coordinate determinant. -/

namespace Erdos633b

theorem coordinate_independent (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ)
    (hdet : (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀) ≠ 0) :
    AffineIndependent ℝ ![(!₂[x₀, y₀] : Plane), !₂[x₁, y₁], !₂[x₂, y₂]] := by
  rw [affineIndependent_iff_of_fintype]
  intro f hf hv i
  rw [Finset.univ.weightedVSub_eq_linear_combination hf] at hv
  have hsum : f 0 + f 1 + f 2 = 0 := by simpa [Fin.sum_univ_three] using hf
  have hx : f 0 * x₀ + f 1 * x₁ + f 2 * x₂ = 0 := by
    simpa [Fin.sum_univ_three] using congrArg (fun p : Plane => p 0) hv
  have hy : f 0 * y₀ + f 1 * y₁ + f 2 * y₂ = 0 := by
    simpa [Fin.sum_univ_three] using congrArg (fun p : Plane => p 1) hv
  have h1 : f 1 * ((x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀)) = 0 := by
    linear_combination (y₂ - y₀) * hx - (x₂ - x₀) * hy +
      (x₂ * y₀ - x₀ * y₂) * hsum
  have h2 : f 2 * ((x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀)) = 0 := by
    linear_combination -(y₁ - y₀) * hx + (x₁ - x₀) * hy +
      (x₀ * y₁ - x₁ * y₀) * hsum
  have h1' : f 1 = 0 := (mul_eq_zero.mp h1).resolve_right hdet
  have h2' : f 2 = 0 := (mul_eq_zero.mp h2).resolve_right hdet
  have h0' : f 0 = 0 := by linarith
  fin_cases i
  · exact h0'
  · exact h1'
  · exact h2'

noncomputable def coordinateTriangle (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ)
    (hdet : (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀) ≠ 0) : Triangle where
  points := ![!₂[x₀, y₀], !₂[x₁, y₁], !₂[x₂, y₂]]
  independent := coordinate_independent x₀ y₀ x₁ y₁ x₂ y₂ hdet

end Erdos633b
