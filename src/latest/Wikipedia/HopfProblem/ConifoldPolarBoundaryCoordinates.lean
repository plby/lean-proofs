import Wikipedia.HopfProblem.ConifoldPolarDefs

/-!
# Marked boundary frames in real normal coordinates

These identities express the original second column of the product of the two
marked boundary frames in the fixed four-dimensional real normal coordinates.
They require no unit-length or nonvanishing assumptions.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- The marked second-column formula in the original four real normal coordinates. -/
theorem normalCoordinates_unitaryFrame_mul_rowFrame
    (r : ℝ) (v : Fin 2 → ℂ) (α β : ℂ) :
    normalCoordinates (unitaryFrame v * rowFrame r α β) =
      (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ![((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).re,
          ((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).im,
          ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).re,
          ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).im] := by
  simp only [normalCoordinates, unitaryFrame_mul_rowFrame_secondColumn]

/-- The same marked normal coordinates, with each real component divided by the radius. -/
theorem normalCoordinates_unitaryFrame_mul_rowFrame_real
    (r : ℝ) (v : Fin 2 → ℂ) (α β : ℂ) :
    normalCoordinates (unitaryFrame v * rowFrame r α β) =
      (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ![(v 0 * β + jVector v 0 * conj α).re / r,
          (v 0 * β + jVector v 0 * conj α).im / r,
          (v 1 * β + jVector v 1 * conj α).re / r,
          (v 1 * β + jVector v 1 * conj α).im / r] := by
  simp only [normalCoordinates_unitaryFrame_mul_rowFrame,
    Complex.div_ofReal_re, Complex.div_ofReal_im]

end Wikipedia.HopfProblem.ConifoldPolar
