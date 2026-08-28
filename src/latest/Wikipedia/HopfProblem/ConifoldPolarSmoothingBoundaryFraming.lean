import Wikipedia.HopfProblem.ConifoldPolarBoundary
import Wikipedia.HopfProblem.ConifoldPolarTargetAlgebraUnitary

/-!
# The original marked rank-one boundary coordinates

The rank-one matrix is packaged in its existing conifold boundary subtype.
Its marked normal vector is defined by the literal second-column expression,
with the original signs, conjugation, and radius normalization.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- A rank-one matrix on the original conifold Frobenius level. -/
def rankOneBoundary (r : ℝ) (v : Fin 2 → ℂ)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    ConifoldBoundary r :=
  ⟨rankOneMatrix v α β, det_rankOneMatrix v α β, by
    rw [frobeniusSq_rankOneMatrix, hv, hαβ, one_mul]⟩

@[simp] theorem rankOneBoundary_val (r : ℝ) (v : Fin 2 → ℂ)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (rankOneBoundary r v hv α β hαβ).val = rankOneMatrix v α β := rfl

/-- The marked normal vector in the original four real coordinates. -/
def markedNormalVector (r : ℝ) (v : Fin 2 → ℂ) (α β : ℂ) : Normal :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    ![((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).re,
      ((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).im,
      ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).re,
      ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).im]

theorem markedNormalVector_real (r : ℝ) (v : Fin 2 → ℂ) (α β : ℂ) :
    markedNormalVector r v α β =
      (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ![(v 0 * β + jVector v 0 * conj α).re / r,
          (v 0 * β + jVector v 0 * conj α).im / r,
          (v 1 * β + jVector v 1 * conj α).re / r,
          (v 1 * β + jVector v 1 * conj α).im / r] := by
  simp only [markedNormalVector, Complex.div_ofReal_re, Complex.div_ofReal_im]

theorem normalCoordinates_boundary_rankOne {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    normalCoordinates (unitaryPart
      (ConifoldStandardBoundary.boundaryHomeomorph hr (rankOneBoundary r v hv α β hαβ)).val) =
        markedNormalVector r v α β :=
  normalCoordinates_unitaryPart_forward_rankOneMatrix hr v hv α β hαβ

theorem positivePart_boundary_rankOne {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    positivePart
      (ConifoldStandardBoundary.boundaryHomeomorph hr (rankOneBoundary r v hv α β hαβ)).val =
        unitaryFrame v * radialDiagonal r * (unitaryFrame v).conjTranspose :=
  positivePart_forward_rankOneMatrix hr v hv α β hαβ

theorem markedNormalVector_norm {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    ‖markedNormalVector r v α β‖ = 1 := by
  rw [← normalCoordinates_boundary_rankOne hr v hv α β hαβ]
  apply norm_normalCoordinates_eq_one
  · exact adjointAdjugate_unitaryPart _
  · apply det_unitaryPart
    exact (ConifoldStandardBoundary.boundaryHomeomorph hr
      (rankOneBoundary r v hv α β hαβ)).property.1

theorem markedNormalVector_mem_sphere {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    markedNormalVector r v α β ∈ NormalSphere := by
  simpa only [Metric.mem_sphere, dist_zero_right] using
    markedNormalVector_norm hr v hv α β hαβ

/-- The same literal marked normal vector, now in its original unit-sphere subtype. -/
def markedNormalSphere {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) : NormalSphere :=
  ⟨markedNormalVector r v α β, markedNormalVector_mem_sphere hr v hv α β hαβ⟩

@[simp] theorem markedNormalSphere_val {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (markedNormalSphere hr v hv α β hαβ).val = markedNormalVector r v α β := rfl

end Wikipedia.HopfProblem.ConifoldPolar
