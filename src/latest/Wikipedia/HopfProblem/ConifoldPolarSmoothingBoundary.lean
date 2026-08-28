import Wikipedia.HopfProblem.ConifoldPolarSmoothingBoundaryLevels
import Wikipedia.HopfProblem.ConifoldPolarSmoothingBoundaryFraming

/-!
# The original conifold boundary in explicit sphere-product coordinates

The existing boundary homeomorphism is followed by the literal polar
coordinates on the smoothing boundary.  The resulting Euclidean base radius
is `(r - r⁻¹) / 2`, and the marked rank-one formula retains its original
normal-frame signs and conjugation.  No global threefold complement is
identified by these standard-model results.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- The existing conifold boundary followed by the explicit smoothing polar coordinates. -/
def conifoldBoundaryHomeomorph {r : ℝ} (hr : 1 < r) :
    ConifoldBoundary r ≃ₜ ↥(Metric.sphere (0 : Base) (boundaryRadius r)) × NormalSphere :=
  (ConifoldStandardBoundary.boundaryHomeomorph hr).trans (smoothingBoundaryHomeomorph hr)

@[simp] theorem conifoldBoundaryHomeomorph_fst_val {r : ℝ} (hr : 1 < r)
    (M : ConifoldBoundary r) :
    (conifoldBoundaryHomeomorph hr M).1.val =
      baseCoordinates (positivePart (ConifoldStandardBoundary.forward r M.val)) := rfl

@[simp] theorem conifoldBoundaryHomeomorph_snd_val {r : ℝ} (hr : 1 < r)
    (M : ConifoldBoundary r) :
    (conifoldBoundaryHomeomorph hr M).2.val =
      normalCoordinates (unitaryPart (ConifoldStandardBoundary.forward r M.val)) := rfl

@[simp] theorem conifoldBoundaryHomeomorph_symm_val {r : ℝ} (hr : 1 < r)
    (q : ↥(Metric.sphere (0 : Base) (boundaryRadius r)) × NormalSphere) :
    ((conifoldBoundaryHomeomorph hr).symm q).val =
      ConifoldStandardBoundary.backward r (positiveMatrix q.1.val * unitaryMatrix q.2.val) :=
  rfl

/-- The original marked radial matrix gives the base coordinate of the smoothing boundary. -/
theorem smoothingBoundaryHomeomorph_markedBase {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (smoothingBoundaryHomeomorph hr
      (ConifoldStandardBoundary.boundaryHomeomorph hr (rankOneBoundary r v hv α β hαβ))).1.val =
        baseCoordinates (unitaryFrame v * radialDiagonal r * (unitaryFrame v).conjTranspose) := by
  rw [smoothingBoundaryHomeomorph_fst_val, positivePart_boundary_rankOne hr v hv α β hαβ]

/-- The smoothing boundary's `S³` coordinate is the literal original marked normal vector. -/
theorem smoothingBoundaryHomeomorph_markedNormal {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (smoothingBoundaryHomeomorph hr
      (ConifoldStandardBoundary.boundaryHomeomorph hr (rankOneBoundary r v hv α β hαβ))).2.val =
      (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ![((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).re,
          ((v 0 * β + jVector v 0 * conj α) / (r : ℂ)).im,
          ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).re,
          ((v 1 * β + jVector v 1 * conj α) / (r : ℂ)).im] := by
  rw [smoothingBoundaryHomeomorph_snd_val]
  exact normalCoordinates_boundary_rankOne hr v hv α β hαβ

theorem conifoldBoundaryHomeomorph_markedBase {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (conifoldBoundaryHomeomorph hr (rankOneBoundary r v hv α β hαβ)).1.val =
      baseCoordinates (unitaryFrame v * radialDiagonal r * (unitaryFrame v).conjTranspose) :=
  smoothingBoundaryHomeomorph_markedBase hr v hv α β hαβ

theorem conifoldBoundaryHomeomorph_markedNormal {r : ℝ} (hr : 1 < r)
    (v : Fin 2 → ℂ) (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (α β : ℂ) (hαβ : Complex.normSq α + Complex.normSq β = r ^ 2) :
    (conifoldBoundaryHomeomorph hr (rankOneBoundary r v hv α β hαβ)).2 =
      markedNormalSphere hr v hv α β hαβ := by
  apply Subtype.ext
  exact smoothingBoundaryHomeomorph_markedNormal hr v hv α β hαβ

/-- The full boundary composition preserves the original opposite-weight circle marking. -/
theorem conifoldBoundaryHomeomorph_circle {r : ℝ} (hr : 1 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (M : ConifoldBoundary r) :
    conifoldBoundaryHomeomorph hr (conifoldCircle u hu M) =
      ((conifoldBoundaryHomeomorph hr M).1,
        sphereRotation u hu (conifoldBoundaryHomeomorph hr M).2) := by
  change smoothingBoundaryHomeomorph hr
      (ConifoldStandardBoundary.boundaryHomeomorph hr (conifoldCircle u hu M)) =
    ((smoothingBoundaryHomeomorph hr (ConifoldStandardBoundary.boundaryHomeomorph hr M)).1,
      sphereRotation u hu
        (smoothingBoundaryHomeomorph hr (ConifoldStandardBoundary.boundaryHomeomorph hr M)).2)
  rw [ConifoldStandardBoundary.boundaryHomeomorph_circle, smoothingBoundaryHomeomorph_circle]

end Wikipedia.HopfProblem.ConifoldPolar
