import Wikipedia.NoExoticSixSphere.OutwardGraphNormalCoordinates
import Wikipedia.NoExoticSixSphere.BoundaryOperatorParityCriterion

/-!
# Original geometric sphere parity from a framed hypersurface boundary operator

The original boundary frame is an appended normal frame, in explicitly
retained normal-model coordinates. Graph the height derivative and use
the proved two-stage homotopy. The resulting extension criterion concerns
the original geometric sphere parity, not a newly assigned obstruction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary OutwardGraphFrame CollaredDiskFrame

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_iff_outwardOperator_extends {k : ℕ}
    (hN : e.ambientDimension = 3 + (k + 4))
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (A : C(Sphere 3, Vector k →L[ℝ] Vector e.ambientDimension))
    (D : C(Sphere 3, Vector 4 →L[ℝ] Vector e.ambientDimension))
    (ν : C(Sphere 3, Vector e.ambientDimension))
    (ξ : C(Sphere 3, Vector e.ambientDimension →L[ℝ] ℝ))
    (Q : e.NormalModel ≃L[ℝ] Vector (k + 1))
    (P : C(Sphere 3, Monomorphism.Space e.ambientDimension (k + 4)))
    (hP : ∀ s, (P s).val = OperatorSum.operator (A s) (D s))
    (ha : ∀ s, a.ambient (f s) =
      (OrthogonalFrameAppend.operator (A s) (ν s)).comp Q.toContinuousLinearMap)
    (hD : ∀ s : Sphere 3, fderiv ℝ F s.val = graph (D s) (ξ s))
    (hA : ∀ s u, ξ s (A s u) = 0) (hν : ∀ s, ξ s (ν s) < 0)
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    e.sphereParity a f hf hi hd = 0 ↔ Extends P := by
  have hAD : ∀ s, Injective ((A s).coprod (D s)) :=
    fun s ↦ coprod_injective_of_operator (P s) (A s) (D s) (hP s)
  let G := outwardMap A D ν ξ Q hAD hA hν
  have hG (s : Sphere 3) : (G s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val) := by
    rw [ha, hD]
    exact outwardMap_value A D ν ξ Q hAD hA hν s
  exact (e.sphereParity_zero_iff_boundaryOperator_extends a f hf hi hd F hF hb G hG hheight).trans
    (extends_outward_normalCoordinates_iff hN A D ν ξ Q P G hP
      (outwardMap_value A D ν ξ Q hAD hA hν) hA hν)

end NoExoticSixSphere.EuclideanEmbedding
