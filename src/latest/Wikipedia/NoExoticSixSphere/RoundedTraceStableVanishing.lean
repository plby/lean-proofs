import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalProductCollapse
import Wikipedia.NoExoticSixSphere.AffineProductCollapseSuspension

/-!
# Actual framed unit surgery preserves stable vanishing of the original collapse

For an orthonormal input frame, the trace's product representative uses
the original collapse and frame, with all coordinate signs accounted for.
The proved finite product/suspension comparison therefore gives precisely
the same stable vanishing criterion for the original manifold and the
actual surgery target. No vanishing or Arf detection is inferred.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (ha : ∀ x v, ‖a.ambient x v‖ = ‖v‖) (d : e.FramedCollapseData a)

omit [T2Space M] in
theorem original_product_finite_nullhomotopic_iff :
    (∃ r : ℕ, (SphereMapSuspension.iterate
      (OriginalEnd.orthonormalInputCollapseData A ha d).sphereMap r).Nullhomotopic) ↔
    ∃ r : ℕ, (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic := by
  let : Nonempty M := ⟨f (pole 3)⟩
  exact AffineProductCollapse.finite_collapseData_nullhomotopic_iff
    d (OriginalEnd.productAmbientCoordinates A) (OriginalEnd.productNormalCoordinates A)
    (OriginalEnd.heightOffset A) (OriginalEnd.productAmbientCoordinates_embedding A) (by
      intro x v
      rw [OriginalEnd.productAmbientCoordinates_frame, a.normalized_eq_self ha])

include ha in
theorem surgery_cubicalStableClass_eq_one_iff (hd : 8 ≤ e.ambientDimension) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∀ dS : (UnitSurgery.inducedEmbedding A hR).FramedCollapseData
      (UnitSurgery.normalFraming A hR),
      dS.cubicalStableClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) = 1 ↔
        d.cubicalStableClass hd = 1 := by
  let := UnitSurgery.targetChartedSpace A hR
  intro dS
  rw [OriginalEnd.surgery_cubicalStableClass_eq_orthonormal_product A hR ha d dS]
  have hdO : 8 ≤ (OriginalEnd.embedding A).ambientDimension :=
    endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))
  have hO :=
    (OriginalEnd.orthonormalInputCollapseData A ha d).cubicalStableClass_eq_one_iff_finite hdO
  exact hO.trans ((original_product_finite_nullhomotopic_iff A ha d).trans
    (d.cubicalStableClass_eq_one_iff_finite hd).symm)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
