import Wikipedia.NoExoticSixSphere.NormalDisplacementDerivative
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Local normal neighborhoods

Normal displacement is a smooth local diffeomorphism at every point of the
zero section. This is a local statement; a single globally injective tubular
neighborhood still requires a separate argument.
-/

open scoped Manifold ContDiff Bundle
open Bundle

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M)

/-- The normal-coordinate displacement has a smooth local inverse at zero. -/
theorem isLocalDiffeomorphAt_localNormalDisplacement (x : M) :
    IsLocalDiffeomorphAt ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      (e.localNormalDisplacement x) (x, 0) := by
  exact isLocalDiffeomorphAt_of_invertible_mvfderiv
    (e.contMDiff_localNormalDisplacement x) (e.localNormalDisplacement_derivative_isInvertible x)

/-- A normal-bundle trivialization viewed as a smooth partial diffeomorphism. -/
noncomputable def normalChartPartialDiffeomorph (x : M) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel))
      e.NormalBundle (M × e.NormalModel) ∞ where
  toPartialEquiv :=
    (trivializationAt e.NormalModel e.NormalSpace x).toOpenPartialHomeomorph.toPartialEquiv
  open_source := (trivializationAt e.NormalModel e.NormalSpace x).open_source
  open_target := (trivializationAt e.NormalModel e.NormalSpace x).open_target
  contMDiffOn_toFun := (trivializationAt e.NormalModel e.NormalSpace x).contMDiffOn
  contMDiffOn_invFun := (trivializationAt e.NormalModel e.NormalSpace x).contMDiffOn_symm

/-- The zero section has zero normal coordinates. -/
theorem normalChartPartialDiffeomorph_zero (x : M) :
    e.normalChartPartialDiffeomorph x (zeroSection e.NormalModel e.NormalSpace x) = (x, 0) := by
  change (x, ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x x 0) = (x, 0)
  rw [map_zero]

/-- The zero section lies in its centered normal chart. -/
theorem normalChart_source_zero (x : M) :
    zeroSection e.NormalModel e.NormalSpace x ∈ (e.normalChartPartialDiffeomorph x).source := by
  change x ∈ projectionTransportDomain e.normalProjection x
  exact mem_projectionTransportDomain e.normalProjection e.normalProjection_idempotent x

/-- Reading normal displacement in a valid normal chart gives the local coordinate expression. -/
theorem localNormalDisplacement_chart_apply (x : M) (v : e.NormalBundle)
    (hv : v ∈ (e.normalChartPartialDiffeomorph x).source) :
    e.localNormalDisplacement x (e.normalChartPartialDiffeomorph x v) =
      e.normalDisplacement v := by
  have hbase : v.proj ∈ projectionTransportDomain e.normalProjection x := hv
  have hback := ProjectionBundle.fromCoordinates_toCoordinates e.normalProjection
    e.normalProjection_idempotent e.normalModelEquiv x v.proj hbase v.2
  rw [e.localNormalDisplacement_eq]
  change e.normalDisplacement ⟨v.proj, ProjectionBundle.fromCoordinates
    e.normalProjection e.normalModelEquiv x v.proj
    (ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x v.proj v.2)⟩ = _
  rw [hback]

/-- Normal displacement is a smooth local diffeomorphism along the entire zero section. -/
theorem isLocalDiffeomorphAt_normalDisplacement_zero (x : M) :
    IsLocalDiffeomorphAt ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement (zeroSection e.NormalModel e.NormalSpace x) := by
  obtain ⟨d, hd, heq⟩ := e.isLocalDiffeomorphAt_localNormalDisplacement x
  let c := e.normalChartPartialDiffeomorph x
  have hc : zeroSection e.NormalModel e.NormalSpace x ∈ c.source :=
    e.normalChart_source_zero x
  have hcd : c (zeroSection e.NormalModel e.NormalSpace x) ∈ d.source := by
    rw [e.normalChartPartialDiffeomorph_zero]
    exact hd
  refine ⟨c.trans d, ⟨hc, hcd⟩, ?_⟩
  intro v hv
  exact (e.localNormalDisplacement_chart_apply x v hv.1).symm.trans (heq hv.2)

end NoExoticSixSphere.EuclideanEmbedding
