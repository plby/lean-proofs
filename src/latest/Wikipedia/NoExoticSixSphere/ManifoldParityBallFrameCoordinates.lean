import Wikipedia.NoExoticSixSphere.ManifoldFrameBlockCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBoundaryMaps

/-!
# The actual frame-coordinate changes extend across every retained parity ball

The original ball chart gives maps of the whole closed four-ball into the
valid source and target chart domains. The coordinate families and their
inverses are continuous there, including at the intrinsic singular center.
On the boundary, the global operator is exactly the retained parity-one
linking operator with identity normal columns, in these coordinates.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBall

open GLOrthonormalization FrameBlockCoordinates
open Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)

def diskChart : C(DiskCylinder.Disk (E := Vector 4), ℝ × Sphere 3) :=
  ⟨fun z ↦ B.chart z.val,
    (B.chart.contMDiffOn_toFun.continuousOn.mono B.ball_source).domRestrict⟩

theorem diskChart_boundary (s : Sphere 3) :
    B.diskChart (DiskCylinder.boundaryToDisk s) = B.boundaryMap s := rfl

def diskSourcePoint : C(DiskCylinder.Disk (E := Vector 4), B.sourceChart.source) where
  toFun z := ⟨(B.diskChart z).2, (B.chart_valid z.val z.property).2.1⟩
  continuous_toFun := (continuous_snd.comp B.diskChart.continuous).subtype_mk _

def diskSourceCoordinates (k : ℕ) (z : DiskCylinder.Disk (E := Vector 4)) :
    Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  sourceCoordinates k B.sourceChart (B.diskSourcePoint z)

theorem continuous_diskSourceCoordinates (k : ℕ) :
    Continuous (fun z ↦ (B.diskSourceCoordinates k z).toContinuousLinearMap) :=
  (continuous_sourceCoordinates k B.sourceChart).comp B.diskSourcePoint.continuous

theorem continuous_inverse_diskSourceCoordinates (k : ℕ) :
    Continuous (fun z ↦ (B.diskSourceCoordinates k z).symm.toContinuousLinearMap) :=
  (continuous_inverse_sourceCoordinates k B.sourceChart).comp B.diskSourcePoint.continuous

variable (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

def diskTargetPoint : C(DiskCylinder.Disk (E := Vector 4), B.targetChart.source) where
  toFun z := ⟨g (B.diskChart z).1 (B.diskChart z).2, (B.chart_valid z.val z.property).2.2⟩
  continuous_toFun := (hg.continuous.comp B.diskChart.continuous).subtype_mk _

variable (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

def diskTargetCoordinates (z : DiskCylinder.Disk (E := Vector 4)) :
    Vector ((e.ambientDimension - 6) + 6) ≃L[ℝ] Vector e.ambientDimension :=
  e.normalChartCoordinates a B.targetChart (B.diskTargetPoint hg z)

theorem continuous_diskTargetCoordinates :
    Continuous (fun z ↦ (B.diskTargetCoordinates hg e a z).toContinuousLinearMap) :=
  (e.continuous_normalChartCoordinates a B.targetChart).comp (B.diskTargetPoint hg).continuous

theorem continuous_inverse_diskTargetCoordinates :
    Continuous (fun z ↦ (B.diskTargetCoordinates hg e a z).symm.toContinuousLinearMap) :=
  (e.continuous_inverse_normalChartCoordinates a B.targetChart).comp
    (B.diskTargetPoint hg).continuous

theorem boundary_operator_factorization (s : Sphere 3) :
    e.normalSpatialOperator a g (B.boundaryMap s) =
      (B.diskTargetCoordinates hg e a (DiskCylinder.boundaryToDisk s)).toContinuousLinearMap.comp
        ((identityBlockOperator (e.ambientDimension - 6) (B.link s).val).comp
          (B.diskSourceCoordinates (e.ambientDimension - 6)
            (DiskCylinder.boundaryToDisk s)).toContinuousLinearMap) := by
  rw [B.link_value]
  exact e.normalSpatialOperator_in_charts a g hg B.sourceChart B.targetChart
    (B.chart s.val) (B.chart_valid s.val (Metric.sphere_subset_closedBall s.property)).2.1
      (B.chart_valid s.val (Metric.sphere_subset_closedBall s.property)).2.2

end NoExoticSixSphere.SphereFamily.ParityBall
