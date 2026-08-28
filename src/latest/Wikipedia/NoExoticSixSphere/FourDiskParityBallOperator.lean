import Wikipedia.NoExoticSixSphere.ManifoldFourDiskChartOperator
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension

/-!
# The actual global operator on a retained four-disk singularity ball

The original target coordinates and the prescribed normal frame define
coordinates over the whole closed ball, including its singular center.
Their inverses are continuous there. Exact disk extension of the global
link is therefore equivalent to extension of the original parity-one
chart link; no coordinate change is assumed to extend just from its
boundary values.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBall

open GLOrthonormalization Stiefel DiskBoundary FrameBlockCoordinates
open Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} {x : Vector 4} (B : ParityBall g x)
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def diskChartPoint (z : DiskCylinder.Disk (E := Vector 4)) : B.targetChart.source :=
  ⟨g (B.chart z.val), (B.chart_valid z.val z.property).2⟩

def diskTargetCoordinates (z : DiskCylinder.Disk (E := Vector 4)) :
    Vector ((e.ambientDimension - 7) + 7) ≃L[ℝ] Vector e.ambientDimension :=
  e.normalChartCoordinates a B.targetChart (B.diskChartPoint z)

variable (hg : ∀ z ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g z)

include hg

theorem continuous_diskChartPoint : Continuous B.diskChartPoint := by
  have hc : Continuous (fun z : DiskCylinder.Disk (E := Vector 4) ↦ B.chart z.val) :=
    (B.chart.contMDiffOn_toFun.continuousOn.mono B.ball_source).domRestrict
  have hgc : ContinuousOn g (closedBall 0 1) :=
    fun z hz ↦ (hg z hz).continuousAt.continuousWithinAt
  exact (hgc.comp_continuous hc
    (fun z ↦ ball_subset_closedBall (B.chart_valid z.val z.property).1)).subtype_mk _

theorem continuous_diskTargetCoordinates :
    Continuous (fun z ↦ (B.diskTargetCoordinates e a z).toContinuousLinearMap) :=
  (e.continuous_normalChartCoordinates a B.targetChart).comp (B.continuous_diskChartPoint hg)

theorem continuous_inverse_diskTargetCoordinates :
    Continuous (fun z ↦ (B.diskTargetCoordinates e a z).symm.toContinuousLinearMap) :=
  (e.continuous_inverse_normalChartCoordinates a B.targetChart).comp
    (B.continuous_diskChartPoint hg)

theorem boundary_operator_factorization (s : Sphere 3) :
    e.normalFourDiskOperator a g (B.chart s.val) =
      (B.diskTargetCoordinates e a (DiskCylinder.boundaryToDisk s)).toContinuousLinearMap.comp
        (identityBlockOperator (e.ambientDimension - 7) (B.link s).val) := by
  have hs := B.chart_valid s.val (sphere_subset_closedBall s.property)
  rw [B.link_value]
  exact e.normalFourDiskOperator_in_chart g (B.chart s.val)
    ((hg _ (ball_subset_closedBall hs.1)).mdifferentiableAt (by simp)) B.targetChart hs.2 a

theorem injective_boundary_normalFourDiskOperator (s : Sphere 3) :
    Injective (e.normalFourDiskOperator a g (B.chart s.val)) := by
  rw [B.boundary_operator_factorization e a hg s]
  exact (B.diskTargetCoordinates e a (DiskCylinder.boundaryToDisk s)).injective.comp
    (identityBlockOperator_injective _ (B.link s).val (B.link s).property)

def globalOperatorLink :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) where
  toFun s := ⟨e.normalFourDiskOperator a g (B.chart s.val),
    B.injective_boundary_normalFourDiskOperator e a hg s⟩
  continuous_toFun := by
    have hc : Continuous (fun s : Sphere 3 ↦ B.chart s.val) :=
      (B.chart.contMDiffOn_toFun.continuousOn.mono
        (sphere_subset_closedBall.trans B.ball_source)).domRestrict
    exact ((e.continuousOn_normalFourDiskOperator a g hg).comp_continuous hc
      (fun s ↦ ball_subset_closedBall
        (B.chart_valid s.val (sphere_subset_closedBall s.property)).1)).subtype_mk _

theorem globalOperatorLink_value (s : Sphere 3) :
    (B.globalOperatorLink e a hg s).val = e.normalFourDiskOperator a g (B.chart s.val) := rfl

theorem extends_globalOperatorLink_iff :
    Extends (B.globalOperatorLink e a hg) ↔ Extends B.link := by
  have he : Extends (B.globalOperatorLink e a hg) ↔
      Extends ((Monomorphism.frontBlockMap (e.ambientDimension - 7)).comp B.link) := by
    apply Monomorphism.extends_recoordinate_iff
      (B.diskTargetCoordinates e a)
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector ((e.ambientDimension - 7) + 4)))
      (B.continuous_diskTargetCoordinates e a hg)
      (B.continuous_inverse_diskTargetCoordinates e a hg)
      continuous_const continuous_const
      ((Monomorphism.frontBlockMap (e.ambientDimension - 7)).comp B.link)
      (B.globalOperatorLink e a hg)
    intro s
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A : Vector ((e.ambientDimension - 7) + 4) →L[ℝ]
      Vector e.ambientDimension ↦ A v) (B.boundary_operator_factorization e a hg s)
  exact he.trans (Monomorphism.extends_frontBlockMap_iff (by decide) rfl _ B.link)

theorem globalOperatorLink_not_extends : ¬ Extends (B.globalOperatorLink e a hg) := by
  intro h
  have hz := (Monomorphism.sphereParity_zero_iff_extension 2 B.link).mpr
    ((B.extends_globalOperatorLink_iff e a hg).mp h)
  rw [B.parity_one] at hz
  exact one_ne_zero hz

theorem normalized_globalOperatorLink_not_extends :
    ¬ Extends ((Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 7) + 4)).comp
      (B.globalOperatorLink e a hg)) := by
  intro h
  exact B.globalOperatorLink_not_extends e a hg ((extends_normalize_iff _).mp h)

end NoExoticSixSphere.GenericFourDisk.ParityBall
