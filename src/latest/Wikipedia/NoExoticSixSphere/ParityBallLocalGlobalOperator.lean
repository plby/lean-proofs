import Wikipedia.NoExoticSixSphere.FourDiskParityBallOperator

/-!
# Original global frame columns on a parity ball in any source region

Only smoothness on the actual retained ball image is required. The
prescribed normal frame and original target chart give continuous target
coordinates over the entire model disk, including its singular center.
Their inverses are also continuous there, so extension of the actual
global link is equivalent to extension of the original parity-one link.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBall

open GLOrthonormalization Stiefel DiskBoundary FrameBlockCoordinates
open Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} {x : Vector 4} {U : Set (Vector 4)} (B : ParityBall g x U)
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def localChartPoint (z : DiskCylinder.Disk (E := Vector 4)) : B.targetChart.source :=
  ⟨g (B.chart z.val), (B.chart_valid z.val z.property).2⟩

def localTargetCoordinates (z : DiskCylinder.Disk (E := Vector 4)) :
    Vector ((e.ambientDimension - 7) + 7) ≃L[ℝ] Vector e.ambientDimension :=
  e.normalChartCoordinates a B.targetChart (B.localChartPoint z)

variable (hg : ∀ y ∈ B.closedRegion, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g y)

include hg

theorem continuous_localChartPoint : Continuous B.localChartPoint := by
  have hc : Continuous (fun z : DiskCylinder.Disk (E := Vector 4) ↦ B.chart z.val) :=
    (B.chart.contMDiffOn_toFun.continuousOn.mono B.ball_source).domRestrict
  have hgc : ContinuousOn g B.closedRegion :=
    fun y hy ↦ (hg y hy).continuousAt.continuousWithinAt
  exact (hgc.comp_continuous hc (fun z ↦ ⟨z.val, z.property, rfl⟩)).subtype_mk _

theorem continuous_localTargetCoordinates :
    Continuous (fun z ↦ (B.localTargetCoordinates e a z).toContinuousLinearMap) :=
  (e.continuous_normalChartCoordinates a B.targetChart).comp (B.continuous_localChartPoint hg)

theorem continuous_inverse_localTargetCoordinates :
    Continuous (fun z ↦ (B.localTargetCoordinates e a z).symm.toContinuousLinearMap) :=
  (e.continuous_inverse_normalChartCoordinates a B.targetChart).comp
    (B.continuous_localChartPoint hg)

theorem local_boundary_operator_factorization (s : Sphere 3) :
    e.normalFourDiskOperator a g (B.chart s.val) =
      (B.localTargetCoordinates e a (DiskCylinder.boundaryToDisk s)).toContinuousLinearMap.comp
        (identityBlockOperator (e.ambientDimension - 7) (B.link s).val) := by
  have hs := B.chart_valid s.val (sphere_subset_closedBall s.property)
  rw [B.link_value]
  exact e.normalFourDiskOperator_in_chart g (B.chart s.val)
    ((hg _ ⟨s.val, sphere_subset_closedBall s.property, rfl⟩).mdifferentiableAt (by simp))
    B.targetChart hs.2 a

theorem injective_local_boundary_operator (s : Sphere 3) :
    Injective (e.normalFourDiskOperator a g (B.chart s.val)) := by
  rw [B.local_boundary_operator_factorization e a hg s]
  exact (B.localTargetCoordinates e a (DiskCylinder.boundaryToDisk s)).injective.comp
    (identityBlockOperator_injective _ (B.link s).val (B.link s).property)

def localGlobalOperatorLink :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) where
  toFun s := ⟨e.normalFourDiskOperator a g (B.chart s.val),
    B.injective_local_boundary_operator e a hg s⟩
  continuous_toFun := by
    have hc : Continuous (fun s : Sphere 3 ↦ B.chart s.val) :=
      (B.chart.contMDiffOn_toFun.continuousOn.mono
        (sphere_subset_closedBall.trans B.ball_source)).domRestrict
    have hOp : ContinuousOn (e.normalFourDiskOperator a g) B.closedRegion :=
      fun y hy ↦ (e.contDiffAt_normalFourDiskOperator a g y
        (hg y hy)).continuousAt.continuousWithinAt
    exact (hOp.comp_continuous hc
      (fun s ↦ ⟨s.val, sphere_subset_closedBall s.property, rfl⟩)).subtype_mk _

theorem localGlobalOperatorLink_value (s : Sphere 3) :
    (B.localGlobalOperatorLink e a hg s).val = e.normalFourDiskOperator a g (B.chart s.val) := rfl

theorem extends_localGlobalOperatorLink_iff :
    Extends (B.localGlobalOperatorLink e a hg) ↔ Extends B.link := by
  have he : Extends (B.localGlobalOperatorLink e a hg) ↔
      Extends ((Monomorphism.frontBlockMap (e.ambientDimension - 7)).comp B.link) := by
    apply Monomorphism.extends_recoordinate_iff
      (B.localTargetCoordinates e a)
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector ((e.ambientDimension - 7) + 4)))
      (B.continuous_localTargetCoordinates e a hg)
      (B.continuous_inverse_localTargetCoordinates e a hg)
      continuous_const continuous_const
      ((Monomorphism.frontBlockMap (e.ambientDimension - 7)).comp B.link)
      (B.localGlobalOperatorLink e a hg)
    intro s
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A : Vector ((e.ambientDimension - 7) + 4) →L[ℝ]
      Vector e.ambientDimension ↦ A v) (B.local_boundary_operator_factorization e a hg s)
  exact he.trans (Monomorphism.extends_frontBlockMap_iff (by decide) rfl _ B.link)

theorem localGlobalOperatorLink_not_extends : ¬ Extends (B.localGlobalOperatorLink e a hg) := by
  intro h
  have hz := (Monomorphism.sphereParity_zero_iff_extension 2 B.link).mpr
    ((B.extends_localGlobalOperatorLink_iff e a hg).mp h)
  rw [B.parity_one] at hz
  exact one_ne_zero hz

theorem normalized_localGlobalOperatorLink_not_extends :
    ¬ Extends ((Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 7) + 4)).comp
      (B.localGlobalOperatorLink e a hg)) := by
  intro h
  exact B.localGlobalOperatorLink_not_extends e a hg ((extends_normalize_iff _).mp h)

end NoExoticSixSphere.GenericFourDisk.ParityBall
