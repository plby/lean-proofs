import Wikipedia.NoExoticSixSphere.CompactifiedCollapseNormalOperator
import Wikipedia.NoExoticSixSphere.CompactifiedCollapseFiberIdentification
import Wikipedia.NoExoticSixSphere.StereographicNormalFrameCoordinates
import Wikipedia.NoExoticSixSphere.RegularFiberTargetChartFrame

/-!
# The actual normal-frame identity for the compactified collapse fiber

Use the native fiber diffeomorphism, the genuine target projection chart,
and the original prescribed collapse frame. One fixed normal-coordinate
equivalence converts the new actual frame into the ordinary stabilization
of the original frame under the actual variable ambient equivalence.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization StereographicEquator Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (hd : e.ambientDimension = (e.ambientDimension - n) + n)

def compactifiedNormalCoordinates :
    Vector ((e.ambientDimension - n) + 1) ≃L[ℝ] Vector (e.ambientDimension + 1 - n) :=
  (normalEquationCoordinates (e.ambientDimension - n) d.radius d.radius_pos.ne').trans
    (RegularSphereFiber.normalCoordinates n hd).symm

theorem compactifiedNormalCoordinates_cancel (v : Vector ((e.ambientDimension - n) + 1)) :
    RegularSphereFiber.normalCoordinates n hd (d.compactifiedNormalCoordinates hd v) =
      normalEquationCoordinates (e.ambientDimension - n) d.radius d.radius_pos.ne' v := by
  simp only [compactifiedNormalCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

variable [IsManifold (𝓡 n) ∞ M]
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)))
  (hg : ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞ g)
  (hreg : ∀ y, g y = sphereZero (e.ambientDimension - n) →
    Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) g y))
  (hfiber : ∀ y, g y = sphereZero (e.ambientDimension - n) ↔ ∃ x, e.compactifiedEmbedding x = y)
  (hgerm : ∀ x, (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)

include hgerm in
theorem compactifiedFrame_ambient (b : Sphere e.ambientDimension) (x : M)
    (v : Vector ((e.ambientDimension - n) + 1)) :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - n)) hreg n
      (by simpa using hd);
    (RegularSphereFiber.frameWithTargetChart g hg (sphereZero (e.ambientDimension - n))
      hreg n hd b (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero_mem_projection_source _)).ambient
      (e.diffeomorphToCompactifiedFiber g hg hreg hd hfiber x)
      (d.compactifiedNormalCoordinates hd v) =
        augmentedCoordinates e.ambientDimension (e.toFun x)
          (BlockSum.operator 1 (a.ambient x) v) := by
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - n)) hreg n
    (by simpa using hd)
  rw [RegularSphereFiber.frameWithTargetChart_ambient]
  change orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart g
    (sphereZero (e.ambientDimension - n))
    (sphereProjectionDiffeomorph (e.ambientDimension - n)) b)
      (e.diffeomorphToCompactifiedFiber g hg hreg hd hfiber x).val.val)
        (RegularSphereFiber.normalCoordinates n hd (d.compactifiedNormalCoordinates hd v)) = _
  rw [e.diffeomorphToCompactifiedFiber_val, d.compactifiedNormalCoordinates_cancel]
  exact normalFrame_block (e.toFun x) (a.ambient x) d.radius d.radius_pos.ne' _
    (d.orthogonalRightInverse_compactified_equations g hg x (hgerm x) b) v

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
