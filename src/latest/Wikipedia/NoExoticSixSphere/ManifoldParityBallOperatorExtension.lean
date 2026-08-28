import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension
import Wikipedia.NoExoticSixSphere.ManifoldParityBallFrameCoordinates

/-!
# The actual global operator has nonzero obstruction on every retained ball

The retained chart link is stabilized by the actual identity normal block.
The coordinate changes extend over the whole ball, so exact extension of
the global boundary operator is equivalent to extension of the original
parity-one chart link. In particular, neither boundary operator extends.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBall

open GLOrthonormalization Stiefel DiskBoundary
open Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)
  (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

include hg in
theorem injective_boundary_normalSpatialOperator (s : Sphere 3) :
    Injective (e.normalSpatialOperator a g (B.boundaryMap s)) := by
  rw [B.boundary_operator_factorization hg e a s]
  exact (B.diskTargetCoordinates hg e a (DiskCylinder.boundaryToDisk s)).injective.comp
    ((FrameBlockCoordinates.identityBlockOperator_injective _ (B.link s).val
      (B.link s).property).comp
        (B.diskSourceCoordinates _ (DiskCylinder.boundaryToDisk s)).injective)

def globalOperatorLink :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) where
  toFun s := ⟨e.normalSpatialOperator a g (B.boundaryMap s),
    B.injective_boundary_normalSpatialOperator hg e a s⟩
  continuous_toFun := ((e.contMDiff_normalSpatialOperator a g hg).continuous.comp
    B.boundaryMap.continuous).subtype_mk _

theorem globalOperatorLink_value (s : Sphere 3) :
    (B.globalOperatorLink hg e a s).val = e.normalSpatialOperator a g (B.boundaryMap s) := rfl

theorem extends_globalOperatorLink_iff :
    Extends (B.globalOperatorLink hg e a) ↔ Extends B.link := by
  have he : Extends (B.globalOperatorLink hg e a) ↔
      Extends ((Monomorphism.frontBlockMap (e.ambientDimension - 6)).comp B.link) := by
    apply Monomorphism.extends_recoordinate_iff
      (B.diskTargetCoordinates hg e a) (B.diskSourceCoordinates (e.ambientDimension - 6))
      (B.continuous_diskTargetCoordinates hg e a)
      (B.continuous_inverse_diskTargetCoordinates hg e a)
      (B.continuous_diskSourceCoordinates _) (B.continuous_inverse_diskSourceCoordinates _)
      ((Monomorphism.frontBlockMap (e.ambientDimension - 6)).comp B.link)
      (B.globalOperatorLink hg e a)
    intro s
    apply Subtype.ext
    exact B.boundary_operator_factorization hg e a s
  exact he.trans (Monomorphism.extends_frontBlockMap_iff (by decide) rfl _ B.link)

theorem globalOperatorLink_not_extends : ¬ Extends (B.globalOperatorLink hg e a) := by
  intro h
  have hz := (Monomorphism.sphereParity_zero_iff_extension 1 B.link).mpr
    ((B.extends_globalOperatorLink_iff hg e a).mp h)
  rw [B.parity_one] at hz
  exact one_ne_zero hz

theorem normalized_globalOperatorLink_not_extends :
    ¬ Extends ((Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 6) + 3)).comp
      (B.globalOperatorLink hg e a)) := by
  intro h
  exact B.globalOperatorLink_not_extends hg e a ((extends_normalize_iff _).mp h)

end NoExoticSixSphere.SphereFamily.ParityBall
