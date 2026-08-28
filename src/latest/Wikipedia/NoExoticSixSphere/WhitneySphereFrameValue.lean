import Wikipedia.NoExoticSixSphere.WhitneySphereContraction
import Wikipedia.NoExoticSixSphere.GeometricSphereParityNullhomotopy

/-!
# The actual source-twisted frame obstruction of a Whitney sphere is one

The chart-contained map is a constructed nullhomotopic self-transverse
immersion with exactly one unordered double point. The previously proved
homotopy invariance of corrected geometric parity therefore computes its
frame obstruction. No local obstruction value is assigned by definition.
Comparison with the glued sphere's frame map is a separate obligation.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization WhitneySphere SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hprod : closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 ⊆ Φ.source)

include r in
theorem immersedSphereFrameParity_whitney :
    e.immersedSphereFrameParity a (chartMap Φ)
      (contMDiff_chartMap Φ hprod) (injective_mfderiv_chartMap Φ hprod) = 1 := by
  let f := chartContinuousMap Φ hprod
  have hz := e.geometricSphereParity_zero_of_nullhomotopic a r f (Φ 0)
    ⟨contraction Φ hprod⟩
  have he := e.geometricSphereParity_eq_representative a r f f
    (contMDiff_chartMap Φ hprod) (injective_mfderiv_chartMap Φ hprod)
    ((nativeSphereSelfTransverse_iff _).mp (selfTransverse_chartMap Φ hprod))
    (ContinuousMap.Homotopic.refl f)
  rw [he] at hz
  change e.immersedSphereFrameParity a (chartMap Φ)
    (contMDiff_chartMap Φ hprod) (injective_mfderiv_chartMap Φ hprod) +
      SphereSelfIntersections.unorderedParity (chartMap Φ) = 0 at hz
  rw [unorderedParity_chartMap Φ hprod] at hz
  have h := eq_neg_of_add_eq_zero_left hz
  simpa only [ZMod.neg_eq_self_mod_two] using h

include r in
theorem twistedWhitneyFrame_not_extends :
    ¬ DiskBoundary.Extends (SpanningDiskFrameCoordinates.twistedBlockMap
      (e.sphereFrameOperatorMap a (chartMap Φ)
        (contMDiff_chartMap Φ hprod) (injective_mfderiv_chartMap Φ hprod))) := by
  intro h
  have hz := (e.immersedSphereFrameParity_zero_iff a (chartMap Φ)
    (contMDiff_chartMap Φ hprod) (injective_mfderiv_chartMap Φ hprod)).mpr h
  rw [e.immersedSphereFrameParity_whitney a r Φ hprod] at hz
  exact one_ne_zero hz

end NoExoticSixSphere.EuclideanEmbedding
