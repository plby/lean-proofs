import Wikipedia.NoExoticSixSphere.QuaternionicHopfFactorTangentOperators
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame

/-!
# The actual factor-frame maps before normal-column normalization

Both maps are homotopic to the normal-plus-tangent maps used by geometric
parity. Their formulas retain the original ambient and normal coordinates,
including the radius, signs, and doubled tangent operators. The parity test
still includes the actual sphere-dependent source twist.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Stiefel SpanningDiskFrameCoordinates DiskBoundary SphereThreeTangentFrame

local instance : ChartedSpace (V 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas

def southPairLeftRawFrameMap : C(Sphere 3, Monomorphism.Space 16 13) :=
  southPairEuclideanEmbedding.rawSphereFrameOperatorMap southPairEuclideanNormalFrame
    southPairLeftSphere contMDiff_southPairLeftSphere southPairLeftSphere_differential_injective

def southPairRightRawFrameMap : C(Sphere 3, Monomorphism.Space 16 13) :=
  southPairEuclideanEmbedding.rawSphereFrameOperatorMap southPairEuclideanNormalFrame
    southPairRightSphere contMDiff_southPairRightSphere southPairRightSphere_differential_injective

theorem southPairLeftRawFrameMap_value (s : Sphere 3) :
    (southPairLeftRawFrameMap s).val =
      OperatorSum.operator (southPairEuclideanNormalOperator (s, spherePole 3))
        (southPairLeftAmbientLinear.comp (operator s.val)) := by
  change OperatorSum.operator (southPairEuclideanNormalFrame.ambient (southPairLeftSphere s))
    (framedDerivative (southPairEuclideanAmbient ∘ southPairLeftSphere) s) = _
  rw [southPairEuclideanNormalFrame_ambient, southPairLeftSphere_apply]
  exact congrArg (fun L : V 3 →L[ℝ] V 16 ↦
    OperatorSum.operator (southPairEuclideanNormalOperator (s, spherePole 3)) L)
      (southPairLeftSphere_framedDerivative s)

theorem southPairRightRawFrameMap_value (s : Sphere 3) :
    (southPairRightRawFrameMap s).val =
      OperatorSum.operator (southPairEuclideanNormalOperator (spherePole 3, s))
        (southPairRightAmbientLinear.comp (operator s.val)) := by
  change OperatorSum.operator (southPairEuclideanNormalFrame.ambient (southPairRightSphere s))
    (framedDerivative (southPairEuclideanAmbient ∘ southPairRightSphere) s) = _
  rw [southPairEuclideanNormalFrame_ambient, southPairRightSphere_apply]
  exact congrArg (fun L : V 3 →L[ℝ] V 16 ↦
    OperatorSum.operator (southPairEuclideanNormalOperator (spherePole 3, s)) L)
      (southPairRightSphere_framedDerivative s)

theorem southPairEuclideanNormalOperator_apply (p : Sphere 3 × Sphere 3) (v : V 10) :
    southPairEuclideanNormalOperator p v = southPairAmbientEuclideanCoordinates
      (southPairNormalFrame.ambient p (southPairNormalEuclideanCoordinates.symm v)) := rfl

theorem southPairLeftRawFrameMap_apply (s : Sphere 3) (v : V 13) :
    (southPairLeftRawFrameMap s).val v = southPairAmbientEuclideanCoordinates
      (southPairNormalFrame.ambient (s, spherePole 3)
        (southPairNormalEuclideanCoordinates.symm
          (EuclideanSpace.finAddEquivProd (n := 10) (m := 3) v).1) +
        (2 : ℝ) • WithLp.toLp 2
          (southAxis (operator s.val (EuclideanSpace.finAddEquivProd v).2), (0 : V 8))) := by
  rw [southPairLeftRawFrameMap_value, OperatorSum.operator_apply,
    southPairEuclideanNormalOperator_apply, ContinuousLinearMap.comp_apply,
    southPairLeftAmbientLinear_apply, map_add]

theorem southPairRightRawFrameMap_apply (s : Sphere 3) (v : V 13) :
    (southPairRightRawFrameMap s).val v = southPairAmbientEuclideanCoordinates
      (southPairNormalFrame.ambient (spherePole 3, s)
        (southPairNormalEuclideanCoordinates.symm
          (EuclideanSpace.finAddEquivProd (n := 10) (m := 3) v).1) +
        (2 : ℝ) • WithLp.toLp 2
          ((0 : V 8), southAxis (operator s.val (EuclideanSpace.finAddEquivProd v).2))) := by
  rw [southPairRightRawFrameMap_value, OperatorSum.operator_apply,
    southPairEuclideanNormalOperator_apply, ContinuousLinearMap.comp_apply,
    southPairRightAmbientLinear_apply, map_add]

theorem southPairLeftRawFrameMap_homotopic : southPairLeftRawFrameMap.Homotopic
    (southPairEuclideanEmbedding.sphereFrameOperatorMap southPairEuclideanNormalFrame
      southPairLeftSphere contMDiff_southPairLeftSphere
        southPairLeftSphere_differential_injective) :=
  southPairEuclideanEmbedding.rawSphereFrameOperatorMap_homotopic southPairEuclideanNormalFrame
    southPairLeftSphere contMDiff_southPairLeftSphere southPairLeftSphere_differential_injective

theorem southPairRightRawFrameMap_homotopic : southPairRightRawFrameMap.Homotopic
    (southPairEuclideanEmbedding.sphereFrameOperatorMap southPairEuclideanNormalFrame
      southPairRightSphere contMDiff_southPairRightSphere
        southPairRightSphere_differential_injective) :=
  southPairEuclideanEmbedding.rawSphereFrameOperatorMap_homotopic southPairEuclideanNormalFrame
    southPairRightSphere contMDiff_southPairRightSphere southPairRightSphere_differential_injective

theorem southPairLeftSphere_parity_zero_iff :
    southPairEuclideanEmbedding.sphereParity southPairEuclideanNormalFrame
      southPairLeftSphere contMDiff_southPairLeftSphere southPairLeftSphere_injective
        southPairLeftSphere_differential_injective = 0 ↔
      Extends (twistedBlockMap (k := 10) southPairLeftRawFrameMap) :=
  southPairEuclideanEmbedding.sphereParity_zero_iff_raw_twisted_extension
    southPairEuclideanNormalFrame southPairLeftSphere contMDiff_southPairLeftSphere
      southPairLeftSphere_differential_injective southPairLeftSphere_injective

theorem southPairRightSphere_parity_zero_iff :
    southPairEuclideanEmbedding.sphereParity southPairEuclideanNormalFrame
      southPairRightSphere contMDiff_southPairRightSphere southPairRightSphere_injective
        southPairRightSphere_differential_injective = 0 ↔
      Extends (twistedBlockMap (k := 10) southPairRightRawFrameMap) :=
  southPairEuclideanEmbedding.sphereParity_zero_iff_raw_twisted_extension
    southPairEuclideanNormalFrame southPairRightSphere contMDiff_southPairRightSphere
      southPairRightSphere_differential_injective southPairRightSphere_injective

end NoExoticSixSphere.QuaternionicHopf
