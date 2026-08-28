import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductFactorSpheres
import Wikipedia.NoExoticSixSphere.SphereAffineFrameDerivative

/-!
# The actual tangent operators of the embedded factor spheres

The original quaternionic source tangent frame is retained. The ambient
isometry and the doubled-radius factor remain explicit in both operators.
These computations do not assign a parity value to either factor.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open SphereThreeTangentFrame

def southPairLeftAmbientLinear : V 4 →L[ℝ] V 16 :=
  southPairAmbientEuclideanCoordinates.toContinuousLinearMap.comp
    ((2 : ℝ) • ((WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℝ (V 8) (V 8)).comp southAxis.toContinuousLinearMap)))

def southPairRightAmbientLinear : V 4 →L[ℝ] V 16 :=
  southPairAmbientEuclideanCoordinates.toContinuousLinearMap.comp
    ((2 : ℝ) • ((WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℝ (V 8) (V 8)).comp southAxis.toContinuousLinearMap)))

def southPairLeftAmbientConstant : V 16 :=
  southPairAmbientEuclideanCoordinates
    ((2 : ℝ) • WithLp.toLp 2 ((0 : V 8), southFiberAmbient (spherePole 3)))

def southPairRightAmbientConstant : V 16 :=
  southPairAmbientEuclideanCoordinates
    ((2 : ℝ) • WithLp.toLp 2 (southFiberAmbient (spherePole 3), (0 : V 8)))

theorem southPairLeftAmbientLinear_apply (v : V 4) :
    southPairLeftAmbientLinear v = southPairAmbientEuclideanCoordinates
      ((2 : ℝ) • WithLp.toLp 2 (southAxis v, (0 : V 8))) := rfl

theorem southPairRightAmbientLinear_apply (v : V 4) :
    southPairRightAmbientLinear v = southPairAmbientEuclideanCoordinates
      ((2 : ℝ) • WithLp.toLp 2 ((0 : V 8), southAxis v)) := rfl

theorem southPairEuclideanAmbient_apply (p : Sphere 3 × Sphere 3) :
    southPairEuclideanAmbient p = southPairAmbientEuclideanCoordinates
      ((2 : ℝ) • WithLp.toLp 2 (southFiberAmbient p.1, southFiberAmbient p.2)) := rfl

theorem southPairLeftSphere_ambient (s : Sphere 3) :
    southPairEuclideanAmbient (southPairLeftSphere s) =
      southPairLeftAmbientLinear s.val + southPairLeftAmbientConstant := by
  rw [southPairLeftSphere_apply, southPairEuclideanAmbient_apply, southPairLeftAmbientLinear_apply]
  change southPairAmbientEuclideanCoordinates
    ((2 : ℝ) • WithLp.toLp 2 (southFiberAmbient s, southFiberAmbient (spherePole 3))) =
      southPairAmbientEuclideanCoordinates ((2 : ℝ) • WithLp.toLp 2 (southFiberAmbient s, 0)) +
        southPairAmbientEuclideanCoordinates
          ((2 : ℝ) • WithLp.toLp 2 ((0 : V 8), southFiberAmbient (spherePole 3)))
  rw [← map_add, ← smul_add]
  congr 2
  apply WithLp.ofLp_injective
  simp only [WithLp.ofLp_add, Prod.mk_add_mk, add_zero, zero_add]

theorem southPairRightSphere_ambient (s : Sphere 3) :
    southPairEuclideanAmbient (southPairRightSphere s) =
      southPairRightAmbientLinear s.val + southPairRightAmbientConstant := by
  rw [southPairRightSphere_apply, southPairEuclideanAmbient_apply,
    southPairRightAmbientLinear_apply]
  change southPairAmbientEuclideanCoordinates
    ((2 : ℝ) • WithLp.toLp 2 (southFiberAmbient (spherePole 3), southFiberAmbient s)) =
      southPairAmbientEuclideanCoordinates
        ((2 : ℝ) • WithLp.toLp 2 ((0 : V 8), southFiberAmbient s)) +
        southPairAmbientEuclideanCoordinates
          ((2 : ℝ) • WithLp.toLp 2 (southFiberAmbient (spherePole 3), (0 : V 8)))
  rw [← map_add, ← smul_add]
  congr 2
  apply WithLp.ofLp_injective
  simp only [WithLp.ofLp_add, Prod.mk_add_mk, add_zero, zero_add]

theorem southPairLeftSphere_framedDerivative (s : Sphere 3) :
    framedDerivative (southPairEuclideanAmbient ∘ southPairLeftSphere) s =
      southPairLeftAmbientLinear.comp (operator s.val) := by
  have he : southPairEuclideanAmbient ∘ southPairLeftSphere =
      fun q : Sphere 3 ↦ southPairLeftAmbientLinear q.val + southPairLeftAmbientConstant :=
    funext southPairLeftSphere_ambient
  rw [he]
  exact framedDerivative_affine _ _ s

theorem southPairRightSphere_framedDerivative (s : Sphere 3) :
    framedDerivative (southPairEuclideanAmbient ∘ southPairRightSphere) s =
      southPairRightAmbientLinear.comp (operator s.val) := by
  have he : southPairEuclideanAmbient ∘ southPairRightSphere =
      fun q : Sphere 3 ↦ southPairRightAmbientLinear q.val + southPairRightAmbientConstant :=
    funext southPairRightSphere_ambient
  rw [he]
  exact framedDerivative_affine _ _ s

theorem southPairLeftSphere_framedDerivative_apply (s : Sphere 3) (v : V 3) :
    framedDerivative (southPairEuclideanAmbient ∘ southPairLeftSphere) s v =
      southPairAmbientEuclideanCoordinates
        ((2 : ℝ) • WithLp.toLp 2 (southAxis (operator s.val v), (0 : V 8))) := by
  rw [southPairLeftSphere_framedDerivative]
  rfl

theorem southPairRightSphere_framedDerivative_apply (s : Sphere 3) (v : V 3) :
    framedDerivative (southPairEuclideanAmbient ∘ southPairRightSphere) s v =
      southPairAmbientEuclideanCoordinates
        ((2 : ℝ) • WithLp.toLp 2 ((0 : V 8), southAxis (operator s.val v))) := by
  rw [southPairRightSphere_framedDerivative]
  rfl

end NoExoticSixSphere.QuaternionicHopf
