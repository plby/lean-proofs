import Wikipedia.NoExoticSixSphere.QuaternionicHopfStabilizedTube
import Wikipedia.NoExoticSixSphere.RadialCompressionDerivative

/-!
# The fixed normal-coordinate change of the actual stabilized Hopf tube

The chosen tube radius is part of the coordinate change. Its negative
real-coordinate factor and quaternionic target-coordinate map are explicit.
The differential of the actual compressed tube is then the computed frame
composed with this invertible coordinate map.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

local instance : ChartedSpace (V 3) {x : Sphere 7 // sphereMap x = south} :=
  regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

def southNormalCoordinates (r : ℝ) (hr : r ≠ 0) : (V 4 × ℝ) ≃L[ℝ] SouthNormalModel :=
  (ContinuousLinearEquiv.prodComm ℝ (V 4) ℝ).trans
    (((LinearEquiv.smulOfNeZero ℝ ℝ (-2) (by norm_num)).toContinuousLinearEquiv.prodCongr
      (targetTailChartEquiv.symm.trans
        (LinearEquiv.smulOfNeZero ℝ ℍ (2 * r)
          (mul_ne_zero (by norm_num) hr)).toContinuousLinearEquiv)).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ).symm)

theorem southNormalCoordinates_apply (r : ℝ) (hr : r ≠ 0) (p : V 4 × ℝ) :
    southNormalCoordinates r hr p =
      WithLp.toLp 2 ((-2 : ℝ) * p.2, (2 * r) • targetTailChartEquiv.symm p.1) := rfl

def southCompressedNormalCoordinates (r : ℝ) (p : V 4 × ℝ) : SouthNormalModel :=
  southNormalCoordinates 1 one_ne_zero
    (OpenPartialHomeomorph.univBall (0 : V 4) r p.1, p.2)

theorem southCompressedNormalCoordinates_apply (r : ℝ) (p : V 4 × ℝ) :
    southCompressedNormalCoordinates r p = WithLp.toLp 2 ((2 : ℝ) * (-p.2),
      (2 : ℝ) • targetTailChartEquiv.symm
        (OpenPartialHomeomorph.univBall (0 : V 4) r p.1)) := by
  rw [southCompressedNormalCoordinates, southNormalCoordinates_apply, mul_one]
  congr 1
  apply Prod.ext
  · ring
  · rfl

theorem southNormalCoordinates_radius_comp (r : ℝ) (hr : r ≠ 0) :
    (southNormalCoordinates 1 one_ne_zero).toContinuousLinearMap.comp
        ((r • ContinuousLinearMap.id ℝ (V 4)).prodMap
          (ContinuousLinearMap.id ℝ ℝ)) =
      (southNormalCoordinates r hr).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro p
  change southNormalCoordinates 1 one_ne_zero (r • p.1, p.2) = southNormalCoordinates r hr p
  rw [southNormalCoordinates_apply, southNormalCoordinates_apply, map_smul, smul_smul, mul_one]

theorem hasFDerivAt_southCompressedNormalCoordinates (r : ℝ) (hr : 0 < r) :
    HasFDerivAt (southCompressedNormalCoordinates r)
      (southNormalCoordinates r hr.ne').toContinuousLinearMap 0 := by
  have h := (southNormalCoordinates 1 one_ne_zero).hasFDerivAt.comp (0 : V 4 × ℝ)
    (HasFDerivAt.prodMap (0 : V 4 × ℝ) (hasFDerivAt_univBall_zero r hr)
      (hasFDerivAt_id (0 : ℝ)))
  rw [southNormalCoordinates_radius_comp r hr.ne'] at h
  exact h

theorem southStabilizedTube_normal_formula (q : Sphere 3) (p : V 4 × ℝ) :
    southStabilizedTube (q, p) = (2 : ℝ) • southFiberAmbient q +
      southRadialFrame 1 q (southCompressedNormalCoordinates southChartTube.radius p) := by
  rw [southCompressedNormalCoordinates_apply]
  exact southStabilizedTube_formula q p.1 p.2

theorem hasFDerivAt_southStabilizedTube_normal (q : Sphere 3) :
    HasFDerivAt (fun p : V 4 × ℝ ↦ southStabilizedTube (q, p))
      ((southRadialFrame 1 q).comp
        (southNormalCoordinates southChartTube.radius
          southChartTube.radius_pos.ne').toContinuousLinearMap) 0 := by
  have he : (fun p : V 4 × ℝ ↦ southStabilizedTube (q, p)) =
      fun p ↦ (2 : ℝ) • southFiberAmbient q +
        southRadialFrame 1 q (southCompressedNormalCoordinates southChartTube.radius p) :=
    funext (southStabilizedTube_normal_formula q)
  rw [he]
  exact ((southRadialFrame 1 q).hasFDerivAt.comp 0
    (hasFDerivAt_southCompressedNormalCoordinates southChartTube.radius
      southChartTube.radius_pos)).const_add _

end NoExoticSixSphere.QuaternionicHopf
