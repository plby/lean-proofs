import Wikipedia.HopfProblem.DegreeCollapseSphereCenteredEquationDerivative
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSouthPolynomialFrame

/-!
# The explicit induced frame of the actual Hopf sphere fiber

The full original sphere-level equation derivative is the polynomial
derivative followed by the fixed radial/tangent target equivalence.
Its canonical frame has positive radial half-scale and the quaternionic
columns in the actual chosen target-chart basis. No basis is replaced
by the identity and no framing class is assigned by definition.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthSphereFrame

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfSouthPolynomialFrame
open SphereCenteredAmbientChart hiding V
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

theorem inner_inclusion (q : Sphere 3) (v : V 8) :
    inner ℝ (inclusion q) v =
      inner ℝ (Quaternion.linearIsometryEquivTuple.symm q.val) (second v) := by
  have h := planeCoordinates.symm.inner_map_map (inclusion q) v
  rw [WithLp.prod_inner_apply] at h
  change inner ℝ (first (inclusion q)) (first v) +
    inner ℝ (second (inclusion q)) (second v) = inner ℝ (inclusion q) v at h
  have hfirst : first (inclusion q) = 0 := QuaternionicHopfSouthFiber.first_fiberPoint q
  have hsecond : second (inclusion q) = Quaternion.linearIsometryEquivTuple.symm q.val :=
    QuaternionicHopfSouthFiber.second_fiberPoint q
  rw [hfirst, hsecond, inner_zero_left, zero_add] at h
  exact h.symm

theorem norm_compatibility (q : Sphere 3) (v : V 8) :
    2 * inner ℝ (inclusion q) v =
      inner ℝ QuaternionicHopfSouthFiber.point.val (fderiv ℝ polynomial (inclusion q) v) := by
  rw [inner_inclusion, QuaternionicHopfSouthRegularity.point_inner_head,
    polynomial_fderiv_south, SphereCylinder.join_head]
  ring

theorem polynomial_radial (q : Sphere 3) :
    fderiv ℝ polynomial (inclusion q) (inclusion q) =
      (2 : ℝ) • QuaternionicHopfSouthFiber.point.val := by
  rw [polynomial_derivative_radial, ← QuaternionicHopfSouthFiber.point_join, ← map_smul]
  apply congrArg (SphereCylinder.join 3)
  apply Prod.ext <;> norm_num

theorem radial_compatibility (q : Sphere 3) :
    linearPart QuaternionicHopfSouthFiber.point
      (fderiv ℝ polynomial (inclusion q) (inclusion q)) = 0 := by
  rw [polynomial_radial, map_smul, linearPart_radial, smul_zero]

def targetEquiv : V 5 ≃L[ℝ] WithLp 2 (ℝ × V 4) :=
  coordinateEquiv QuaternionicHopfSouthFiber.point

theorem equations_derivative (a : Sphere 7) (q : Sphere 3) :
    fderiv ℝ (SphereFiberNormalFrame.equations sphereMap QuaternionicHopfSouthFiber.point a)
      (inclusion q) = targetEquiv.toContinuousLinearMap.comp
        (fderiv ℝ polynomial (inclusion q)) :=
  SphereCenteredEquationDerivative.fderiv_equations_eq_split_comp sphereMap polynomial
    sphereMap_val QuaternionicHopfSouthFiber.point a (QuaternionicHopfSouthFiber.fiberPoint q)
    (QuaternionicHopfSouthFiber.sphereMap_fiberPoint q)
    (contDiff_polynomial.differentiable (by simp) _) (norm_compatibility q) (radial_compatibility q)

def sphereRightInverse (q : Sphere 3) : WithLp 2 (ℝ × V 4) →L[ℝ] V 8 :=
  (rightInverse q).comp targetEquiv.symm.toContinuousLinearMap

theorem canonical_equations (a : Sphere 7) (q : Sphere 3) :
    orthogonalRightInverse (fderiv ℝ
      (SphereFiberNormalFrame.equations sphereMap QuaternionicHopfSouthFiber.point a)
      (inclusion q)) = sphereRightInverse q := by
  rw [equations_derivative]
  have h := SphereCenteredEquationDerivative.canonical_postcompose QuaternionicHopfSouthFiber.point
    (fderiv ℝ polynomial (inclusion q)) (polynomial_fderiv_surjective q)
  rw [canonical_rightInverse q] at h
  exact h

theorem contMDiff_sphereRightInverse :
    ContMDiff (𝓡 3) 𝓘(ℝ, WithLp 2 (ℝ × V 4) →L[ℝ] V 8) ∞ sphereRightInverse :=
  contMDiff_rightInverse.clm_comp contMDiff_const

def targetTail : V 4 →L[ℝ] V 4 :=
  (SphereCylinder.tail 3).comp (tangentLift QuaternionicHopfSouthFiber.point)

theorem tangentLift_head (w : V 4) :
    tangentLift QuaternionicHopfSouthFiber.point w 0 = 0 := by
  have h := tangentLift_inner QuaternionicHopfSouthFiber.point w
  rw [QuaternionicHopfSouthRegularity.point_inner_head] at h
  exact neg_eq_zero.mp h

theorem tangentLift_eq_join (w : V 4) :
    tangentLift QuaternionicHopfSouthFiber.point w = SphereCylinder.join 3 (0, targetTail w) :=
  (QuaternionicHopf.join_zero_tail _ (tangentLift_head w)).symm

theorem targetEquiv_symm_join (p : WithLp 2 (ℝ × V 4)) :
    targetEquiv.symm p = SphereCylinder.join 3 (-p.fst, targetTail p.snd) := by
  rw [targetEquiv, coordinateEquiv_symm_apply, tangentLift_eq_join,
    ← QuaternionicHopfSouthFiber.point_join, ← map_smul, ← map_add]
  apply congrArg (SphereCylinder.join 3)
  apply Prod.ext <;> simp

theorem sphereRightInverse_apply (q : Sphere 3) (p : WithLp 2 (ℝ × V 4)) :
    sphereRightInverse q p = (1 / 2 : ℝ) • (p.fst • inclusion q) +
      (1 / 2 : ℝ) • QuaternionicHopfSouthNormal.frame q (targetTail p.snd) := by
  change rightInverse q (targetEquiv.symm p) = _
  rw [targetEquiv_symm_join]
  change rawRightInverse q ((SphereCylinder.join 3).symm
    (SphereCylinder.join 3 (-p.fst, targetTail p.snd))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, rawRightInverse_apply]
  congr 1
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem sphereFrame_formula (a : Sphere 7) (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap QuaternionicHopfSouthFiber.point
      QuaternionicHopfSouthRegularity.south_regular 3 (by simp);
    (SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap
      QuaternionicHopfSouthFiber.point
      QuaternionicHopfSouthRegularity.south_regular 3 (by decide) a).ambient
        (QuaternionicHopfSouthRegularity.fiberDiffeomorph q) = sphereRightInverse q := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap QuaternionicHopfSouthFiber.point
    QuaternionicHopfSouthRegularity.south_regular 3 (by simp)
  rw [SphereFiberNormalFrame.normalFrame_ambient]
  exact canonical_equations a q


theorem targetTail_norm (w : V 4) : ‖targetTail w‖ = ‖w‖ := by
  have hL : ‖tangentLift QuaternionicHopfSouthFiber.point w‖ = ‖w‖ :=
    (coordinates QuaternionicHopfSouthFiber.point).symm.norm_map w
  have h := SphereCylinder.norm_join_sq 3 0 (targetTail w)
  rw [← tangentLift_eq_join, hL] at h
  nlinarith [norm_nonneg (targetTail w), norm_nonneg w]

def targetTailIsometry : V 4 →ₗᵢ[ℝ] V 4 where
  toLinearMap := targetTail.toLinearMap
  norm_map' := targetTail_norm

def targetTailEquiv : V 4 ≃ₗᵢ[ℝ] V 4 :=
  LinearIsometryEquiv.ofSurjective targetTailIsometry
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := targetTailIsometry.toLinearMap) rfl).mp targetTailIsometry.injective)

theorem targetTailEquiv_apply (w : V 4) : targetTailEquiv w = targetTail w := rfl

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthSphereFrame
