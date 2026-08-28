import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteFrameLift
import Wikipedia.NoExoticSixSphere.QuaternionicBalancedFrameContraction

/-!
# The balanced quaternionic contraction transports the exact lifted columns

The lifted finite normal columns have their original radial half-scale and
fixed target basis. The same balanced ambient operator carries these normal
columns and the original global tangent columns from the real quaternion
reference point to every sphere point. Its contraction remains injective.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteBalancedFrame

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfFiniteFrame
open QuaternionicHopfFiniteFrameLift

def reference : Sphere 3 := UnitQuaternionSphere.sphereHomeomorph 1

theorem reference_quaternion : Quaternion.linearIsometryEquivTuple.symm reference.val = 1 :=
  Quaternion.linearIsometryEquivTuple.symm_apply_apply 1

def normal (q : Sphere 3) : WithLp 2 (ℝ × V 4) →L[ℝ] V 8 :=
  SphereFiniteEquationLift.lift (finitePoint q) (rightInverse q)

theorem normal_apply (q : Sphere 3) (z : WithLp 2 (ℝ × V 4)) :
    normal q z = ((1 / 2 : ℝ) * z.fst) • QuaternionicHopfSouthPolynomialFrame.inclusion q +
      (1 / 2 : ℝ) • QuaternionicHopfSouthNormal.frame q
        (QuaternionicHopfSouthSphereFrame.targetTailEquiv z.snd) := by
  rw [normal, SphereFiniteRadialCoordinates.lift_eq_coordinates, lifted_normal_coordinates]

theorem normal_first (q : Sphere 3) (z : WithLp 2 (ℝ × V 4)) :
    first (normal q z) = (1 / 2 : ℝ) •
      (Quaternion.linearIsometryEquivTuple.symm
        (QuaternionicHopfSouthSphereFrame.targetTailEquiv z.snd) *
          Quaternion.linearIsometryEquivTuple.symm q.val) := by
  rw [normal_apply, map_add, map_smul, map_smul, QuaternionicHopfSouthNormal.first_frame]
  change ((1 / 2 : ℝ) * z.fst) • first (QuaternionicHopfSouthFiber.fiberPoint q).val + _ = _
  rw [QuaternionicHopfSouthFiber.first_fiberPoint, smul_zero, zero_add]

theorem normal_second (q : Sphere 3) (z : WithLp 2 (ℝ × V 4)) :
    second (normal q z) = ((1 / 2 : ℝ) * z.fst) •
      Quaternion.linearIsometryEquivTuple.symm q.val := by
  rw [normal_apply, map_add, map_smul, map_smul, QuaternionicHopfSouthNormal.second_frame]
  change ((1 / 2 : ℝ) * z.fst) • second (QuaternionicHopfSouthFiber.fiberPoint q).val + _ = _
  rw [QuaternionicHopfSouthFiber.second_fiberPoint, smul_zero, add_zero]

theorem balanced_normal (q : Sphere 3) (z : WithLp 2 (ℝ × V 4)) :
    balancedFrameContraction (0, q) (normal reference z) = normal q z := by
  apply first_second_ext
  · rw [balancedFrameContraction_zero_first, normal_first, normal_first,
      reference_quaternion, mul_one, smul_mul_assoc]
  · rw [balancedFrameContraction_zero_second, normal_second, normal_second,
      reference_quaternion, mul_smul_comm, mul_one]

theorem balanced_tangent (q : Sphere 3) (v : V 3) :
    balancedFrameContraction (0, q)
      (QuaternionicHopfSouthFiber.axis (SphereThreeTangentFrame.operator reference.val v)) =
        QuaternionicHopfSouthFiber.axis (SphereThreeTangentFrame.operator q.val v) := by
  apply first_second_ext
  · rw [balancedFrameContraction_zero_first, QuaternionicHopfSouthFiber.first_axis,
      QuaternionicHopfSouthFiber.first_axis, zero_mul]
  · rw [balancedFrameContraction_zero_second, QuaternionicHopfSouthFiber.second_axis,
      QuaternionicHopfSouthFiber.second_axis, SphereThreeTangentFrame.operator_apply,
      SphereThreeTangentFrame.operator_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, reference_quaternion, one_mul]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteBalancedFrame
