import Wikipedia.NoExoticSixSphere.QuaternionicBalancedFrameContraction
import Wikipedia.NoExoticSixSphere.SphereThreeTangentFrame

/-!
# The balanced rotation carries the actual reference normal and tangent columns

The reference point is the real unit quaternion in the original standard
three-sphere. The computed south-fiber normal frame and the original
left-quaternion tangent frame are transported by the same ambient operator.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionicHopf

open SphereThreeTangentFrame

def southFrameReference : Sphere 3 :=
  Wikipedia.HopfProblem.UnitQuaternionSphere.sphereHomeomorph 1

theorem southFrameReference_quaternion :
    Quaternion.linearIsometryEquivTuple.symm southFrameReference.val = 1 :=
  Quaternion.linearIsometryEquivTuple.symm_apply_apply 1

theorem balancedFrameContraction_normal (s : Sphere 3) (v : SouthNormalModel) :
    balancedFrameContraction (0, s) (southNormalFrame.ambient southFrameReference v) =
      southNormalFrame.ambient s v := by
  apply first_second_ext
  · rw [balancedFrameContraction_zero_first, southNormalFrame_first,
      southNormalFrame_first, southFrameReference_quaternion, mul_one, smul_mul_assoc]
  · rw [balancedFrameContraction_zero_second, southNormalFrame_second,
      southNormalFrame_second, southFrameReference_quaternion,
      mul_smul_comm, mul_smul_comm, mul_one]

theorem balancedFrameContraction_tangent (s : Sphere 3) (v : V 3) :
    balancedFrameContraction (0, s) (southAxis (operator southFrameReference.val v)) =
      southAxis (operator s.val v) := by
  apply first_second_ext
  · rw [balancedFrameContraction_zero_first, first_southAxis, first_southAxis, zero_mul]
  · rw [balancedFrameContraction_zero_second, second_southAxis, second_southAxis,
      operator_apply, operator_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, southFrameReference_quaternion, one_mul]

end NoExoticSixSphere.QuaternionicHopf
