import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportExistence
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections

/-!
# The nonzero radial section and its actual local coefficients

The scalar is computed by the constructed connection along an actual finite
radial chart chain. Interpreting it in the scalar core's independently
defined fibre coordinates gives a genuine section, not a section supplied
as part of the input data.
-/

noncomputable section

open Set Bundle

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationGlobalTransport

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- The actual radial section in the scalar presentation's preferred fibre
coordinates. Its local smoothness is established separately. -/
def coreFrame (x : ComplexPlane₂) : A.core.Fiber x := globalRadialScalar A x

theorem coreFrame_ne_zero (x : ComplexPlane₂) : coreFrame A x ≠ 0 :=
  globalRadialScalar_ne_zero A x

/-- The section's coefficient in an original scalar-cocycle chart. -/
def frameCoefficient (i : ι) (x : ComplexPlane₂) : ℂ :=
  (A.transition (A.indexAt x) i x : ℂ) * globalRadialScalar A x

@[simp] theorem localCoefficient_coreFrame (i : ι) (x : ComplexPlane₂) :
    A.localCoefficient (coreFrame A) i x = frameCoefficient A i x := rfl

theorem frameCoefficient_ne_zero (i : ι) (x : ComplexPlane₂) :
    frameCoefficient A i x ≠ 0 :=
  mul_ne_zero (A.transition_ne_zero _ _ _) (globalRadialScalar_ne_zero A x)

/-- The constructed coefficients obey the original scalar transition law. -/
theorem frameCoefficient_compatible : A.IsCompatible (frameCoefficient A) :=
  A.localCoefficient_compatible (coreFrame A)

@[simp] theorem frameCoefficient_indexAt (x : ComplexPlane₂) :
    frameCoefficient A (A.indexAt x) x = globalRadialScalar A x := by
  rw [frameCoefficient, A.transition_self _ _ (A.mem_baseSet_at x)]
  exact one_mul _

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame
