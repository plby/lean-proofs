import Wikipedia.HopfProblem.CuspExponentials
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local holomorphic charts for the normalized exponential

The coordinatewise normalized exponential is a local analytic diffeomorphism.
Its derivative is a diagonal continuous linear equivalence at every point.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

def exponentialPair (z : ComplexPlane₂) : ComplexPlane₂ := fun i => exponential (z i)

theorem exponentialPair_holomorphic : ContDiff ℂ ω exponentialPair := by
  apply contDiff_pi.mpr
  intro i
  exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ i)

theorem exponential_hasDerivAt (z : ℂ) :
    HasDerivAt exponential (exponential z * (2 * Real.pi * Complex.I)) z := by
  change HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * w))
    (Complex.exp (2 * Real.pi * Complex.I * z) * (2 * Real.pi * Complex.I)) z
  convert!
    ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).cexp
    using 1
  simp

def exponentialPairDerivative (z : ComplexPlane₂) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  ContinuousLinearEquiv.piCongrRight fun i => ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (exponential (z i) * (2 * Real.pi * Complex.I))
      (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))

theorem exponentialPair_hasFDerivAt (z : ComplexPlane₂) :
    HasFDerivAt exponentialPair (exponentialPairDerivative z : ComplexPlane₂ →L[ℂ] ComplexPlane₂)
      z := by
  apply hasFDerivAt_pi''
  intro i
  convert! ((exponential_hasDerivAt (z i)).hasFDerivAt_equiv
    (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero)).comp z
    (hasFDerivAt_apply (𝕜 := ℂ) i z) using 1

def exponentialChart (z : ComplexPlane₂) : OpenPartialHomeomorph ComplexPlane₂ ComplexPlane₂ :=
  exponentialPair_holomorphic.contDiffAt.toOpenPartialHomeomorph exponentialPair
    (exponentialPair_hasFDerivAt z) (by simp)

@[simp] theorem exponentialChart_apply (z w : ComplexPlane₂) :
    exponentialChart z w = exponentialPair w := rfl

@[simp] theorem exponentialChart_coe (z : ComplexPlane₂) :
    (exponentialChart z : ComplexPlane₂ → ComplexPlane₂) = exponentialPair := rfl

theorem mem_exponentialChart_source (z : ComplexPlane₂) :
    z ∈ (exponentialChart z).source :=
  exponentialPair_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    (exponentialPair_hasFDerivAt z) (by simp)

theorem exponentialChart_holomorphic (z : ComplexPlane₂) :
    ContDiffOn ℂ ω (exponentialChart z) (exponentialChart z).source :=
  exponentialPair_holomorphic.contDiffOn

theorem exponentialChart_symm_holomorphic (z : ComplexPlane₂) :
    ContDiffOn ℂ ω (exponentialChart z).symm (exponentialChart z).target := by
  intro w hw
  exact ((exponentialChart z).contDiffAt_symm hw
    (exponentialPair_hasFDerivAt ((exponentialChart z).symm w))
    exponentialPair_holomorphic.contDiffAt).contDiffWithinAt

theorem exponentialChart_mem_maximalAtlas (z : ComplexPlane₂) :
    exponentialChart z ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ ComplexPlane₂) ω ComplexPlane₂ :=
  (exponentialChart z).mem_maximalAtlas_of_contMDiffOn
    (exponentialChart_holomorphic z).contMDiffOn
    (exponentialChart_symm_holomorphic z).contMDiffOn

end Wikipedia.HopfProblem.CuspUniformization
