import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCovariance
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsVerticalOne
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsHighDegrees
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsVanishing
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCompactVanishing

/-!
# Proposition 9.20: vanishing of genuine global holomorphic forms

The coefficients below are extracted from arbitrary native holomorphic
sections of the alternating cotangent bundles of the constructed threefold.
Their extensions, transformation laws and cusp orders have all been proved
from the actual fillings. Scalar vanishing therefore kills the original
forms, using the proved density of the regular cover. No coefficient,
extension, covariance, or cohomology hypothesis is imposed on a form.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms

open HolomorphicDifferentialForms TriangleHolomorphicDifferentials

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The second vertical coefficient vanishes by invariant scalar descent
and its actual first cusp order. -/
theorem extended_fibreOne_second_eq_zero
    (θ : Form RegularCover.Model Threefold.Space 1) :
    (fun z : ℍ => EllipticExtension.fibreOne θ z 1) = 0 :=
  invariant_scalar_eq_zero_of_hasCuspOrder_one
    ((ContinuousLinearMap.proj (1 : Fin 2) : ComplexPlane₂ →L[ℂ] ℂ).contMDiff.comp
      (EllipticExtension.fibreOne_holomorphic θ))
    (EllipticExtension.fibreOne_second_invariant θ)
    (EllipticExtension.fibreOne_hasCuspOrder θ 1)

/-- The period derivative kills the first vertical coefficient after the
second one vanishes, for every genuine global one-form. -/
theorem regular_fibreOne_eq_zero
    (θ : Form RegularCover.Model Threefold.Space 1) :
    RegularCover.fibreOne θ = 0 := by
  apply RegularCover.fibreOne_eq_zero_of_second θ
  intro z
  simpa only [EllipticExtension.fibreOne_restrict, Pi.zero_apply] using
    congrFun (extended_fibreOne_second_eq_zero θ) z.val

/-- Every genuine global holomorphic one-form on the constructed
threefold vanishes. -/
theorem oneForm_eq_zero (θ : Form RegularCover.Model Threefold.Space 1) : θ = 0 := by
  have hC := regular_fibreOne_eq_zero θ
  have hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0 :=
    fun z => congrFun hC z
  have hA := invariant_oneForm_eq_zero
    (EllipticExtension.baseOne_holomorphic θ hc)
    (EllipticExtension.baseOne_isInvariantDifferential θ hc)
    (EllipticExtension.baseOne_hasCuspOrder θ hc)
  apply (RegularCover.oneForm_eq_zero_iff_coefficients θ).mpr
  refine ⟨?_, hC⟩
  funext z
  simpa only [EllipticExtension.baseOne_restrict, Pi.zero_apply] using congrFun hA z.val

/-- The second mixed coefficient is an invariant one-differential with
the actual first cusp order. -/
theorem extended_mixedTwo_second_eq_zero
    (θ : Form RegularCover.Model Threefold.Space 2) :
    (fun z : ℍ => EllipticExtension.mixedTwo θ z 1) = 0 :=
  invariant_oneForm_eq_zero
    ((ContinuousLinearMap.proj (1 : Fin 2) : ComplexPlane₂ →L[ℂ] ℂ).contMDiff.comp
      (EllipticExtension.mixedTwo_holomorphic θ))
    (EllipticExtension.mixedTwo_second_isInvariantDifferential θ)
    (EllipticExtension.mixedTwo_hasCuspOrder θ 1)

/-- After the second mixed coefficient vanishes, the first has the
reciprocal-determinant weight and hence also vanishes. -/
theorem extended_mixedTwo_first_eq_zero
    (θ : Form RegularCover.Model Threefold.Space 2) :
    (fun z : ℍ => EllipticExtension.mixedTwo θ z 0) = 0 :=
  weight_oneForm_eq_zero
    ((ContinuousLinearMap.proj (0 : Fin 2) : ComplexPlane₂ →L[ℂ] ℂ).contMDiff.comp
      (EllipticExtension.mixedTwo_holomorphic θ))
    (EllipticExtension.mixedTwo_first_isWeightOneDifferential θ
      (extended_mixedTwo_second_eq_zero θ))
    (EllipticExtension.mixedTwo_hasCuspOrder θ 0)

/-- Every genuine global holomorphic two-form vanishes. -/
theorem twoForm_eq_zero (θ : Form RegularCover.Model Threefold.Space 2) : θ = 0 := by
  apply (RegularCover.twoForm_eq_zero_iff_coefficients θ).mpr
  funext z i
  fin_cases i
  · change RegularCover.mixedTwo θ z 0 = 0
    simpa only [EllipticExtension.mixedTwo_restrict, Pi.zero_apply] using
      congrFun (extended_mixedTwo_first_eq_zero θ) z.val
  · change RegularCover.mixedTwo θ z 1 = 0
    simpa only [EllipticExtension.mixedTwo_restrict, Pi.zero_apply] using
      congrFun (extended_mixedTwo_second_eq_zero θ) z.val

/-- Every genuine global holomorphic top form vanishes. -/
theorem threeForm_eq_zero (θ : Form RegularCover.Model Threefold.Space 3) : θ = 0 := by
  have hC := weight_oneForm_eq_zero (EllipticExtension.baseTop_holomorphic θ)
    (EllipticExtension.baseTop_isWeightOneDifferential θ)
    (EllipticExtension.baseTop_hasCuspOrder θ)
  apply (RegularCover.threeForm_eq_zero_iff_coefficients θ).mpr
  funext z
  simpa only [EllipticExtension.baseTop_restrict, Pi.zero_apply] using congrFun hC z.val

/-- Proposition 9.20 for all positive degrees, on the actual native
alternating cotangent bundles. -/
theorem form_eq_zero_of_pos {p : ℕ} (hp : 0 < p)
    (θ : Form RegularCover.Model Threefold.Space p) : θ = 0 := by
  by_cases hhigh : 3 < p
  · exact form_eq_zero_of_three_lt hhigh θ
  have hcases : p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact oneForm_eq_zero θ
  · exact twoForm_eq_zero θ
  · exact threeForm_eq_zero θ

theorem forms_subsingleton_of_pos {p : ℕ} (hp : 0 < p) :
    Subsingleton (Form RegularCover.Model Threefold.Space p) :=
  ⟨fun θ η => (form_eq_zero_of_pos hp θ).trans (form_eq_zero_of_pos hp η).symm⟩

/-- The dimension of the genuine space of global holomorphic p-forms is
zero for every positive p. -/
theorem forms_finrank_of_pos {p : ℕ} (hp : 0 < p) :
    Module.finrank ℂ (Form RegularCover.Model Threefold.Space p) = 0 := by
  let : Subsingleton (Form RegularCover.Model Threefold.Space p) :=
    forms_subsingleton_of_pos hp
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms
