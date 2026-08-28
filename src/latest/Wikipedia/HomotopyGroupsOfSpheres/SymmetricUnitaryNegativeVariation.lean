import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealExponential
import Wikipedia.HomotopyGroupsOfSpheres.OrthogonalTestFieldSandwich
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVariationDerivative

/-!
# The actual second energy derivative of the constrained variation

The energy uses the faithful real orthogonal representation. Its squared
metric is twice the complex matrix squared norm. The constrained matrix
variation equals the already verified rotating sine-field variation, so
the orthogonal second-variation theorem applies to this actual family.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open RealSymmetricMixing ImaginarySymmetricMatrices ComplexMatrixRealRepresentation
open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform

variable {N : Type*} [Fintype N] [DecidableEq N]

def energy (γ : ℝ → SpecialSpace N) : ℝ :=
  NoExoticSixSphere.OrthogonalPathEnergy.energy
    (fun t ↦ action (γ t).val.val.val) 0 1

theorem endpointVariation_real_family (A C : DirectionSpace N) (s t : ℝ) :
    specialOrthogonal (endpointVariation A C s t) =
      NoExoticSixSphere.OrthogonalExponentialVariation.family
        (fun r ↦ (1 : OrthogonalOperators (2 * Fintype.card N)) *
          NoExoticSixSphere.OrthogonalExponential.exp (r • skewMap A))
        (NoExoticSixSphere.OrthogonalIndexTestField.field (skewMap A) (skewMap C)) (s, t) := by
  rw [specialOrthogonal_endpointVariation, OrthogonalTestFieldSandwich.family_eq_sandwich]

theorem endpointVariation_energy_eq_testField (A C : DirectionSpace N) :
    (fun s ↦ energy (fun t ↦ endpointVariation A C s t)) =
      fun s ↦ NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t ↦ (NoExoticSixSphere.OrthogonalExponentialVariation.family
          (fun r ↦ (1 : OrthogonalOperators (2 * Fintype.card N)) *
            NoExoticSixSphere.OrthogonalExponential.exp (r • skewMap A))
          (NoExoticSixSphere.OrthogonalIndexTestField.field (skewMap A) (skewMap C))
          (s, t)).val.val) 0 1 := by
  funext s
  unfold energy
  congr 1
  funext t
  exact congrArg (fun B : OrthogonalOperators (2 * Fintype.card N) ↦ B.val.val)
    (endpointVariation_real_family A C s t)

theorem hasDerivAt_deriv_energy_endpointVariation (A C : DirectionSpace N) :
    HasDerivAt (deriv (fun s ↦ energy (fun t ↦ endpointVariation A C s t)))
      (2 * (Real.pi ^ 2 * squareNorm (imaginary C.val) -
        (1 / 4 : ℝ) * squareNorm (commutator (imaginary A.val) (imaginary C.val)))) 0 := by
  rw [endpointVariation_energy_eq_testField]
  have h := NoExoticSixSphere.OrthogonalIndexTestField.hasDerivAt_deriv_energy_testField
    (1 : OrthogonalOperators (2 * Fintype.card N)) (skewMap A) (skewMap C)
  apply h.congr_deriv
  change Real.pi ^ 2 * NoExoticSixSphere.HilbertSchmidt.squareNorm (action (imaginary C.val)) -
      (1 / 4 : ℝ) * NoExoticSixSphere.HilbertSchmidt.squareNorm
        (NoExoticSixSphere.OrthogonalCommutator.commutator
          (action (imaginary A.val)) (action (imaginary C.val))) = _
  rw [squareNorm_action, squareNorm_action_commutator]
  ring

theorem negative_secondDerivative_endpointVariation (A C : DirectionSpace N)
    (h : 4 * Real.pi ^ 2 * squareNorm (imaginary C.val) <
      squareNorm (commutator (imaginary A.val) (imaginary C.val))) :
    deriv (deriv (fun s ↦ energy (fun t ↦ endpointVariation A C s t))) 0 < 0 := by
  rw [(hasDerivAt_deriv_energy_endpointVariation A C).deriv]
  linarith

theorem negative_secondDerivative_of_real_commutator (A C : DirectionSpace N)
    (h : 4 * Real.pi ^ 2 * RealMatrixSquareNorm.squareNorm C.val <
      RealMatrixSquareNorm.squareNorm (RealMatrixSquareNorm.commutator A.val C.val)) :
    deriv (deriv (fun s ↦ energy (fun t ↦ endpointVariation A C s t))) 0 < 0 := by
  apply negative_secondDerivative_endpointVariation
  rw [squareNorm_imaginary, squareNorm_commutator_imaginary]
  exact h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
