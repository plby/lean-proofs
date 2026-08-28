import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductSignAction

/-! # Four distinct inputs for every allowed midpoint scalar phase -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def negativePhase (u : unitary ℂ) : unitary ℂ :=
  ⟨-u.val, by
    constructor
    · simpa only [star_neg, neg_mul_neg] using u.property.1
    · simpa only [star_neg, neg_mul_neg] using u.property.2⟩

theorem negativePhase_cube (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    (negativePhase u).val ^ 3 = 1 := by
  change (-u.val) ^ 3 = 1
  rw [neg_pow, hu]
  norm_num

theorem rotationSphere_target_of_diagonal (z : UnitSphere) (u : ℂ)
    (hz : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ u * targetEigenvalues r)) :
    (symmetricMap (rotationSphere z)).val.val = u • targetMatrix targetAlpha targetBeta := by
  have hd : targetRotation * (u • targetMatrix targetAlpha targetBeta) * targetRotation =
      Matrix.diagonal (fun r ↦ u * targetEigenvalues r) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, targetRotation_targetMatrix]
    ext r s
    by_cases h : r = s
    · subst s
      simp [targetEigenvalues]
    · simp [h]
  rw [symmetricMap_rotationSphere, hz, ← hd]
  simp only [mul_assoc, ← mul_assoc targetRotation targetRotation,
    targetRotation_mul_self, one_mul, mul_one]

def phaseInput (u : unitary ℂ) (b : Bool × Bool) : UnitSphere :=
  rotationSphere (scalarSphere (negativePhase u) (signSphere b.1 b.2 MidpointSeed.rotatedInput))

theorem phaseInput_matrix (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    (symmetricMap (phaseInput u b)).val.val = u.val • targetMatrix targetAlpha targetBeta := by
  apply rotationSphere_target_of_diagonal
  rw [symmetricMap_scalarSphere (negativePhase u) (negativePhase_cube u hu),
    diagonal_signSphere b.1 b.2 MidpointSeed.rotatedInput _ MidpointSeed.symmetricMap_rotatedInput]
  ext r s
  by_cases h : r = s
  · subst s
    simp [negativePhase]
  · simp [h]

theorem phaseInput_injective (u : unitary ℂ) : Function.Injective (phaseInput u) :=
  rotationSphere_involutive.injective.comp ((scalarSphere_injective (negativePhase u)).comp
    (signSphere_choices_injective MidpointSeed.rotatedInput
      (MidpointSeed.rotatedInput_coordinate_ne_zero 0)
      (MidpointSeed.rotatedInput_coordinate_ne_zero 1)))

def fourInputs (u : unitary ℂ) (hu : u.val ^ 3 = -1) : Bool × Bool ↪ midpointFiber u where
  toFun b := ⟨phaseInput u b, phaseInput_matrix u hu b⟩
  inj' := fun _ _ h ↦ phaseInput_injective u (congrArg Subtype.val h)

theorem midpointFiber_card_eq_four (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    Nat.card (midpointFiber u) = 4 := by
  have hb := midpointFiber_finite_card_le_four u hu
  let : Finite (midpointFiber u) := hb.1
  apply Nat.le_antisymm hb.2
  have h := Nat.card_le_card_of_injective (fourInputs u hu) (fourInputs u hu).injective
  simpa using h

theorem midpointPhaseSet_ncard_eq_four (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    (midpointPhaseSet u).ncard = 4 := by
  rw [← Nat.card_coe_set_eq]
  exact midpointFiber_card_eq_four u hu

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
