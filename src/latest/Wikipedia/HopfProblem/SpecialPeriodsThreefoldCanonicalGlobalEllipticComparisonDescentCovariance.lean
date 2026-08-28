import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonUnit
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBaseCovariance

/-!
# Actual elliptic invariance of the comparison unit

The global modular generator has the determinant multiplier of the actual
elliptic fibre action.  It cancels the already proved base differential
and local canonical-section multipliers.  The extended ratio is therefore
invariant under the actual affine finite group, including its central fibre.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Triangle Elliptic EllipticFilling GlobalGenerator SectionsUnit

/-- The genuine global generator has the determinant multiplier of the
actual varying elliptic monodromy, not only its central linearization. -/
theorem discGenerator_rotation (j : Kind) (s : Disc) :
    discGenerator j (familyRotation j s) =
      (linearMatrix j ((specialLocalData j).periods.point s)).det * discGenerator j s := by
  simp only [discGenerator, neighborhoodLift_rotation]
  cases j
  · change generator (generatorOneSL • neighborhoodLift .three s) =
      ((specialLocalData .three).periods.point s).val.R₁.det *
        generator (neighborhoodLift .three s)
    rw [generator_generator₁, PeriodPoint.det_R₁]
    change -generator (neighborhoodLift .three s) / specialTau (neighborhoodLift .three s) =
      (-1 / specialTau (neighborhoodLift .three s)) * generator (neighborhoodLift .three s)
    ring
  · change generator (generatorTwoSL • neighborhoodLift .four s) =
      ((specialLocalData .four).periods.point s).val.R₂.det *
        generator (neighborhoodLift .four s)
    rw [generator_generator₂, PeriodPoint.det_R₂]
    change generator (neighborhoodLift .four s) / specialTau (neighborhoodLift .four s) =
      (1 / specialTau (neighborhoodLift .four s)) * generator (neighborhoodLift .four s)
    ring

/-- The denominator of the punctured comparison has exactly the same
inverse rotation multiplier as the actual finite-coordinate derivative. -/
theorem ratioDenominator_rotation (j : Kind) (s : Disc) :
    (discGenerator j (familyRotation j s) * specialCoefficient j (familyRotation j s)) *
        normalPhase j = discGenerator j s * specialCoefficient j s := by
  rw [discGenerator_rotation]
  calc
    _ = discGenerator j s * (specialCoefficient j (familyRotation j s) *
        (normalPhase j * (linearMatrix j ((specialLocalData j).periods.point s)).det)) := by
      ring
    _ = _ := congrArg (fun c : ℂ => discGenerator j s * c)
      (specialCoefficient_covariance j s)

/-- The actual comparison unit is invariant under the generator of the
elliptic action, with its already constructed central value unchanged. -/
theorem ratio_rotation (j : Kind) (s : Disc) :
    ratio j (familyRotation j s) = ratio j s := by
  by_cases hs : (s : ℂ) = 0
  · have he : s = discZero := Subtype.ext hs
    subst s
    exact congrArg (ratio j) (familyRotation_zero j)
  · have hrot : (familyRotation j s : ℂ) ≠ 0 := by
      rw [familyRotation_val]
      exact mul_ne_zero (normalPhase_ne_zero j) hs
    rw [ratio_of_ne_zero j _ hrot, ratio_of_ne_zero j s hs, puncturedRatio, puncturedRatio]
    calc
      _ = (baseDerivative j (familyRotation j s) * normalPhase j) /
          ((discGenerator j (familyRotation j s) *
            specialCoefficient j (familyRotation j s)) * normalPhase j) :=
        (mul_div_mul_right _ _ (normalPhase_ne_zero j)).symm
      _ = _ := by rw [baseDerivative_rotation, ratioDenominator_rotation]

theorem ratio_rotation_iterate (j : Kind) (n : ℕ) (s : Disc) :
    ratio j ((familyRotation j)^[n] s) = ratio j s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ratio_rotation, ih]

/-- The prescribed affine twist does not alter the base coordinate, so
the genuine finite action preserves the actual comparison coefficient. -/
theorem ratio_action (j : Kind) (g : CyclicGroup j) (x : (specialLocalData j).TotalSpace) :
    letI := (specialLocalData j).action j.twist (mainTwist_admissible j).1
    ratio j (g • x).1 = ratio j x.1 := by
  let := (specialLocalData j).action j.twist (mainTwist_admissible j).1
  rw [(specialLocalData j).action_apply]
  exact ratio_rotation_iterate j g.toAdd.val x.1

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
