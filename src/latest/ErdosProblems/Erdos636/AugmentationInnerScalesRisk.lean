/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.AugmentationInnerScales

/-!
# The final inner-exposure risk budget

This file converts the four explicit square-root-scale risks into the
coefficient inequality used by the final inner-exposure construction.  The
geometric summand is supplied by `ExposureGeometryBounds`; the collision,
candidate-degree, and switching summands are bounded here using the literal
floor denominators.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationInnerScales

noncomputable section

open AsymptoticThresholds

/-- The literal inner-exposure failure sum is at most `1/6` once its geometric
part costs at most `1/48` and the three remaining coefficient bounds cost at
most `7/48`. -/
lemma exposureRisk_le_one_sixth_of_coefficient_bounds
    {K nD nZ nS : ℕ}
    {a₀ deltaUpper cBalance innerTheta qGeom badGeomCoeff qDegree
      meanRadius energyCoeff qScale kappaCoeff badCollisionCoeff
      badDegreeCoeff : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀)
    (hnS : nS + 1 = nZ)
    (hnZ : (nZ : ℝ) ≤ deltaUpper * Real.sqrt nD)
    (hcBalance : 0 < cBalance) (hinnerTheta : 0 < innerTheta)
    (_hqGeom : 0 ≤ qGeom) (_hbadGeomCoeff : 0 < badGeomCoeff)
    (_hqDegree : 0 < qDegree) (_hmeanRadius : 0 ≤ meanRadius)
    (henergyCoeff : 0 < energyCoeff) (hqScale : 0 < qScale)
    (hkappaCoeff : 0 < kappaCoeff)
    (hbadCollisionCoeff : 0 < badCollisionCoeff)
    (hbadDegreeCoeff : 0 < badDegreeCoeff)
    (hgeometric :
      (nS + 1 : ℕ) *
          AugmentationGraphFull.graphDegreeRisk
            (AugmentationScales.geometricThreshold qGeom K nS nD)
            nD (K * nS) /
            (AugmentationScales.geometricBadBudget badGeomCoeff nD + 1 : ℕ) ≤
        1 / 48)
    (hcoeff :
      deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff / badCollisionCoeff +
        (a₀ / 4) *
            (2 * Real.exp (-(qDegree ^ 2 /
              (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff +
        deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
            qScale / kappaCoeff ≤ 7 / 48) :
    exposureRisk K nD nZ nS a₀ cBalance innerTheta qGeom badGeomCoeff
      qDegree meanRadius energyCoeff qScale kappaCoeff badCollisionCoeff
      badDegreeCoeff ≤ 1 / 6 := by
  unfold exposureRisk
  have hnZpos : 0 < nZ := by omega
  have hnDpos : 0 < nD := by
    by_contra h
    have hnDzero : nD = 0 := Nat.eq_zero_of_not_pos h
    subst nD
    have hnZreal : (0 : ℝ) < nZ := by exact_mod_cast hnZpos
    norm_num at hnZ
    linarith
  have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnDpos
  have hsqrtPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt hnDreal.le
  have hnSleZ : nS ≤ nZ := by omega
  have hnSUpper : (nS : ℝ) ≤ deltaUpper * Real.sqrt nD := by
    calc
      (nS : ℝ) ≤ (nZ : ℝ) := by exact_mod_cast hnSleZ
      _ ≤ deltaUpper * Real.sqrt nD := hnZ
  have hnZUpper : ((nS + 1 : ℕ) : ℝ) ≤
      deltaUpper * Real.sqrt nD := by simpa only [hnS] using hnZ
  have hdeltaUpper : 0 < deltaUpper := by
    have hnZreal : (0 : ℝ) < nZ := by exact_mod_cast hnZpos
    nlinarith
  have hs₀Upper : (partialMatchingSize a₀ nD : ℝ) ≤
      a₀ / 4 * Real.sqrt nD := by
    rw [partialMatchingSize]
    have hfloor := Nat.floor_le
      (show 0 ≤ a₀ * Real.sqrt nD / 4 by positivity)
    nlinarith
  have hs₀nonneg : (0 : ℝ) ≤ partialMatchingSize a₀ nD := by positivity
  have hs₀sq : (partialMatchingSize a₀ nD : ℝ) ^ 2 ≤
      a₀ ^ 2 / 16 * nD := by
    have hsquare := mul_self_le_mul_self hs₀nonneg hs₀Upper
    calc
      (partialMatchingSize a₀ nD : ℝ) ^ 2 ≤
          (a₀ / 4 * Real.sqrt nD) ^ 2 := by
            simpa only [pow_two] using hsquare
      _ = a₀ ^ 2 / 16 * nD := by rw [mul_pow, hsqrtSq]; ring
  have hchoose : ((partialMatchingSize a₀ nD).choose 2 : ℝ) ≤
      a₀ ^ 2 / 16 * nD := by
    have hchoose' : ((partialMatchingSize a₀ nD).choose 2 : ℝ) ≤
        (partialMatchingSize a₀ nD : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow (partialMatchingSize a₀ nD) 2
    exact hchoose'.trans hs₀sq
  have hvarPos : 0 < AntiConcentration.variancePointMassConstant cBalance
      (innerTheta ^ 2 / 4) K :=
    AntiConcentration.variancePointMassConstant_pos hcBalance (by positivity) hK
  have hsqrtLeTwo : Real.sqrt nD ≤ Real.sqrt (((2 * nD : ℕ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show nD ≤ 2 * nD by omega)
  have hcollisionFloor : badCollisionCoeff * Real.sqrt nD ≤
      ((collisionBadBudget badCollisionCoeff nD + 1 : ℕ) : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (badCollisionCoeff * Real.sqrt nD)
    simpa only [collisionBadBudget, Nat.cast_add, Nat.cast_one] using hfloor.le
  have hcollisionDenPos : (0 : ℝ) <
      (collisionBadBudget badCollisionCoeff nD + 1 : ℕ) := by positivity
  have hcollisionPre :
      ((nS + 1 : ℕ) : ℝ) *
            ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
            (AntiConcentration.variancePointMassConstant cBalance
                (innerTheta ^ 2 / 4) K /
              Real.sqrt (((2 * nD : ℕ) : ℝ))) /
            collisionThreshold energyCoeff nD ≤
        deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff * Real.sqrt nD := by
    have hsqrtInv :
        AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            Real.sqrt (((2 * nD : ℕ) : ℝ)) ≤
          AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K / Real.sqrt nD := by
      exact div_le_div_of_nonneg_left hvarPos.le hsqrtPos hsqrtLeTwo
    dsimp only [collisionThreshold]
    calc
      ((nS + 1 : ℕ) : ℝ) *
            ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
            (AntiConcentration.variancePointMassConstant cBalance
                (innerTheta ^ 2 / 4) K /
              Real.sqrt (((2 * nD : ℕ) : ℝ))) /
            (energyCoeff * Real.sqrt nD) ≤
          (deltaUpper * Real.sqrt nD) *
            (a₀ ^ 2 / 16 * nD) *
            (AntiConcentration.variancePointMassConstant cBalance
                (innerTheta ^ 2 / 4) K / Real.sqrt nD) /
            (energyCoeff * Real.sqrt nD) := by
              gcongr
      _ = deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff * Real.sqrt nD := by
              field_simp [hsqrtPos.ne', henergyCoeff.ne']
              nlinarith [hsqrtSq]
  have hcollisionTerm :
      (nS + 1 : ℕ) *
            (partialMatchingSize a₀ nD).choose 2 *
            (AntiConcentration.variancePointMassConstant cBalance
                (innerTheta ^ 2 / 4) K /
              Real.sqrt (((2 * nD : ℕ) : ℝ))) /
            collisionThreshold energyCoeff nD /
            (collisionBadBudget badCollisionCoeff nD + 1 : ℕ) ≤
        deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff / badCollisionCoeff := by
    rw [div_le_iff₀ hcollisionDenPos]
    calc
      ((nS + 1 : ℕ) : ℝ) *
            ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
            (AntiConcentration.variancePointMassConstant cBalance
                (innerTheta ^ 2 / 4) K /
              Real.sqrt (((2 * nD : ℕ) : ℝ))) /
            collisionThreshold energyCoeff nD ≤
          deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff * Real.sqrt nD := hcollisionPre
      _ = (deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff / badCollisionCoeff) *
              (badCollisionCoeff * Real.sqrt nD) := by field_simp
      _ ≤ (deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff / badCollisionCoeff) *
              (collisionBadBudget badCollisionCoeff nD + 1 : ℕ) := by
                gcongr
  have hdegreeEq := graphDegreeRisk_candidateDegreeThreshold
    (qDegree := qDegree) hK hnDpos
  have hdegreeFloor : badDegreeCoeff * Real.sqrt nD ≤
      ((degreeBadBudget badDegreeCoeff nD + 1 : ℕ) : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (badDegreeCoeff * Real.sqrt nD)
    simpa only [degreeBadBudget, Nat.cast_add, Nat.cast_one] using hfloor.le
  have hdegreeDenPos : (0 : ℝ) <
      (degreeBadBudget badDegreeCoeff nD + 1 : ℕ) := by positivity
  have hpDegreeNonneg :
      0 ≤ 2 * Real.exp (-(qDegree ^ 2 / (32 * (K : ℝ) ^ 2))) := by positivity
  have hdegreeTerm :
      partialMatchingSize a₀ nD *
            AugmentationGraphFull.graphDegreeRisk
              (candidateDegreeThreshold qDegree nD) nD K /
            (degreeBadBudget badDegreeCoeff nD + 1 : ℕ) ≤
        (a₀ / 4) *
            (2 * Real.exp (-(qDegree ^ 2 /
              (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff := by
    rw [hdegreeEq, div_le_iff₀ hdegreeDenPos]
    calc
      (partialMatchingSize a₀ nD : ℝ) *
            (2 * Real.exp (-(qDegree ^ 2 / (32 * (K : ℝ) ^ 2)))) ≤
          (a₀ / 4 * Real.sqrt nD) *
            (2 * Real.exp (-(qDegree ^ 2 / (32 * (K : ℝ) ^ 2)))) := by
              exact mul_le_mul_of_nonneg_right hs₀Upper hpDegreeNonneg
      _ = ((a₀ / 4) *
            (2 * Real.exp (-(qDegree ^ 2 /
              (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff) *
              (badDegreeCoeff * Real.sqrt nD) := by field_simp
      _ ≤ ((a₀ / 4) *
            (2 * Real.exp (-(qDegree ^ 2 /
              (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff) *
              (degreeBadBudget badDegreeCoeff nD + 1 : ℕ) := by
                gcongr
  have hsqrtVariance := sqrt_graphSwitchVariance
    (K := K) (meanRadius := meanRadius) hnDpos
  have hsqrtCoeffNonneg :
      0 ≤ Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) := Real.sqrt_nonneg _
  have hswitchTerm :
      (nS *
          (Real.sqrt
            (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
              qScale)) /
          switchingCutoff kappaCoeff nD ≤
        deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
            qScale / kappaCoeff := by
    rw [hsqrtVariance]
    dsimp only [switchingCutoff]
    calc
      ((nS : ℝ) *
          (Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) * Real.sqrt nD /
            qScale)) /
          (kappaCoeff * nD) ≤
        ((deltaUpper * Real.sqrt nD) *
          (Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) * Real.sqrt nD /
            qScale)) /
          (kappaCoeff * nD) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hnSUpper
                (div_nonneg
                  (mul_nonneg hsqrtCoeffNonneg hsqrtPos.le) hqScale.le))
              (mul_pos hkappaCoeff (by exact_mod_cast hnDpos)).le
      _ = deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
            qScale / kappaCoeff := by
              calc
                ((deltaUpper * Real.sqrt nD) *
                    (Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) *
                      Real.sqrt nD / qScale)) /
                    (kappaCoeff * nD) =
                    (deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
                      qScale / kappaCoeff) *
                      ((Real.sqrt nD) ^ 2 / (nD : ℝ)) := by ring
                _ = deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
                      qScale / kappaCoeff := by
                        rw [hsqrtSq]
                        field_simp
  linarith [hgeometric, hcollisionTerm, hdegreeTerm, hswitchTerm, hcoeff]

end

end AugmentationInnerScales
end Erdos636
