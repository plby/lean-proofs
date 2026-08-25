import ErdosProblems.Erdos67.MRGSA10LambdaWindowMassOrdinary
import ErdosProblems.Erdos67.DyadicGeometric

/-!
# Logarithmic scalar for the ordinary A.10 window mass

The ordinary-multiplicative Mangoldt window has a prime contribution of
order `Nat.log 2 X` and an explicit higher-prime-power contribution.  Once
the source cutoff satisfies `log(X)^4 <= y`, the latter is smaller than one
logarithmic unit, so the whole mass is `O(log X)`.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Universal coefficient in the logarithmic A.10 window-mass bound. -/
def gsA10OrdinaryLambdaWindowMassLogConstant : ℝ :=
  2 * (Real.log 4 + 4) / Real.log 2 + 12

theorem gsA10OrdinaryLambdaWindowMassLogConstant_nonneg :
    0 ≤ gsA10OrdinaryLambdaWindowMassLogConstant := by
  unfold gsA10OrdinaryLambdaWindowMassLogConstant
  positivity

/-- The ordinary Mangoldt-window mass is at most a fixed multiple of
`log X` under the source fourth-power cutoff. -/
theorem gsA10OrdinaryLambdaWindowMassBase_le_log
    {y X : ℕ} (hX : 0 < X)
    (hy3 : 3 ≤ y)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hmass : Erdos67.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hy : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ)) :
    gsA10OrdinaryLambdaWindowMassBase y X ≤
      gsA10OrdinaryLambdaWindowMassLogConstant *
        Real.log (X : ℝ) := by
  let L : ℝ := Real.log (X : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlogX
  have hhppBase := gsA10HigherPrimePowerGeometricMass_le (X := X) hy3
  have hcoef : 0 ≤ 12 * L / (y : ℝ) := by positivity
  have hhppMass : gsA10HigherPrimePowerGeometricMass y X ≤
      12 * L / (y : ℝ) * L := by
    exact hhppBase.trans (mul_le_mul_of_nonneg_left hmass hcoef)
  have hLfour : 0 < L ^ 4 := pow_pos hL _
  have hnum : 0 ≤ 12 * L ^ 2 := by positivity
  have hden : (12 * L ^ 2) / (y : ℝ) ≤
      (12 * L ^ 2) / L ^ 4 :=
    div_le_div_of_nonneg_left hnum hLfour hy
  have hhpp : gsA10HigherPrimePowerGeometricMass y X ≤ 12 * L := by
    calc
      gsA10HigherPrimePowerGeometricMass y X ≤
          12 * L / (y : ℝ) * L := hhppMass
      _ = (12 * L ^ 2) / (y : ℝ) := by ring
      _ ≤ (12 * L ^ 2) / L ^ 4 := hden
      _ = 12 / L ^ 2 := by field_simp
      _ ≤ 12 * L := by
        have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hlogX
        have hLinvsq : 1 / L ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hLsq
        calc
          12 / L ^ 2 = 12 * (1 / L ^ 2) := by ring
          _ ≤ 12 * 1 := mul_le_mul_of_nonneg_left hLinvsq (by norm_num)
          _ ≤ 12 * L := by nlinarith
  have hnatLog := Erdos67.DyadicGeometric.natLog_two_le_realLog_div hX
  unfold gsA10OrdinaryLambdaWindowMassBase
  calc
    2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ) +
        gsA10HigherPrimePowerGeometricMass y X ≤
      2 * (Real.log 4 + 4) * (L / Real.log 2) + 12 * L := by
        gcongr
    _ = gsA10OrdinaryLambdaWindowMassLogConstant * L := by
      unfold gsA10OrdinaryLambdaWindowMassLogConstant L
      ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsA10OrdinaryLambdaWindowMassBase_le_log
