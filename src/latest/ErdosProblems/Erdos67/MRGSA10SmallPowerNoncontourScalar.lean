import ErdosProblems.Erdos67.MRGSA10SourceScaleNoncontourScalar
import ErdosProblems.Erdos67.MRGSA10TwoBlockAtypicalSmallPowerScale

/-!
# Non-contour scalars at the small-power A.10 schedule
-/

open Filter

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The selected logarithmic width divided by the ambient logarithm is far
smaller than the final weak exponent. -/
theorem eventually_log_smallPowerBlockCutoff_div_log_le :
    ∀ᶠ Z : ℕ in atTop,
      Real.log
          (((2 ^ ((Erdos67.gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ)) /
          Real.log (Z : ℝ) ≤
        (2 * Real.log 2) *
          (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  filter_upwards
      [Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 1),
       eventually_ge_atTop 4] with Z hRone hZ
  let L : ℝ := Nat.log 2 Z
  let R : ℝ := Real.log (Z : ℝ)
  let K : ℕ := Erdos67.gsA10SmallPowerBlockExponent Z
  let y : ℕ := 2 ^ (K ^ 2)
  have hRpos : 0 < R := zero_lt_one.trans_le (by simpa only [R] using hRone)
  have hL0 : 0 ≤ L := by positivity
  have hLR : L ≤ 2 * R := by
    have hnat := Erdos67.DyadicGeometric.natLog_two_le_realLog_div
      (show 0 < Z by omega)
    have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmul : L * Real.log 2 ≤ R := by
      apply (le_div_iff₀ hlogTwoPos).mp
      simpa only [L, R] using hnat
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith
  have hpow : L ^ (1 / 500 : ℝ) ≤
      2 * R ^ (1 / 500 : ℝ) := by
    have hmono := Real.rpow_le_rpow hL0 hLR
      (by norm_num : (0 : ℝ) ≤ 1 / 500)
    have hmul : (2 * R) ^ (1 / 500 : ℝ) =
        2 ^ (1 / 500 : ℝ) * R ^ (1 / 500 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hRpos.le]
    have htwo : (2 : ℝ) ^ (1 / 500 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 500 : ℝ) ≤ 1)
    calc
      L ^ (1 / 500 : ℝ) ≤ (2 * R) ^ (1 / 500 : ℝ) := hmono
      _ = 2 ^ (1 / 500 : ℝ) * R ^ (1 / 500 : ℝ) := hmul
      _ ≤ 2 * R ^ (1 / 500 : ℝ) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hRpos.le _)
  have hlogy :=
    Erdos67.log_smallPowerBlockCutoff_le_natLog_rpow_one_five_hundredth Z
  have hratioRaw : Real.log (y : ℝ) / R ≤
      (2 * Real.log 2) * R ^ (1 / 500 - 1 : ℝ) := by
    have hnum : Real.log (y : ℝ) ≤
        (2 * Real.log 2) * R ^ (1 / 500 : ℝ) := by
      calc
        Real.log (y : ℝ) ≤ Real.log 2 * L ^ (1 / 500 : ℝ) := by
          simpa only [y, K, L] using hlogy
        _ ≤ Real.log 2 * (2 * R ^ (1 / 500 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (Real.log_pos (by norm_num)).le
        _ = (2 * Real.log 2) * R ^ (1 / 500 : ℝ) := by ring
    calc
      Real.log (y : ℝ) / R ≤
          ((2 * Real.log 2) * R ^ (1 / 500 : ℝ)) / R :=
        div_le_div_of_nonneg_right hnum hRpos.le
      _ = (2 * Real.log 2) * R ^ (1 / 500 - 1 : ℝ) := by
        rw [Real.rpow_sub_one hRpos.ne']
        ring
  have hweaken : R ^ (1 / 500 - 1 : ℝ) ≤
      R ^ (-(1 / 1000 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by simpa only [R] using hRone) (by norm_num)
  exact hratioRaw.trans (mul_le_mul_of_nonneg_left hweaken (by positivity))

/-- The reciprocal alpha-beta width is also stronger than the final weak
exponent. -/
theorem eventually_inv_log_smallPowerBlockCutoff_le_realLog_one_thousandth :
    ∀ᶠ Z : ℕ in atTop,
      (Real.log
          (((2 ^ ((Erdos67.gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ)))⁻¹ ≤
        (8 / Real.log 2) *
          (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  filter_upwards
      [Erdos67.eventually_inv_log_smallPowerBlockCutoff_le,
       Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 1),
       eventually_ge_atTop 4] with Z hinv hRone hZ
  let R : ℝ := Real.log (Z : ℝ)
  have hconvert := Erdos67.natLog_two_rpow_neg_le_two_mul_realLog hZ
    (show (0 : ℝ) ≤ 1 / 500 by norm_num)
    (show (1 / 500 : ℝ) ≤ 1 by norm_num)
  have hweaken : R ^ (-(1 / 500 : ℝ)) ≤
      R ^ (-(1 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by simpa only [R] using hRone)
      (by norm_num)
  calc
    (Real.log
        (((2 ^ ((Erdos67.gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ)))⁻¹ ≤
        (4 / Real.log 2) *
          (Nat.log 2 Z : ℝ) ^ (-(1 / 500 : ℝ)) := hinv
    _ ≤ (4 / Real.log 2) *
        (2 * (Real.log (Z : ℝ)) ^ (-(1 / 500 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hconvert (by positivity)
    _ ≤ (8 / Real.log 2) * R ^ (-(1 / 1000 : ℝ)) := by
      dsimp only [R]
      have hcoef : 0 ≤ (8 / Real.log 2 : ℝ) := by positivity
      calc
        (4 / Real.log 2) *
            (2 * Real.log (Z : ℝ) ^ (-(1 / 500 : ℝ))) =
            (8 / Real.log 2) * R ^ (-(1 / 500 : ℝ)) := by
          dsimp only [R]
          ring
        _ ≤ (8 / Real.log 2) * R ^ (-(1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left hweaken hcoef

/-- Fixed constant absorbing every ordinary-prefix term except the joint
moving contour and the atypical density. -/
def gsA10SmallPowerNoncontourConstant : ℝ :=
  (9 + gsA10GlobalSecondaryShiuConstant) * (2 * Real.log 2) +
    gsA10MovingPerronAveragedMassConstant * (8 / Real.log 2)

theorem gsA10SmallPowerNoncontourConstant_nonneg :
    0 ≤ gsA10SmallPowerNoncontourConstant := by
  unfold gsA10SmallPowerNoncontourConstant
  exact add_nonneg
    (mul_nonneg
      (add_nonneg (by norm_num) gsA10GlobalSecondaryShiuConstant_nonneg)
      (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le))
    (mul_nonneg gsA10MovingPerronAveragedMassConstant_nonneg (by positivity))

/-- Joint near projection, endpoint, averaged mass, and Shiu secondary at
the small-power schedule. -/
theorem eventually_jointSource_add_shiu_smallPowerBlock_le :
    ∀ᶠ Z : ℕ in atTop,
      let y := 2 ^ ((Erdos67.gsA10SmallPowerBlockExponent Z) ^ 2)
      gsA10JointMovingProjectionSourceBudget y Z +
          gsA10GlobalSecondaryShiuConstant *
            Real.log (y : ℝ) / Real.log (Z : ℝ) ≤
        gsA10SmallPowerNoncontourConstant *
          (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  filter_upwards
      [eventually_log_smallPowerBlockCutoff_div_log_le,
       eventually_inv_log_smallPowerBlockCutoff_le_realLog_one_thousandth,
       Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 1),
       eventually_ge_atTop 4] with Z hratio hinv hRone hZ
  dsimp only
  let y : ℕ := 2 ^ ((Erdos67.gsA10SmallPowerBlockExponent Z) ^ 2)
  let R : ℝ := Real.log (Z : ℝ)
  let d : ℝ := (Real.log (y : ℝ)) / R
  let e : ℝ := R ^ (-(1 / 1000 : ℝ))
  have hRpos : 0 < R := zero_lt_one.trans_le (by simpa only [R] using hRone)
  have hlogy0 : 0 ≤ Real.log (y : ℝ) := by
    exact Real.log_nonneg (by
      norm_cast
      exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
  have hd0 : 0 ≤ d := div_nonneg hlogy0 hRpos.le
  have hharmonic : (harmonic Z : ℝ) ≤ 2 * R := by
    calc
      (harmonic Z : ℝ) ≤ 1 + Real.log (Z : ℝ) := harmonic_le_one_add_log Z
      _ ≤ 2 * R := by dsimp only [R]; linarith
  have hfirst :
      4 * (harmonic Z : ℝ) * Real.log (y : ℝ) / R ^ 2 ≤ 8 * d := by
    rw [show 4 * (harmonic Z : ℝ) * Real.log (y : ℝ) / R ^ 2 =
      4 * ((harmonic Z : ℝ) / R) * d by
        dsimp only [d]
        field_simp]
    have hHR : (harmonic Z : ℝ) / R ≤ 2 :=
      (div_le_iff₀ hRpos).2 (by simpa only [mul_comm] using hharmonic)
    exact mul_le_mul_of_nonneg_right (by nlinarith) hd0
  have hRZ : R ≤ 2 * (Z : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Z)
    have hZ0 : (0 : ℝ) ≤ Z := by positivity
    linarith
  have hsecond : Real.log (y : ℝ) / (2 * (Z : ℝ)) ≤ d :=
    div_le_div_of_nonneg_left hlogy0 hRpos hRZ
  have hnear :
      4 * (harmonic Z : ℝ) * Real.log (y : ℝ) / R ^ 2 +
          Real.log (y : ℝ) / (2 * (Z : ℝ)) ≤ 9 * d := by
    linarith
  have hratio' : d ≤ (2 * Real.log 2) * e := by
    simpa only [d, e, R, y] using hratio
  have hinv' : (Real.log (y : ℝ))⁻¹ ≤ (8 / Real.log 2) * e := by
    simpa only [e, R, y] using hinv
  have hfinal :
      (4 * (harmonic Z : ℝ) * Real.log (y : ℝ) / R ^ 2 +
        Real.log (y : ℝ) / (2 * (Z : ℝ)) +
        gsA10MovingPerronAveragedMassConstant * (Real.log (y : ℝ))⁻¹) +
        gsA10GlobalSecondaryShiuConstant * d ≤
      gsA10SmallPowerNoncontourConstant * e := by
    calc
      _ ≤ 9 * d +
          gsA10MovingPerronAveragedMassConstant * (Real.log (y : ℝ))⁻¹ +
          gsA10GlobalSecondaryShiuConstant * d := by
        gcongr
      _ = (9 + gsA10GlobalSecondaryShiuConstant) * d +
          gsA10MovingPerronAveragedMassConstant * (Real.log (y : ℝ))⁻¹ := by ring
      _ ≤ (9 + gsA10GlobalSecondaryShiuConstant) *
          ((2 * Real.log 2) * e) +
        gsA10MovingPerronAveragedMassConstant * ((8 / Real.log 2) * e) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hratio'
            (add_nonneg (by norm_num) gsA10GlobalSecondaryShiuConstant_nonneg))
          (mul_le_mul_of_nonneg_left hinv'
            gsA10MovingPerronAveragedMassConstant_nonneg)
      _ = gsA10SmallPowerNoncontourConstant * e := by
        unfold gsA10SmallPowerNoncontourConstant
        ring
  unfold gsA10JointMovingProjectionSourceBudget
  convert hfinal using 1 <;> dsimp only [y, R, d, e] <;> ring

end


end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.eventually_jointSource_add_shiu_smallPowerBlock_le
