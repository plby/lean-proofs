import ErdosProblems.Erdos67.MRGSA10TwoBlockAtypicalSmallPowerScale
import ErdosProblems.Erdos67.MRGSA10PrimeLambdaSourceCumulative

/-!
# The affine source row at the small-power A.10 cutoff

The final source schedule uses `y = 2^(K^2)` with
`K = floor ((log₂ X)^(1/1000))`.  The already-proved structural estimate
`log(X)^4 ≤ y` is enough to bound the affine row at height `log(X)^2` by
a constant depending only on the fixed beta-sieve constant.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- A fixed bound for the affine prime row at the small-power cutoff. -/
def gsA10SmallPowerSourceRowBound (Cbeta : ℝ) : ℝ :=
  Real.exp 1 * Real.sqrt Real.pi *
    (gsA10PrimeSourceAffineRowConstant Cbeta +
      72 * gsA10BetaSourceDensityConstant Cbeta +
      16 * (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cbeta : ℕ))

theorem gsA10SmallPowerSourceRowBound_nonneg
    {Cbeta : ℝ} (hCbeta : 1 ≤ Cbeta) :
    0 ≤ gsA10SmallPowerSourceRowBound Cbeta := by
  unfold gsA10SmallPowerSourceRowBound gsA10BetaSourceDensityConstant
  have hA := gsA10PrimeSourceAffineRowConstant_nonneg hCbeta
  positivity

/-- The affine row is uniformly bounded using only the structural
`log(X)^4 ≤ y` estimate. -/
theorem gsA10PrimeSourceAffineRow_smallPower_mul_log_sq_le
    {Cbeta : ℝ} (hCbeta : 1 ≤ Cbeta)
    {y X : ℕ} (hy : 0 < y)
    (hlog : Real.log 4 ≤ Real.log (X : ℝ))
    (hlogFour : Real.log (X : ℝ) ^ 4 ≤ (y : ℝ)) :
    Real.exp 1 * Real.sqrt Real.pi *
        (gsA10PrimeSourceAffineRowConstant Cbeta +
          gsA10PrimeSourceAffineRowSlope Cbeta y X *
            Real.log (X : ℝ) ^ 2) ≤
      gsA10SmallPowerSourceRowBound Cbeta := by
  let L : ℝ := Real.log (X : ℝ)
  have hLpos : 0 < L :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)).trans_le
      (by simpa only [L] using hlog)
  have hL0 : 0 ≤ L := hLpos.le
  have hlog4One : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hLone : (1 : ℝ) ≤ L :=
    hlog4One.trans (by simpa only [L] using hlog)
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hLfourOne : (1 : ℝ) ≤ L ^ 4 := by
    exact one_le_pow₀ hLone
  have hyOne : (1 : ℝ) ≤ y := hLfourOne.trans hlogFour
  have hLsq : L ^ 2 ≤ L ^ 4 := by
    nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hdiv : L ^ 2 / (y : ℝ) ≤ 1 := by
    apply (div_le_one hyR).2
    exact hLsq.trans hlogFour
  have hlogFourX : Real.log ((4 * X : ℕ) : ℝ) ≤ 2 * L := by
    have hXpos : 0 < X := by
      by_contra hX
      have hXzero : X = 0 := Nat.eq_zero_of_not_pos hX
      subst X
      simp [L] at hLpos
    have hlog4 : Real.log ((4 * X : ℕ) : ℝ) =
        Real.log 4 + L := by
      dsimp only [L]
      rw [show (((4 * X : ℕ) : ℝ)) = (4 : ℝ) * (X : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by exact_mod_cast hXpos.ne')]
    have hlog4le : Real.log 4 ≤ L := by simpa only [L] using hlog
    rw [hlog4]
    linarith
  have hyPow : (y : ℝ) ^ (-7 / 8 : ℝ) ≤ L ^ (-3 : ℝ) := by
    calc
      (y : ℝ) ^ (-7 / 8 : ℝ) ≤ (y : ℝ) ^ (-3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hyOne (by norm_num)
      _ ≤ (L ^ 4) ^ (-3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlogFour (by norm_num)
      _ = L ^ (-3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
        norm_num
  have htail : Real.log ((4 * X : ℕ) : ℝ) * L ^ 2 *
      (y : ℝ) ^ (-7 / 8 : ℝ) ≤ 2 := by
    calc
      Real.log ((4 * X : ℕ) : ℝ) * L ^ 2 *
          (y : ℝ) ^ (-7 / 8 : ℝ) ≤
        (2 * L) * L ^ 2 * L ^ (-3 : ℝ) := by
          gcongr
      _ = 2 := by
        have hneg : L ^ (-3 : ℝ) = (L ^ 3)⁻¹ := by
          rw [Real.rpow_neg hL0]
          norm_num
        rw [hneg]
        field_simp
  have hslope : gsA10PrimeSourceAffineRowSlope Cbeta y X * L ^ 2 ≤
      72 * gsA10BetaSourceDensityConstant Cbeta +
        16 * (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cbeta : ℕ) := by
    unfold gsA10PrimeSourceAffineRowSlope
    calc
      (72 * gsA10BetaSourceDensityConstant Cbeta / y +
          8 * (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cbeta : ℕ) *
            Real.log ((4 * X : ℕ) : ℝ) * (y : ℝ) ^ (-7 / 8 : ℝ)) *
          L ^ 2 =
        72 * gsA10BetaSourceDensityConstant Cbeta * (L ^ 2 / y) +
          8 * (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cbeta : ℕ) *
            (Real.log ((4 * X : ℕ) : ℝ) * L ^ 2 *
              (y : ℝ) ^ (-7 / 8 : ℝ)) := by ring
      _ ≤ 72 * gsA10BetaSourceDensityConstant Cbeta * 1 +
          8 * (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cbeta : ℕ) * 2 := by
        gcongr
        · unfold gsA10BetaSourceDensityConstant
          positivity
      _ = _ := by ring
  unfold gsA10SmallPowerSourceRowBound
  have hcoef : 0 ≤ Real.exp 1 * Real.sqrt Real.pi := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  dsimp only [L] at hslope
  linarith

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.gsA10PrimeSourceAffineRow_smallPower_mul_log_sq_le
