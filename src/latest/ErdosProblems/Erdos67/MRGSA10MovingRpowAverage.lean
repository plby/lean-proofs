import ErdosProblems.Erdos67.MRGSA10MovingRpowRestoredPerron
import ErdosProblems.Erdos67.MRGSA10PerronRpowAverage

/-!
# Averaging the exact moving Perron power

The left prime-window energy contributes `(X / y)^(2 beta)` after taking
its square root.  Keeping the exact Perron power cancels this beta growth
before integration; the alpha integral then contributes `X / log X`.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The moving kernel together with the square-root growth of the left
prime-window energy. -/
def gsA10MovingRpowPrimeFactor
    (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  gsA10MovingPerronKernelScale X alpha beta *
    (((X / y : ℕ) : ℝ) ^ (2 * beta))

theorem continuous_gsA10MovingRpowPrimeFactor
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) :
    Continuous (Function.uncurry (gsA10MovingRpowPrimeFactor y X)) := by
  have hX : 0 < X := hy.trans_le hyX
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hdiv : X / y ≠ 0 := Nat.ne_of_gt (Nat.div_pos hyX hy)
  unfold gsA10MovingRpowPrimeFactor gsA10MovingPerronKernelScale
  exact (continuous_const.mul
    ((Real.continuous_const_rpow hXR).comp
      (by fun_prop))).mul
        ((Real.continuous_const_rpow (by exact_mod_cast hdiv)).comp
          (by fun_prop))

theorem gsA10MovingRpowPrimeFactor_nonneg
    (y X : ℕ) (alpha beta : ℝ) :
    0 ≤ gsA10MovingRpowPrimeFactor y X alpha beta := by
  unfold gsA10MovingRpowPrimeFactor
  exact mul_nonneg (gsA10MovingPerronKernelScale_nonneg X alpha beta)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Pointwise beta cancellation against the left prime-window energy. -/
theorem gsA10MovingRpowPrimeFactor_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 1 < X)
    {alpha beta : ℝ} (hbeta : 0 ≤ beta) :
    gsA10MovingRpowPrimeFactor y X alpha beta ≤
      2 * Real.exp 1 * (X : ℝ) ^ (1 - alpha) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hdivNat : 0 < X / y := Nat.div_pos hyX hy
  have hdiv0 : (0 : ℝ) < ((X / y : ℕ) : ℝ) := by
    exact_mod_cast hdivNat
  have hdivX : ((X / y : ℕ) : ℝ) ≤ X := by
    exact_mod_cast Nat.div_le_self X y
  have hratio : ((X / y : ℕ) : ℝ) ^ (2 * beta) ≤
      (X : ℝ) ^ (2 * beta) :=
    Real.rpow_le_rpow hdiv0.le hdivX (by positivity)
  have hpowInv :
      (X : ℝ) ^ (Real.log (X : ℝ))⁻¹ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hXR]
    congr 1
    exact mul_inv_cancel₀
      (Real.log_pos (by exact_mod_cast hX)).ne'
  unfold gsA10MovingRpowPrimeFactor gsA10MovingPerronKernelScale
  calc
    2 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
        ((X / y : ℕ) : ℝ) ^ (2 * beta) ≤
        2 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
            (X : ℝ) ^ (2 * beta) := by
      gcongr
    _ = 2 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha) := by
      have hcombine :
          (X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^ (2 * beta) =
            (X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha) := by
        rw [← Real.rpow_add hXR]
        congr 1
        ring
      calc
        2 * (X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
            (X : ℝ) ^ (2 * beta) =
            2 * ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^ (2 * beta)) := by ring
        _ = 2 * (X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha) := by
          rw [hcombine]
    _ = 2 * Real.exp 1 * (X : ℝ) ^ (1 - alpha) := by
      unfold Erdos67.EulerResidue.taoExponent
      rw [show 1 + (Real.log (X : ℝ))⁻¹ - alpha =
        (1 - alpha) + (Real.log (X : ℝ))⁻¹ by ring,
        Real.rpow_add hXR, hpowInv]
      ring

/-- The kernel without the left-energy factor is no larger than the paired
factor, since `X / y ≥ 1` on the source range. -/
theorem gsA10MovingPerronKernelScale_le_primeFactor
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X)
    {alpha beta : ℝ} (hbeta : 0 ≤ beta) :
    gsA10MovingPerronKernelScale X alpha beta ≤
      gsA10MovingRpowPrimeFactor y X alpha beta := by
  have hdiv : 1 ≤ X / y := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.div_pos hyX hy))
  have hpow : (1 : ℝ) ≤ ((X / y : ℕ) : ℝ) ^ (2 * beta) := by
    exact Real.one_le_rpow (by exact_mod_cast hdiv)
      (by positivity : 0 ≤ 2 * beta)
  unfold gsA10MovingRpowPrimeFactor
  nth_rewrite 1 [← mul_one (gsA10MovingPerronKernelScale X alpha beta)]
  exact mul_le_mul_of_nonneg_left hpow
    (gsA10MovingPerronKernelScale_nonneg X alpha beta)

/-- After taking the two square roots in vertical Cauchy, the entire
left-line shift is the single factor `(X / y)^(2 beta)`.  This exact
identity is the algebraic input for the moving-power cancellation. -/
theorem gsA10PrimeLambda_energyPair_eq_ratio_mul_right
    {Cβ : ℝ} {Q S X y : ℕ} {beta T : ℝ}
    (hCβ : 1 ≤ Cβ) (hX : 2 ≤ X) (hT : 0 < T) :
    (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * beta) T) ^
          ((1 : ℝ) / 2) *
        (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
          ((1 : ℝ) / 2) =
      (((X / y : ℕ) : ℝ) ^ (2 * beta)) *
        gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T := by
  let R : ℝ := gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T
  let q : ℝ := ((X / y : ℕ) : ℝ)
  have hrow : 0 ≤ gsA10PrimeGaussianRowBound Cβ Q S y X T :=
    gsA10PrimeGaussianRowBound_nonneg hCβ hX hT
  have hbudget : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have hR : 0 ≤ R := by
    dsimp only [R, gsA10PrimeLambdaRightEnergyBound]
    positivity
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hleft :
      gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * beta) T =
        q ^ (4 * beta) * R := by
    dsimp only [q, R, gsA10PrimeLambdaLeftEnergyBound,
      gsA10PrimeLambdaRightEnergyBound]
    ring_nf
  have hqhalf :
      (q ^ (4 * beta)) ^ ((1 : ℝ) / 2) = q ^ (2 * beta) := by
    rw [← Real.rpow_mul hq]
    congr 1
    ring
  rw [hleft, Real.mul_rpow (Real.rpow_nonneg hq _) hR, hqhalf]
  calc
    q ^ (2 * beta) * R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) =
        q ^ (2 * beta) *
          (R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2)) := by ring
    _ = q ^ (2 * beta) * R := by
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hR]
    _ = (((X / y : ℕ) : ℝ) ^ (2 * beta)) *
        gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T := by
      rfl

/-- Rectangle average after exact beta cancellation. -/
theorem doubleIntervalIntegral_gsA10MovingRpowPrimeFactor_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 1 < X)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10MovingRpowPrimeFactor y X alpha beta) ≤
      2 * Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  let F := gsA10MovingRpowPrimeFactor y X
  let G : ℝ → ℝ := fun alpha ↦
    2 * Real.exp 1 * (X : ℝ) ^ (1 - alpha)
  have hF : Continuous (Function.uncurry F) := by
    simpa only [F] using continuous_gsA10MovingRpowPrimeFactor hy hyX
  have hG : Continuous G := by
    dsimp only [G]
    exact continuous_const.mul
      ((Real.continuous_const_rpow (by positivity : (X : ℝ) ≠ 0)).comp
        (by fun_prop))
  have hinnerCont : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF 0 eta
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤ eta * G alpha := by
    calc
      _ ≤ ∫ beta : ℝ in 0..eta, G alpha := by
        apply intervalIntegral.integral_mono_on heta
        · exact (hF.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
        · exact continuous_const.intervalIntegrable 0 eta
        · intro beta hbeta
          exact gsA10MovingRpowPrimeFactor_le hy hyX hX hbeta.1
      _ = eta * G alpha := by simp
  have houter :
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, eta * G alpha := by
    apply intervalIntegral.integral_mono_on heta
    · exact hinnerCont.intervalIntegrable 0 eta
    · exact (hG.const_mul eta).intervalIntegrable 0 eta
    · intro alpha halpha
      exact hinner alpha
  have hdecay := intervalIntegral_rpow_one_sub_le_div_log hX heta
  change (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
    F alpha beta) ≤ _
  calc
    _ ≤ ∫ alpha : ℝ in 0..eta, eta * G alpha := houter
    _ = 2 * Real.exp 1 * eta *
        (∫ alpha : ℝ in 0..eta, (X : ℝ) ^ (1 - alpha)) := by
      simp only [G, intervalIntegral.integral_const_mul]
      ring
    _ ≤ 2 * Real.exp 1 * eta *
        ((X : ℝ) / Real.log (X : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg 1)) heta)

/-- The HPP correction enjoys at least the same moving-power rectangle
bound (it does not need the additional beta-growth factor). -/
theorem doubleIntervalIntegral_gsA10MovingPerronKernelScale_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 1 < X)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10MovingPerronKernelScale X alpha beta) ≤
      2 * Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hF := continuous_gsA10MovingRpowPrimeFactor hy hyX
  have hK : Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10MovingPerronKernelScale X alpha beta)) := by
    unfold gsA10MovingPerronKernelScale
    exact continuous_const.mul <|
      (Real.continuous_const_rpow (by positivity : (X : ℝ) ≠ 0)).comp
        (by fun_prop)
  have hinnerK : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta,
        gsA10MovingPerronKernelScale X alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hK 0 eta
  have hinnerF : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta,
        gsA10MovingRpowPrimeFactor y X alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF 0 eta
  apply le_trans ?_ (doubleIntervalIntegral_gsA10MovingRpowPrimeFactor_le
    hy hyX hX heta)
  apply intervalIntegral.integral_mono_on heta
  · exact hinnerK.intervalIntegrable 0 eta
  · exact hinnerF.intervalIntegrable 0 eta
  · intro alpha halpha
    apply intervalIntegral.integral_mono_on heta
    · exact (hK.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
    · exact (hF.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
    · intro beta hbeta
      exact gsA10MovingPerronKernelScale_le_primeFactor
        hy hyX hbeta.1

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsA10MovingRpowPrimeFactor_le
#print axioms
  Erdos67.MRHalaszBands.gsA10PrimeLambda_energyPair_eq_ratio_mul_right
#print axioms
  Erdos67.MRHalaszBands.doubleIntervalIntegral_gsA10MovingRpowPrimeFactor_le
#print axioms
  Erdos67.MRHalaszBands.doubleIntervalIntegral_gsA10MovingPerronKernelScale_le
