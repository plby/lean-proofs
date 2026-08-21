import ErdosProblems.Erdos239.External.Erdos67.MRGSA10MovingRpowAverage

/-!
# Averaged restored Perron bound with the moving power retained

This module performs only the exact alpha--beta power cancellation.  It
does not apply the nonfinal fixed-height source schedule: the common prime
energy and the higher-prime-power correction remain visible.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

private theorem gsA10HigherPrimePowerGeometricMass_nonneg_moving
    (y X : ℕ) : 0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
  unfold gsA10HigherPrimePowerGeometricMass
  apply Finset.sum_nonneg
  intro p hp
  have hpData := Erdos67.mem_primesUpTo.mp
    (Finset.mem_filter.mp hp).1
  apply mul_nonneg
  · exact Real.log_nonneg (by exact_mod_cast hpData.1.one_le)
  · apply Finset.sum_nonneg
    intro k hk
    exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
      (by positivity)

/-- The coefficient multiplying the exact moving-power average.  The
right prime energy is kept explicit, as is the full HPP correction. -/
def gsA10MovingRpowRestoredCoefficient
    (Cβ : ℝ) (Q S y A X : ℕ) (T : ℝ) : ℝ :=
  gsA10RestoredFixedHighHalaszEnvelope A X *
      gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T +
    2 * T * gsA10RestoredFixedHighHalaszEnvelope A X *
      ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2))

theorem gsA10MovingRpowRestoredCoefficient_nonneg
    {Cβ : ℝ} {Q S y A X : ℕ} {T : ℝ}
    (hCβ : 1 ≤ Cβ) (hX : 2 ≤ X) (hT : 0 < T) :
    0 ≤ gsA10MovingRpowRestoredCoefficient Cβ Q S y A X T := by
  have hrow : 0 ≤ gsA10PrimeGaussianRowBound Cβ Q S y X T :=
    gsA10PrimeGaussianRowBound_nonneg hCβ hX hT
  have hM : 0 ≤ gsA10RestoredFixedHighHalaszEnvelope A X :=
    gsA10RestoredFixedHighHalaszEnvelope_nonneg A X (by omega)
  have hbudget : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have hmass : 0 ≤ gsA10HigherPrimePowerGeometricMass y X :=
    gsA10HigherPrimePowerGeometricMass_nonneg_moving y X
  unfold gsA10MovingRpowRestoredCoefficient
    gsA10PrimeLambdaRightEnergyBound
    gsA10PrimeLambdaHarmonicBudget
  positivity

/-- A variable continuous majorant can be pulled through the two source
integrals without assuming continuity of the dominated integrand. -/
private theorem norm_two_mul_doubleIntervalIntegral_le_of_majorant
    {F : ℝ → ℝ → ℂ} {G : ℝ → ℝ → ℝ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hG : Continuous (Function.uncurry G))
    (hmajor : ∀ alpha ∈ Icc (0 : ℝ) eta,
      ∀ beta ∈ Icc (0 : ℝ) eta, ‖F alpha beta‖ ≤ G alpha beta) :
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, F alpha beta‖ ≤
      2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, G alpha beta := by
  have hGinner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, G alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hG 0 eta
  have hinner (alpha : ℝ) (halpha : alpha ∈ Icc (0 : ℝ) eta) :
      ‖∫ beta in (0 : ℝ)..eta, F alpha beta‖ ≤
        ∫ beta in (0 : ℝ)..eta, G alpha beta := by
    apply intervalIntegral.norm_integral_le_of_norm_le heta
    · filter_upwards with beta
      intro hbeta
      exact hmajor alpha halpha beta ⟨hbeta.1.le, hbeta.2⟩
    · exact (hG.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
  have houter :
      ‖∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, F alpha beta‖ ≤
        ∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, G alpha beta := by
    apply intervalIntegral.norm_integral_le_of_norm_le heta
    · filter_upwards with alpha
      intro halpha
      exact hinner alpha ⟨halpha.1.le, halpha.2⟩
    · exact hGinner.intervalIntegrable 0 eta
  calc
    ‖2 * ∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, F alpha beta‖ =
        2 * ‖∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, F alpha beta‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 2 * ∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, G alpha beta :=
      mul_le_mul_of_nonneg_left houter (by norm_num)

/-- Pointwise restored Perron control after the exact square-root energy
identity.  The only alpha--beta dependence is the moving-power factor. -/
theorem exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_primeFactor :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (halpha0 : 0 ≤ alpha)
        (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (hbeta0 : 0 ≤ beta)
        (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X)
        (hdist : ∀ t : ℝ, |t| ≤ T →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X),
        ‖gsA10TwoBlockMovingPerronIntegral
            f hmul P₁ P₂ y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ *
            (gsA10MovingRpowRestoredCoefficient Cβ Q S y A X T *
              gsA10MovingRpowPrimeFactor y X alpha beta) := by
  obtain ⟨Cβ, hCβ, hraw⟩ :=
    exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_movingRpow
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hyX hX
    hQ hQy hS hlogCβ alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT
    hTX hdist
  have hbase := hraw hmul hbound P₁ P₂ hsmallOutside hy hX hQ hQy hS
    hlogCβ hlogy halpha0 halpha hbeta0 hbeta hT hTX hdist
  have henergy := gsA10PrimeLambda_energyPair_eq_ratio_mul_right
    (Cβ := Cβ) (Q := Q) (S := S) (X := X) (y := y)
    (beta := beta) (T := T) hCβ hX hT
  have hK := gsA10MovingPerronKernelScale_le_primeFactor
    (y := y) (X := X) (alpha := alpha) (beta := beta)
    (by omega) hyX hbeta0
  have hM : 0 ≤ gsA10RestoredFixedHighHalaszEnvelope A X :=
    gsA10RestoredFixedHighHalaszEnvelope_nonneg A X (by omega)
  let H : ℝ :=
      (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2)
  have hH : 0 ≤ H := by
    have hmass : 0 ≤ gsA10HigherPrimePowerGeometricMass y X :=
      gsA10HigherPrimePowerGeometricMass_nonneg_moving y X
    have hbudget : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
      unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    positivity
  have hR : 0 ≤ gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T := by
    have hrow : 0 ≤ gsA10PrimeGaussianRowBound Cβ Q S y X T :=
      gsA10PrimeGaussianRowBound_nonneg hCβ hX hT
    have hbudget : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
      unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    unfold gsA10PrimeLambdaRightEnergyBound
    positivity
  have hscale : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    ‖gsA10TwoBlockMovingPerronIntegral
        f hmul P₁ P₂ y X alpha beta T‖ ≤ _ := hbase
    _ = (2 * Real.pi)⁻¹ *
        (gsA10RestoredFixedHighHalaszEnvelope A X *
            gsA10MovingPerronKernelScale X alpha beta *
              ((((X / y : ℕ) : ℝ) ^ (2 * beta)) *
                gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) +
          2 * T *
            (gsA10RestoredFixedHighHalaszEnvelope A X *
              gsA10MovingPerronKernelScale X alpha beta) *
            ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
              (2 * gsA10PrimeLambdaHarmonicBudget X *
                  gsA10HigherPrimePowerGeometricMass y X +
                (gsA10HigherPrimePowerGeometricMass y X) ^ 2))) := by
      congr 1
      congr 1
      · calc
          gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10MovingPerronKernelScale X alpha beta *
                (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                    (2 * beta) T) ^ ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                ((1 : ℝ) / 2) =
              gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10MovingPerronKernelScale X alpha beta *
                ((gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                    (2 * beta) T) ^ ((1 : ℝ) / 2) *
                  (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                    ((1 : ℝ) / 2)) := by ring
          _ = _ := by rw [henergy]
    _ ≤ (2 * Real.pi)⁻¹ *
        (gsA10MovingRpowRestoredCoefficient Cβ Q S y A X T *
          gsA10MovingRpowPrimeFactor y X alpha beta) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      unfold gsA10MovingRpowRestoredCoefficient
      have hPF :
          gsA10MovingRpowPrimeFactor y X alpha beta =
            gsA10MovingPerronKernelScale X alpha beta *
              (((X / y : ℕ) : ℝ) ^ (2 * beta)) := rfl
      rw [hPF]
      have hsecond :
          2 * T * gsA10RestoredFixedHighHalaszEnvelope A X * H *
              gsA10MovingPerronKernelScale X alpha beta ≤
            2 * T * gsA10RestoredFixedHighHalaszEnvelope A X * H *
              (gsA10MovingPerronKernelScale X alpha beta *
                (((X / y : ℕ) : ℝ) ^ (2 * beta))) := by
        simpa only [hPF] using
          (mul_le_mul_of_nonneg_left hK
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hT.le) hM) hH))
      calc
        gsA10RestoredFixedHighHalaszEnvelope A X *
              gsA10MovingPerronKernelScale X alpha beta *
              (((X / y : ℕ) : ℝ) ^ (2 * beta) *
                gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) +
            2 * T *
              (gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10MovingPerronKernelScale X alpha beta) * H =
            gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T *
                (gsA10MovingPerronKernelScale X alpha beta *
                  (((X / y : ℕ) : ℝ) ^ (2 * beta))) +
              2 * T * gsA10RestoredFixedHighHalaszEnvelope A X * H *
                gsA10MovingPerronKernelScale X alpha beta := by ring
        _ ≤ gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T *
                (gsA10MovingPerronKernelScale X alpha beta *
                  (((X / y : ℕ) : ℝ) ^ (2 * beta))) +
              2 * T * gsA10RestoredFixedHighHalaszEnvelope A X * H *
                (gsA10MovingPerronKernelScale X alpha beta *
                  (((X / y : ℕ) : ℝ) ^ (2 * beta))) :=
          add_le_add (le_refl _) hsecond
        _ = (gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T +
              2 * T * gsA10RestoredFixedHighHalaszEnvelope A X * H) *
            (gsA10MovingPerronKernelScale X alpha beta *
              (((X / y : ℕ) : ℝ) ^ (2 * beta))) := by ring

/-- Alpha--beta integration of the exact moving-power bound.  This gains
`X / log X` and cancels the beta growth of the left energy.  The theorem is
deliberately not a final source schedule: the right energy and HPP scalar
are still explicit. -/
theorem exists_norm_gsA10TwoBlockMovingPerronIntegrated_restored_le_movingRpow :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {eta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (heta0 : 0 ≤ eta)
        (heta : eta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X)
        (hdist : ∀ t : ℝ, |t| ≤ T →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X),
        ‖gsA10TwoBlockMovingPerronIntegrated
            f hmul P₁ P₂ y X eta T‖ ≤
          2 * (2 * Real.pi)⁻¹ *
            gsA10MovingRpowRestoredCoefficient Cβ Q S y A X T *
              (2 * Real.exp 1 * eta *
                ((X : ℝ) / Real.log (X : ℝ))) := by
  obtain ⟨Cβ, hCβ, hpoint⟩ :=
    exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_primeFactor
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hyX hX
    hQ hQy hS hlogCβ eta T hlogy heta0 heta hT hTX hdist
  let C : ℝ := gsA10MovingRpowRestoredCoefficient Cβ Q S y A X T
  let F : ℝ → ℝ → ℂ := fun alpha beta ↦
    gsA10TwoBlockMovingPerronIntegral
      f hmul P₁ P₂ y X alpha beta T
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    (2 * Real.pi)⁻¹ * C * gsA10MovingRpowPrimeFactor y X alpha beta
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G]
    exact continuous_const.mul
      (continuous_gsA10MovingRpowPrimeFactor (by omega) hyX)
  have hmajor : ∀ alpha ∈ Icc (0 : ℝ) eta,
      ∀ beta ∈ Icc (0 : ℝ) eta, ‖F alpha beta‖ ≤ G alpha beta := by
    intro alpha halpha beta hbeta
    have hp := hpoint hmul hbound P₁ P₂ hsmallOutside hy hyX hX
      hQ hQy hS hlogCβ hlogy halpha.1 (halpha.2.trans heta)
      hbeta.1 (hbeta.2.trans heta) hT hTX hdist
    simpa only [F, G, C, mul_assoc] using hp
  have hnorm := norm_two_mul_doubleIntervalIntegral_le_of_majorant
    heta0 hG hmajor
  have haverage := doubleIntervalIntegral_gsA10MovingRpowPrimeFactor_le
    (y := y) (X := X) (eta := eta) (by omega) hyX (by omega) heta0
  have hC : 0 ≤ C := by
    exact gsA10MovingRpowRestoredCoefficient_nonneg hCβ hX hT
  have hscale : 0 ≤ (2 * Real.pi)⁻¹ * C :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) hC
  unfold gsA10TwoBlockMovingPerronIntegrated
  calc
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta,
        gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta T‖ ≤
        2 * ∫ alpha in 0..eta, ∫ beta in 0..eta,
          G alpha beta := hnorm
    _ = 2 * ((2 * Real.pi)⁻¹ * C) *
        (∫ alpha in 0..eta, ∫ beta in 0..eta,
          gsA10MovingRpowPrimeFactor y X alpha beta) := by
      simp only [G, intervalIntegral.integral_const_mul]
      ring
    _ ≤ 2 * ((2 * Real.pi)⁻¹ * C) *
        (2 * Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ))) := by
      exact mul_le_mul_of_nonneg_left haverage
        (mul_nonneg (by norm_num) hscale)
    _ = 2 * (2 * Real.pi)⁻¹ *
          gsA10MovingRpowRestoredCoefficient Cβ Q S y A X T *
            (2 * Real.exp 1 * eta *
              ((X : ℝ) / Real.log (X : ℝ))) := by
      dsimp only [C]
      ring

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_primeFactor
#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10TwoBlockMovingPerronIntegrated_restored_le_movingRpow
