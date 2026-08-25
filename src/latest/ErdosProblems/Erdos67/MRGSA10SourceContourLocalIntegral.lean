import ErdosProblems.Erdos67.MRGSA10SourceContourLocalEnvelope
import ErdosProblems.Erdos67.MRGSA10SourceBetaIntegral
import ErdosProblems.Erdos67.MRGSA10SourceHPPBetaIntegral

/-! Scalar integration of the continuous fixed-source contour envelope. -/

open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

private theorem doubleIntegral_sourceContourBetaPoleEnvelope_eq
    {X y A : ℕ} (hX : 2 ≤ X) (hy : 0 < y) (hyX : y ≤ X)
    {eta T Arow Brow : ℝ} :
    let L := Real.log (X : ℝ)
    let d := L⁻¹
    let power : ℝ → ℝ → ℝ := fun alpha beta ↦
      (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        ((X / y : ℕ) : ℝ) ^ beta
    let poleThree : ℝ → ℝ := fun beta ↦
      (max (d + beta) (d / 2)) ^ (-3 / 2 : ℝ)
    let poleHalf : ℝ → ℝ := fun beta ↦
      Real.sqrt ((max (d + beta) (d / 2))⁻¹)
    let C := (2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
      Real.exp
        (28 * Real.exp 4 *
            Erdos67.EulerQuantitative.primeQuadraticConstant +
          36 * gsA9SourceShiftConstant) *
      gsA10SourceMaximumModulusSqrtScalar A X
    let Q := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
    let D := 2 * gsA10PrimeLambdaSymmetricBetaScalarConstant
    let G :=
      2 * gsA10PrimeLambdaHarmonicBudget X *
          gsA10HigherPrimePowerGeometricMass y X +
        (gsA10HigherPrimePowerGeometricMass y X) ^ 2
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10SourceContourBetaPoleEnvelope
          A X y alpha beta T Arow Brow) =
      C *
        (Q * D *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                power alpha beta * poleThree beta) +
          4 * T * G *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                power alpha beta * poleHalf beta)) := by
  dsimp only
  let L : ℝ := Real.log (X : ℝ)
  let d : ℝ := L⁻¹
  let power : ℝ → ℝ → ℝ := fun alpha beta ↦
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
      ((X / y : ℕ) : ℝ) ^ beta
  let poleThree : ℝ → ℝ := fun beta ↦
    (max (d + beta) (d / 2)) ^ (-3 / 2 : ℝ)
  let poleHalf : ℝ → ℝ := fun beta ↦
    Real.sqrt ((max (d + beta) (d / 2))⁻¹)
  let C : ℝ := (2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
    Real.exp
      (28 * Real.exp 4 *
          Erdos67.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant) *
    gsA10SourceMaximumModulusSqrtScalar A X
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
  let D : ℝ := 2 * gsA10PrimeLambdaSymmetricBetaScalarConstant
  let G : ℝ :=
    2 * gsA10PrimeLambdaHarmonicBudget X *
        gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2
  have hEnv : ∀ alpha beta,
      gsA10SourceContourBetaPoleEnvelope
          A X y alpha beta T Arow Brow =
        C * (Q * D * (power alpha beta * poleThree beta) +
          4 * T * G * (power alpha beta * poleHalf beta)) := by
    intro alpha beta
    rfl
  simp_rw [hEnv, intervalIntegral.integral_const_mul]
  have hcont := continuous_gsA10SourceContourBetaPoleEnvelope
    hX hy hyX A T Arow Brow
  have hpower : Continuous (Function.uncurry power) := by
    let hXne : (X : ℝ) ≠ 0 := by
      exact_mod_cast (show X ≠ 0 by omega)
    have hdiv : X / y ≠ 0 :=
      Nat.ne_of_gt (Nat.div_pos hyX hy)
    dsimp only [power, Function.uncurry_apply_pair]
    exact ((Real.continuous_const_rpow hXne).comp (by fun_prop)).mul
      ((Real.continuous_const_rpow (by exact_mod_cast hdiv)).comp
        (by fun_prop))
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hpoleThree : Continuous poleThree := by
    dsimp only [poleThree]
    apply Continuous.rpow_const
    · fun_prop
    · intro beta
      left
      exact ((half_pos hd).trans_le (le_max_right _ _)).ne'
  have hpoleHalf : Continuous poleHalf := by
    dsimp only [poleHalf]
    apply Real.continuous_sqrt.comp
    apply Continuous.inv₀
    · fun_prop
    · intro beta hzero
      exact ((half_pos hd).trans_le (le_max_right _ _)).ne' hzero
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    Q * D * (power alpha beta * poleThree beta)
  let H : ℝ → ℝ → ℝ := fun alpha beta ↦
    4 * T * G * (power alpha beta * poleHalf beta)
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry_apply_pair]
    exact continuous_const.mul
      (hpower.mul (hpoleThree.comp continuous_snd))
  have hH : Continuous (Function.uncurry H) := by
    dsimp only [H, Function.uncurry_apply_pair]
    exact continuous_const.mul
      (hpower.mul (hpoleHalf.comp continuous_snd))
  have hadd :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F alpha beta + H alpha beta) =
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F alpha beta) +
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, H alpha beta) := by
    have hinnerF : Continuous (fun alpha : ℝ ↦
        ∫ beta : ℝ in 0..eta, F alpha beta) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hF 0 eta
    have hinnerH : Continuous (fun alpha : ℝ ↦
        ∫ beta : ℝ in 0..eta, H alpha beta) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hH 0 eta
    calc
      _ = ∫ alpha : ℝ in 0..eta,
          ((∫ beta : ℝ in 0..eta, F alpha beta) +
            ∫ beta : ℝ in 0..eta, H alpha beta) := by
        apply intervalIntegral.integral_congr
        intro alpha halpha
        exact intervalIntegral.integral_add
          ((hF.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
          ((hH.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
      _ = _ := intervalIntegral.integral_add
        (hinnerF.intervalIntegrable 0 eta)
        (hinnerH.intervalIntegrable 0 eta)
  rw [show (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Q * D * (power alpha beta * poleThree beta) +
          4 * T * G * (power alpha beta * poleHalf beta)) =
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F alpha beta + H alpha beta) by rfl]
  rw [hadd]
  simp only [F, H, intervalIntegral.integral_const_mul]
  rfl

theorem normalized_doubleIntervalIntegral_gsA10SourceContourBetaPoleEnvelope_le
    {A X y : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 2 ≤ X)
    {eta T Arow Brow : ℝ} (heta : 0 ≤ eta)
    (hT0 : 0 ≤ T) (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow) :
    (X : ℝ)⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10SourceContourBetaPoleEnvelope
              A X y alpha beta T Arow Brow) ≤
      ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
          Real.exp
            (28 * Real.exp 4 *
                Erdos67.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) * Real.exp 1) *
        (gsA10SourceMaximumModulusSqrtScalar A X /
          Real.sqrt (Real.log (X : ℝ))) *
        (2 *
            (Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)) *
            (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
          4 * T *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              (gsA10HigherPrimePowerGeometricMass y X) ^ 2) * eta) := by
  let L : ℝ := Real.log (X : ℝ)
  let d : ℝ := L⁻¹
  let power : ℝ → ℝ → ℝ := fun alpha beta ↦
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
      ((X / y : ℕ) : ℝ) ^ beta
  let poleThree : ℝ → ℝ := fun beta ↦
    (max (d + beta) (d / 2)) ^ (-3 / 2 : ℝ)
  let poleHalf : ℝ → ℝ := fun beta ↦
    Real.sqrt ((max (d + beta) (d / 2))⁻¹)
  let C : ℝ := (2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
    Real.exp
      (28 * Real.exp 4 *
          Erdos67.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant) *
    gsA10SourceMaximumModulusSqrtScalar A X
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
  let D : ℝ := 2 * gsA10PrimeLambdaSymmetricBetaScalarConstant
  let G : ℝ :=
    2 * gsA10PrimeLambdaHarmonicBudget X *
        gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2
  let Ithree : ℝ :=
    ∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, power alpha beta * poleThree beta
  let Ihalf : ℝ :=
    ∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, power alpha beta * poleHalf beta
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hEq :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10SourceContourBetaPoleEnvelope
            A X y alpha beta T Arow Brow) =
        C * (Q * D * Ithree + 4 * T * G * Ihalf) := by
    simpa only [L, d, power, poleThree, poleHalf, C, Q, D, G,
      Ithree, Ihalf] using
      (doubleIntegral_sourceContourBetaPoleEnvelope_eq
        (A := A) hX hy hyX (eta := eta) (T := T)
          (Arow := Arow) (Brow := Brow))
  have hpoleThreeEq : ∀ beta ∈ Icc (0 : ℝ) eta,
      poleThree beta = (L⁻¹ + beta) ^ (-3 / 2 : ℝ) := by
    intro beta hbeta
    dsimp only [poleThree, d]
    rw [max_eq_left]
    linarith [hbeta.1, inv_pos.mpr hL]
  have hpoleHalfEq : ∀ beta ∈ Icc (0 : ℝ) eta,
      poleHalf beta = Real.sqrt ((L⁻¹ + beta)⁻¹) := by
    intro beta hbeta
    dsimp only [poleHalf, d]
    rw [max_eq_left]
    linarith [hbeta.1, inv_pos.mpr hL]
  have hIthree : Ithree ≤
      2 * Real.exp 1 * ((X : ℝ) / L) * Real.sqrt L := by
    have hraw := doubleIntervalIntegral_sourcePerron_symmetricBetaPole_le
      hy hyX (by omega : 1 < X) heta
    have heq : Ithree =
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            power alpha beta * (L⁻¹ + beta) ^ (-3 / 2 : ℝ) := by
      dsimp only [Ithree]
      apply intervalIntegral.integral_congr
      intro alpha halpha
      apply intervalIntegral.integral_congr
      intro beta hbeta
      have hb : beta ∈ Icc (0 : ℝ) eta := by
        simpa only [uIcc_of_le heta] using hbeta
      change power alpha beta * poleThree beta =
        power alpha beta * (L⁻¹ + beta) ^ (-3 / 2 : ℝ)
      rw [hpoleThreeEq beta hb]
    rw [heq]
    simpa only [power, L] using hraw
  have hIhalf : Ihalf ≤
      Real.exp 1 * ((X : ℝ) / L) * (eta * Real.sqrt L) := by
    have hraw :=
      doubleIntervalIntegral_sourcePerron_symmetricBetaSqrtPole_le
        hy hyX (by omega : 1 < X) heta
    have heq : Ihalf =
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            power alpha beta * Real.sqrt ((L⁻¹ + beta)⁻¹) := by
      dsimp only [Ihalf]
      apply intervalIntegral.integral_congr
      intro alpha halpha
      apply intervalIntegral.integral_congr
      intro beta hbeta
      have hb : beta ∈ Icc (0 : ℝ) eta := by
        simpa only [uIcc_of_le heta] using hbeta
      change power alpha beta * poleHalf beta =
        power alpha beta * Real.sqrt ((L⁻¹ + beta)⁻¹)
      rw [hpoleHalfEq beta hb]
    rw [heq]
    simpa only [power, L] using hraw
  have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound := by
    unfold gsA9SmallPrimeEulerBound
    apply Finset.prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (by
      have hpPrime := (Finset.mem_filter.mp hp).2
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hpPrime.one_le)
        (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)))
  have hC0 : 0 ≤ C := by
    dsimp only [C, gsA10SourceMaximumModulusSqrtScalar]
    positivity
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by norm_num)
      gsA10PrimeLambdaSymmetricBetaScalarConstant_nonneg
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    have hH0 : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
      unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    have hP0 : 0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
      unfold gsA10HigherPrimePowerGeometricMass
      apply Finset.sum_nonneg
      intro p hp
      apply mul_nonneg
      · exact Real.log_nonneg (by
          have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
          exact_mod_cast hpPrime.one_le)
      · apply Finset.sum_nonneg
        intro k hk
        exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
          (pow_nonneg (Nat.cast_nonneg _) _)
    positivity
  have hintegrated :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10SourceContourBetaPoleEnvelope
            A X y alpha beta T Arow Brow) ≤
        C * (Q * D *
              (2 * Real.exp 1 * ((X : ℝ) / L) * Real.sqrt L) +
            4 * T * G *
              (Real.exp 1 * ((X : ℝ) / L) *
                (eta * Real.sqrt L))) := by
    rw [hEq]
    exact mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_left hIthree (mul_nonneg hQ0 hD0))
        (mul_le_mul_of_nonneg_left hIhalf
          (mul_nonneg (mul_nonneg (by norm_num) hT0) hG0))) hC0
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  calc
    (X : ℝ)⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10SourceContourBetaPoleEnvelope
              A X y alpha beta T Arow Brow) ≤
      (X : ℝ)⁻¹ *
        (C * (Q * D *
              (2 * Real.exp 1 * ((X : ℝ) / L) * Real.sqrt L) +
            4 * T * G *
              (Real.exp 1 * ((X : ℝ) / L) *
                (eta * Real.sqrt L)))) :=
      mul_le_mul_of_nonneg_left hintegrated (inv_nonneg.mpr hXpos.le)
    _ = ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
          Real.exp
            (28 * Real.exp 4 *
                Erdos67.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) * Real.exp 1) *
        (gsA10SourceMaximumModulusSqrtScalar A X / Real.sqrt L) *
        (2 * Q * D + 4 * T * G * eta) := by
      dsimp only [C]
      field_simp [hXpos.ne', hL.ne', hsqrtL.ne']
      rw [Real.sq_sqrt hL.le]
    _ = _ := by
      dsimp only [Q, D, G, L]

end


end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.normalized_doubleIntervalIntegral_gsA10SourceContourBetaPoleEnvelope_le
