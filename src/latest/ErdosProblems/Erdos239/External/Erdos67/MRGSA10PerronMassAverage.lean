import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PerronRpowAverage

/-!
# Averaging a source-line Perron mass envelope

The coefficient-mass error in GS A.10 carries the moving Perron power
`X^(c-alpha-beta)`.  Its lower auxiliary line may contribute the opposite
growth `X^(1-min (c-beta) 1)`.  This file packages the elementary fact that
an additional nonnegative constant factor may be retained while the two
powers are averaged over the source square.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The fixed-high A.10 line has the same averaged moving-power gain.  Here
the lower Mangoldt window lies on `c - 2 * beta`, while the high Dirichlet
factor stays at `c`. -/
theorem doubleIntervalIntegral_sourcePerron_fixedHigh_rpow_mul_leftGrowth_le
    {X : ℕ} (hX : 1 < X) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
          (X : ℝ) ^
            (1 - min
              (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) ≤
      Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
      (X : ℝ) ^
        (1 - min
          (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)
  let G : ℝ → ℝ := fun alpha ↦ Real.exp 1 * (X : ℝ) ^ (1 - alpha)
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry_apply_pair]
    exact ((Real.continuous_const_rpow hXne).comp
      (by fun_prop)).mul
      ((Real.continuous_const_rpow hXne).comp (by fun_prop))
  have hG : Continuous G := by
    dsimp only [G]
    exact continuous_const.mul
      ((Real.continuous_const_rpow hXne).comp (by fun_prop))
  have hinnerContinuous : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤ eta * G alpha := by
    calc
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤
          ∫ beta : ℝ in 0..eta, G alpha := by
        apply intervalIntegral.integral_mono_on heta
        · exact (hF.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
        · exact continuous_const.intervalIntegrable 0 eta
        · intro beta hbeta
          exact sourcePerron_fixedHigh_rpow_mul_leftGrowth_le hX hbeta.1
      _ = eta * G alpha := by simp
  have houter :
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, eta * G alpha := by
    apply intervalIntegral.integral_mono_on heta
    · exact hinnerContinuous.intervalIntegrable 0 eta
    · exact (hG.const_mul eta).intervalIntegrable 0 eta
    · intro alpha halpha
      exact hinner alpha
  have hdecay := intervalIntegral_rpow_one_sub_le_div_log hX heta
  change (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, F alpha beta) ≤ _
  calc
    (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, eta * G alpha := houter
    _ = eta * Real.exp 1 *
          (∫ alpha : ℝ in 0..eta, (X : ℝ) ^ (1 - alpha)) := by
      simp only [G, intervalIntegral.integral_const_mul]
      ring
    _ ≤ eta * Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg heta (Real.exp_nonneg 1))
    _ = Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by ring

/-- A constant multiple of the fixed-high moving-power envelope retains the
same `eta / log X` gain after averaging. -/
theorem doubleIntervalIntegral_sourcePerron_fixedHigh_massEnvelope_le
    {X : ℕ} (hX : 1 < X) {eta K : ℝ}
    (heta : 0 ≤ eta) (hK : 0 ≤ K) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        K *
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
            (X : ℝ) ^
              (1 - min
                (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))) ≤
      K * Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hbase :=
    doubleIntervalIntegral_sourcePerron_fixedHigh_rpow_mul_leftGrowth_le
      hX heta
  calc
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        K *
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
            (X : ℝ) ^
              (1 - min
                (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))) =
        K *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              (X : ℝ) ^
                  (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
                (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) := by
      simp only [intervalIntegral.integral_const_mul]
    _ ≤ K * (Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ))) :=
      mul_le_mul_of_nonneg_left hbase hK
    _ = K * Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ)) := by ring

/-- A constant multiple of the source moving-power envelope retains the
decisive `eta / log X` gain after the alpha--beta average. -/
theorem doubleIntervalIntegral_sourcePerron_massEnvelope_le
    {X : ℕ} (hX : 1 < X) {eta K : ℝ}
    (heta : 0 ≤ eta) (hK : 0 ≤ K) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        K *
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
            (X : ℝ) ^
              (1 - min
                (Erdos67.EulerResidue.taoExponent X - beta) 1))) ≤
      K * Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hbase := doubleIntervalIntegral_sourcePerron_rpow_mul_leftGrowth_le
    hX heta
  calc
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        K *
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
            (X : ℝ) ^
              (1 - min
                (Erdos67.EulerResidue.taoExponent X - beta) 1))) =
        K *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              (X : ℝ) ^
                  (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
                (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - beta) 1)) := by
      simp only [intervalIntegral.integral_const_mul]
    _ ≤ K * (Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ))) :=
      mul_le_mul_of_nonneg_left hbase hK
    _ = K * Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ)) := by ring

/-- Pointwise coefficient-mass domination by the source envelope can be
integrated without first flattening either moving power. -/
theorem doubleIntervalIntegral_sourcePerron_mul_mass_le
    {X : ℕ} (hX : 1 < X) {eta K : ℝ}
    (heta : 0 ≤ eta) (hK : 0 ≤ K)
    {M : ℝ → ℝ → ℝ}
    (hM : Continuous (Function.uncurry M))
    (hMle : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        M alpha beta ≤
          K * (X : ℝ) ^
            (1 - min
              (Erdos67.EulerResidue.taoExponent X - beta) 1)) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
          M alpha beta) ≤
      K * Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  let P : ℝ → ℝ → ℝ := fun alpha beta ↦
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta)
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    K *
      (P alpha beta *
        (X : ℝ) ^
          (1 - min
            (Erdos67.EulerResidue.taoExponent X - beta) 1))
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hP : Continuous (Function.uncurry P) := by
    dsimp only [P, Function.uncurry_apply_pair]
    exact (Real.continuous_const_rpow hXne).comp (by fun_prop)
  have hleft : Continuous (Function.uncurry (fun alpha beta ↦
      P alpha beta * M alpha beta)) := hP.mul hM
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G, Function.uncurry_apply_pair]
    exact continuous_const.mul <| hP.mul <|
      (Real.continuous_const_rpow hXne).comp (by fun_prop)
  have hmono :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          P alpha beta * M alpha beta) ≤
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, G alpha beta := by
    have hleftInner : Continuous (fun alpha : ℝ ↦
        ∫ beta : ℝ in 0..eta, P alpha beta * M alpha beta) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hleft
    have hGInner : Continuous (fun alpha : ℝ ↦
        ∫ beta : ℝ in 0..eta, G alpha beta) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hG
    apply intervalIntegral.integral_mono_on heta
    · exact hleftInner.intervalIntegrable 0 eta
    · exact hGInner.intervalIntegrable 0 eta
    · intro alpha halpha
      apply intervalIntegral.integral_mono_on heta
      · exact (hleft.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · exact (hG.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · intro beta hbeta
        have hP0 : 0 ≤ P alpha beta := by
          dsimp only [P]
          exact Real.rpow_nonneg (by positivity) _
        calc
          P alpha beta * M alpha beta ≤
              P alpha beta *
                (K * (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - beta) 1)) :=
            mul_le_mul_of_nonneg_left (hMle alpha halpha beta hbeta) hP0
          _ = G alpha beta := by simp only [G]; ring
  calc
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
          M alpha beta) =
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, P alpha beta * M alpha beta := rfl
    _ ≤ ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, G alpha beta := hmono
    _ = ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            K *
              ((X : ℝ) ^
                  (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
                (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - beta) 1)) := by
      apply intervalIntegral.integral_congr
      intro alpha _
      apply intervalIntegral.integral_congr
      intro beta _
      simp only [G, P]
    _ ≤ _ := doubleIntervalIntegral_sourcePerron_massEnvelope_le
      hX heta hK

/-- The pointwise mass-domination wrapper on the source-correct fixed-high
lines.  This is the form consumed by the ordinary-multiplicative A.10
coefficient-mass estimate. -/
theorem doubleIntervalIntegral_sourcePerron_fixedHigh_mul_mass_le
    {X : ℕ} (hX : 1 < X) {eta K : ℝ}
    (heta : 0 ≤ eta) (hK : 0 ≤ K)
    {M : ℝ → ℝ → ℝ}
    (hM : Continuous (Function.uncurry M))
    (hMle : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        M alpha beta ≤
          K * (X : ℝ) ^
            (1 - min
              (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
          M alpha beta) ≤
      K * Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  let P : ℝ → ℝ → ℝ := fun alpha beta ↦
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta)
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    K *
      (P alpha beta *
        (X : ℝ) ^
          (1 - min
            (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hP : Continuous (Function.uncurry P) := by
    dsimp only [P, Function.uncurry_apply_pair]
    exact (Real.continuous_const_rpow hXne).comp (by fun_prop)
  have hleft : Continuous (Function.uncurry (fun alpha beta ↦
      P alpha beta * M alpha beta)) := hP.mul hM
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G, Function.uncurry_apply_pair]
    exact continuous_const.mul <| hP.mul <|
      (Real.continuous_const_rpow hXne).comp (by fun_prop)
  have hmono :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          P alpha beta * M alpha beta) ≤
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, G alpha beta := by
    have hleftInner : Continuous (fun alpha : ℝ ↦
        ∫ beta : ℝ in 0..eta, P alpha beta * M alpha beta) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hleft
    have hGInner : Continuous (fun alpha : ℝ ↦
        ∫ beta : ℝ in 0..eta, G alpha beta) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hG
    apply intervalIntegral.integral_mono_on heta
    · exact hleftInner.intervalIntegrable 0 eta
    · exact hGInner.intervalIntegrable 0 eta
    · intro alpha halpha
      apply intervalIntegral.integral_mono_on heta
      · exact (hleft.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · exact (hG.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · intro beta hbeta
        have hP0 : 0 ≤ P alpha beta := by
          dsimp only [P]
          exact Real.rpow_nonneg (by positivity) _
        calc
          P alpha beta * M alpha beta ≤
              P alpha beta *
                (K * (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) :=
            mul_le_mul_of_nonneg_left (hMle alpha halpha beta hbeta) hP0
          _ = G alpha beta := by simp only [G]; ring
  calc
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
          M alpha beta) =
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, P alpha beta * M alpha beta := rfl
    _ ≤ ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, G alpha beta := hmono
    _ = ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            K *
              ((X : ℝ) ^
                  (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
                (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) := by
      apply intervalIntegral.integral_congr
      intro alpha _
      apply intervalIntegral.integral_congr
      intro beta _
      simp only [G, P]
    _ ≤ _ := doubleIntervalIntegral_sourcePerron_fixedHigh_massEnvelope_le
      hX heta hK

end

end Erdos67.MRHalaszBands
