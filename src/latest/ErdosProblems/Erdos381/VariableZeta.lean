import ErdosProblems.Erdos381.Zeta
import ErdosProblems.Erdos48.PointwiseZeroDetectorSecondParameters
import ErdosProblems.Erdos48.VariableBandLimitedDetector
import ErdosProblems.Erdos48.VariableZeroSelection
import ErdosProblems.Erdos48.VariableSelectedZeroBandMass
import ErdosProblems.Erdos48.VariableRawLogFreeDensity
import ErdosProblems.Erdos48.VariableLogFreeDensityPower

namespace Erdos381

open Complex Metric Set
open BoundedGaps.Maynard
open Erdos48

noncomputable section

/-! The conductor-one analogue of the second Turán detector.  This is the
only analytic step not already shared with the primitive-character density
development. -/

theorem exists_zeta_pointwise_zero_detector_second_of_error_budget :
    ∃ Am Al Af Ad : ℕ,
      37 ≤ Am ∧ 37 ≤ Al ∧ 37 ≤ Af ∧ 37 ≤ Ad ∧
      ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
        ∀ (rho₀ : ℂ), riemannZeta₁ rho₀ = 0 →
          dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
          ∀ (M : ℕ), 1 ≤ M →
            let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
            let Z := zetaSmallDiskZeroFinsupp t eta
            let K := Z.support.card
            (∀ j ∈ Finset.Icc (M + 1) (M + K),
              turanSecondLoss K M * (2 * eta) ^ j *
                zetaPointwiseZeroDetectorError Al Af Ad t eta j ≤ 1 / 4) →
            ∃ j ∈ Finset.Icc (M + 1) (M + K),
              ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
                turanSecondLoss K M * (2 * eta) ^ j *
                  ‖iteratedDeriv (j - 1)
                    (fun w ↦ -logDeriv riemannZeta₁ w) z‖ := by
  obtain ⟨Am, hAm, hmass⟩ := exists_zetaSmallDiskZeroMultiplicity_bound
  obtain ⟨Al, Af, hAl, hAf, htail⟩ :=
    exists_norm_zetaRadiusSix_sub_smallDisk_powerSum_le
  obtain ⟨Ad, hAd, hderiv⟩ := exists_zetaRadiusSix_iteratedDeriv_approximation
  refine ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, ?_⟩
  intro t eta heta0 heta8 rho₀ hzero hrho₀ M hM
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let Z := zetaSmallDiskZeroFinsupp t eta
  let D := zetaRadiusSixZeroFinsupp t
  let K := Z.support.card
  intro hbudget
  have hzre : z.re = 1 + eta := by simp [z]
  have hzrho₀ : z ≠ rho₀ := by
    intro hzr
    have := congrArg Complex.re hzr
    rw [hzre] at this
    have hrhoRe := riemannZeta₁_zero_re_lt_one hzero
    linarith
  have horderNe : analyticOrderNatAt riemannZeta₁ rho₀ ≠ 0 := by
    have hsupp : rho₀ ∈
        (MeromorphicOn.divisor riemannZeta₁ Set.univ).support :=
      (mem_support_divisor_riemannZeta₁_iff (Set.mem_univ rho₀)).2 hzero
    rw [Function.mem_support,
      divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
        (Set.mem_univ rho₀)] at hsupp
    exact_mod_cast hsupp
  have horder : 0 < analyticOrderNatAt riemannZeta₁ rho₀ :=
    Nat.pos_of_ne_zero horderNe
  have hZrho₀ : Z rho₀ ≠ 0 := by
    change zetaSmallDiskZeroMultiplicity t eta rho₀ ≠ 0
    rw [zetaSmallDiskZeroMultiplicity,
      if_pos (hrho₀.trans (by linarith : 2 * eta ≤ 4 * eta))]
    exact horder.ne'
  have hne : ∀ rho ∈ Z.support, z ≠ rho := by
    intro rho hrho hzrho
    have hZrho : Z rho ≠ 0 := Finsupp.mem_support_iff.mp hrho
    have hm : analyticOrderNatAt riemannZeta₁ rho ≠ 0 := by
      change zetaSmallDiskZeroMultiplicity t eta rho ≠ 0 at hZrho
      rw [zetaSmallDiskZeroMultiplicity] at hZrho
      split at hZrho
      · exact hZrho
      · exact False.elim (hZrho rfl)
    have hzeroRho : riemannZeta₁ rho = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
    have hrhoRe : rho.re < 1 := riemannZeta₁_zero_re_lt_one hzeroRho
    have hre := congrArg Complex.re hzrho
    rw [hzre] at hre
    linarith
  obtain ⟨j, hjrange, hjlarge⟩ :=
    exists_weightedReciprocalPowerSum_second Z hZrho₀ hne
      (M := M) (R := 2 * eta) (by positivity) hrho₀
  refine ⟨j, hjrange, ?_⟩
  have hj2 : 2 ≤ j := by
    have := (Finset.mem_Icc.mp hjrange).1
    omega
  let Sz : ℂ := Z.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  let Sd : ℂ := D.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  have hlocal : 1 ≤ turanSecondLoss K M * (2 * eta) ^ j * ‖Sz‖ := by
    simpa only [K, Z, Sz, turanSecondLoss] using hjlarge
  have htail' := htail t eta heta0 heta8 j hj2
  have htailNorm : ‖Sd - Sz‖ ≤
      96 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) * Real.log (|t| + 2)) /
          (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) * Real.log (|t| + 2)) /
          (1 / 2 : ℝ) ^ j := by
    simpa only [Sd, Sz, D, Z, z] using htail'
  have hderiv' := hderiv t eta heta0
    (by linarith : eta ≤ 1) (j - 1)
  have hjpred : j - 1 + 1 = j := by omega
  have hderivNorm :
      ‖iteratedDeriv (j - 1)
            (fun w ↦ -logDeriv riemannZeta₁ w) z -
          (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        (j - 1).factorial *
          (16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3) := by
    simpa only [hjpred, Sd, D, z] using hderiv'
  have hbudget' := hbudget j hjrange
  have herror :
      turanSecondLoss K M * (2 * eta) ^ j *
        ((96 * (Real.log 4 + 4) / (4 * eta) ^ j +
          ((1024 * (Al : ℝ) / 3) * Real.log (|t| + 2)) /
            (4 * eta) ^ (j - 1) +
          (2 * (Af : ℝ) * Real.log (|t| + 2)) /
            (1 / 2 : ℝ) ^ j) +
          16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3) ≤ 1 / 4 := by
    simpa only [zetaPointwiseZeroDetectorError, add_assoc] using hbudget'
  have hSz : ‖Sz‖ ≤ ‖Sd‖ + ‖Sd - Sz‖ := by
    calc
      ‖Sz‖ = ‖Sd - (Sd - Sz)‖ := by ring_nf
      _ ≤ ‖Sd‖ + ‖Sd - Sz‖ := norm_sub_le _ _
  let F : ℂ := iteratedDeriv (j - 1)
    (fun w ↦ -logDeriv riemannZeta₁ w) z
  have hscaled : ((j - 1).factorial : ℝ) * ‖Sd‖ ≤
      ‖F‖ + ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := by
    have htri : ‖(-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        ‖F‖ + ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := by
      calc
        ‖(-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ =
            ‖F - (F - (-1 : ℂ) ^ j *
              (j - 1).factorial * Sd)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_sub_le _ _
    simpa [norm_mul] using htri
  have hfacPos : (0 : ℝ) < (j - 1).factorial := by positivity
  have hlossPos : 0 < turanSecondLoss K M := by
    apply turanSecondLoss_pos
    dsimp [K]
    exact Finset.card_pos.mpr
      ⟨rho₀, Finsupp.mem_support_iff.mpr hZrho₀⟩
  have hXpos : 0 < turanSecondLoss K M * (2 * eta) ^ j := by positivity
  let Etail : ℝ :=
    96 * (Real.log 4 + 4) / (4 * eta) ^ j +
      ((1024 * (Al : ℝ) / 3) * Real.log (|t| + 2)) /
        (4 * eta) ^ (j - 1) +
      (2 * (Af : ℝ) * Real.log (|t| + 2)) /
        (1 / 2 : ℝ) ^ j
  let Ederiv : ℝ :=
    16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3
  have htailUse : ‖Sd - Sz‖ ≤ Etail := by
    simpa only [Etail] using htailNorm
  have hderivUse :
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        (j - 1).factorial * Ederiv := by
    simpa only [F, Ederiv] using hderivNorm
  have herror' :
      turanSecondLoss K M * (2 * eta) ^ j *
        (Etail + Ederiv) ≤ 1 / 4 := by
    simpa only [Etail, Ederiv] using herror
  let X : ℝ := turanSecondLoss K M * (2 * eta) ^ j
  let f : ℝ := ((j - 1).factorial : ℝ)
  have hXnonneg : 0 ≤ X := le_of_lt (by simpa only [X] using hXpos)
  have hfnonneg : 0 ≤ f := le_of_lt (by simpa only [f] using hfacPos)
  have hlocalFac : f ≤ f * (X * ‖Sz‖) := by
    calc
      f = f * 1 := by ring
      _ ≤ f * (X * ‖Sz‖) := by
        apply mul_le_mul_of_nonneg_left _ hfnonneg
        simpa only [X] using hlocal
  have hsumBound :
      f * ‖Sz‖ ≤ ‖F‖ +
        ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
        f * ‖Sd - Sz‖ := by
    calc
      f * ‖Sz‖ ≤ f * (‖Sd‖ + ‖Sd - Sz‖) := by
        exact mul_le_mul_of_nonneg_left hSz hfnonneg
      _ = f * ‖Sd‖ + f * ‖Sd - Sz‖ := by ring
      _ ≤ (‖F‖ +
          ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖) +
          f * ‖Sd - Sz‖ := by
        simpa only [f, add_comm] using
          add_le_add_right hscaled (f * ‖Sd - Sz‖)
  have herrBound :
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖ ≤ f * (Ederiv + Etail) := by
    calc
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖ ≤ f * Ederiv + f * Etail := by
        exact add_le_add (by simpa only [f] using hderivUse)
          (mul_le_mul_of_nonneg_left htailUse hfnonneg)
      _ = f * (Ederiv + Etail) := by ring
  have hscaledError : X *
        (‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖) ≤ f * (1 / 4) := by
    calc
      X * (‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖) ≤ X * (f * (Ederiv + Etail)) := by
        exact mul_le_mul_of_nonneg_left herrBound hXnonneg
      _ = f * (X * (Etail + Ederiv)) := by ring
      _ ≤ f * (1 / 4) := by
        apply mul_le_mul_of_nonneg_left _ hfnonneg
        simpa only [X] using herror'
  have hfacUpper : f ≤ X * ‖F‖ + f * (1 / 4) := by
    calc
      f ≤ f * (X * ‖Sz‖) := hlocalFac
      _ = X * (f * ‖Sz‖) := by ring
      _ ≤ X * (‖F‖ +
          ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖) := by
        exact mul_le_mul_of_nonneg_left hsumBound hXnonneg
      _ = X * ‖F‖ + X *
          (‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
            f * ‖Sd - Sz‖) := by ring
      _ ≤ X * ‖F‖ + f * (1 / 4) :=
        add_le_add (le_refl _) hscaledError
  have hfpos : 0 < f := by simpa only [f] using hfacPos
  change f * (1 / 2) < X * ‖F‖
  nlinarith

/-- Common coefficient in the scaled conductor-one detector error. -/
noncomputable def zetaPointwiseSecondErrorCoefficient
    (Al Af Ad : ℕ) (h : ℝ) : ℝ :=
  96 * (Real.log 4 + 4) +
    (4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) +
      64 * (Ad : ℝ) / 3) * h

theorem zetaPointwiseSecondErrorCoefficient_nonneg
    (Al Af Ad : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ zetaPointwiseSecondErrorCoefficient Al Af Ad h := by
  unfold zetaPointwiseSecondErrorCoefficient
  positivity

/-- The conductor-one error has the same geometric decay as the primitive
character error; only its absolute constant is larger. -/
theorem zetaPointwiseZeroDetectorError_second_scaled_le
    (Al Af Ad j : ℕ) (t eta : ℝ)
    (heta : 0 < eta) (heta8 : eta ≤ 1 / 8) (hj : 1 ≤ j)
    (hlog : 0 ≤ Real.log (|t| + 2)) :
    (2 * eta) ^ j * zetaPointwiseZeroDetectorError Al Af Ad t eta j ≤
      (1 / 2 : ℝ) ^ j *
        zetaPointwiseSecondErrorCoefficient Al Af Ad
          (eta * Real.log (|t| + 2)) := by
  have hgeneric := pointwiseZeroDetectorError_second_scaled_le
    Al Af Ad 1 j t eta heta heta8 hj (by simpa using hlog)
  simp only [Nat.cast_one, one_mul] at hgeneric
  have hratio : (2 * eta) / (4 * eta) = (1 / 2 : ℝ) := by
    field_simp [heta.ne']
    norm_num
  have hextra :
      (2 * eta) ^ j *
          (32 * (Real.log 4 + 4) / (4 * eta) ^ j) =
        (1 / 2 : ℝ) ^ j * (32 * (Real.log 4 + 4)) := by
    calc
      (2 * eta) ^ j *
          (32 * (Real.log 4 + 4) / (4 * eta) ^ j) =
          32 * (Real.log 4 + 4) *
            ((2 * eta) ^ j / (4 * eta) ^ j) := by ring
      _ = 32 * (Real.log 4 + 4) *
            ((2 * eta) / (4 * eta)) ^ j := by rw [div_pow]
      _ = _ := by rw [hratio]; ring
  calc
    (2 * eta) ^ j * zetaPointwiseZeroDetectorError Al Af Ad t eta j =
        (2 * eta) ^ j *
            pointwiseZeroDetectorError Al Af Ad 1 t eta j +
          (2 * eta) ^ j *
            (32 * (Real.log 4 + 4) / (4 * eta) ^ j) := by
      simp only [zetaPointwiseZeroDetectorError,
        pointwiseZeroDetectorError, Nat.cast_one, one_mul]
      ring
    _ ≤ (1 / 2 : ℝ) ^ j *
          pointwiseSecondErrorCoefficient Al Af Ad
            (eta * Real.log (|t| + 2)) +
        (1 / 2 : ℝ) ^ j * (32 * (Real.log 4 + 4)) :=
      add_le_add hgeneric hextra.le
    _ = (1 / 2 : ℝ) ^ j *
        zetaPointwiseSecondErrorCoefficient Al Af Ad
          (eta * Real.log (|t| + 2)) := by
      unfold pointwiseSecondErrorCoefficient
        zetaPointwiseSecondErrorCoefficient
      ring

/-- Integral height governing the variable-order conductor-one detector. -/
noncomputable def zetaVariableDetectorHeight (t eta : ℝ) : ℕ :=
  Nat.ceil (1 + eta * Real.log (|t| + 2))

/-- Every zero of the regularized zeta function in the local disk forces a
large regularized logarithmic derivative at an order linear in logarithmic
height. -/
theorem exists_zeta_variable_pointwise_zero_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
        ∀ (rho₀ : ℂ), riemannZeta₁ rho₀ = 0 →
          dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
          ∀ H : ℕ, zetaVariableDetectorHeight t eta ≤ H →
            let Z := zetaSmallDiskZeroFinsupp t eta
            ∃ j ∈ Finset.Icc (D * H + 1) (D * H + Z.support.card),
              Z.support.card ≤ κ * H ∧
                j ≤ (D + κ) * H ∧
                turanSecondLoss Z.support.card (D * H) *
                    (2 * eta) ^ j ≤ 1 / 32 ∧
                ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
                  turanSecondLoss Z.support.card (D * H) *
                    (2 * eta) ^ j *
                      ‖iteratedDeriv (j - 1)
                        (fun w ↦ -logDeriv riemannZeta₁ w)
                        (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  obtain ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, hdetector⟩ :=
    exists_zeta_pointwise_zero_detector_second_of_error_budget
  obtain ⟨Am', hAm', hmass⟩ := exists_zetaSmallDiskZeroMultiplicity_bound
  let Cmass : ℝ := 48 * (Real.log 4 + 4) + 256 * (Am' : ℝ) / 3
  let κ : ℕ := max 1 (Nat.ceil Cmass)
  let Cerr : ℝ := 96 * (Real.log 4 + 4) +
    (4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) + 64 * (Ad : ℝ) / 3)
  have hCmass : 0 ≤ Cmass := by dsimp [Cmass]; positivity
  have hκ : 1 ≤ κ := le_max_left _ _
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr]; positivity
  obtain ⟨D, hD, hcontract⟩ :=
    exists_turanSecond_contraction_parameter κ Cerr hCerr
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro t eta heta heta8 rho₀ hzero hrho H hHeight
  dsimp only
  let B : ℝ := |t| + 2
  let h : ℝ := eta * Real.log B
  let Z := zetaSmallDiskZeroFinsupp t eta
  let K : ℕ := Z.support.card
  have hB2 : 2 ≤ B := by dsimp [B]; linarith [abs_nonneg t]
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hceilLocal : 1 + h ≤ (zetaVariableDetectorHeight t eta : ℝ) := by
    simpa only [zetaVariableDetectorHeight, h, B] using
      (Nat.le_ceil (1 + h))
  have hHeightCast :
      (zetaVariableDetectorHeight t eta : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast hHeight
  have hceil : 1 + h ≤ (H : ℝ) := hceilLocal.trans hHeightCast
  have hHcast : (1 : ℝ) ≤ H := by linarith
  have hH : 1 ≤ H := by exact_mod_cast hHcast
  have hhH : h ≤ (H : ℝ) := by linarith
  have hmass' := hmass t eta heta (by linarith : eta ≤ 1)
  have hmassC : Z.sum (fun _ m ↦ (m : ℝ)) ≤ Cmass * H := by
    have hsecond :
        (256 * (Am' : ℝ) / 3) * eta * Real.log B ≤
          (256 * (Am' : ℝ) / 3) * H := by
      calc
        (256 * (Am' : ℝ) / 3) * eta * Real.log B =
            (256 * (Am' : ℝ) / 3) * h := by simp only [h]; ring
        _ ≤ (256 * (Am' : ℝ) / 3) * H := by gcongr
    calc
      Z.sum (fun _ m ↦ (m : ℝ)) ≤
          48 * (Real.log 4 + 4) +
            (256 * (Am' : ℝ) / 3) * eta * Real.log B := by
        simpa only [Z, B] using hmass'
      _ ≤ 48 * (Real.log 4 + 4) +
            (256 * (Am' : ℝ) / 3) * H := by linarith
      _ ≤ Cmass * H := by
        dsimp [Cmass]
        have hbase : (0 : ℝ) ≤ 48 * (Real.log 4 + 4) := by positivity
        nlinarith
  have hcardMass : (K : ℝ) ≤ Z.sum (fun _ m ↦ (m : ℝ)) := by
    have hnat := finsupp_support_card_le_sum_nat Z
    exact_mod_cast hnat
  have hCmassκ : Cmass ≤ (κ : ℝ) := by
    exact (Nat.le_ceil Cmass).trans (by
      exact_mod_cast (le_max_right 1 (Nat.ceil Cmass)))
  have hKcast : (K : ℝ) ≤ (κ * H : ℕ) := by
    calc
      (K : ℝ) ≤ Z.sum (fun _ m ↦ (m : ℝ)) := hcardMass
      _ ≤ Cmass * H := hmassC
      _ ≤ (κ : ℝ) * H := mul_le_mul_of_nonneg_right hCmassκ (by positivity)
      _ = (κ * H : ℕ) := by norm_cast
  have hKκ : K ≤ κ * H := by exact_mod_cast hKcast
  have horderNe : analyticOrderNatAt riemannZeta₁ rho₀ ≠ 0 := by
    have hsupp : rho₀ ∈
        (MeromorphicOn.divisor riemannZeta₁ Set.univ).support :=
      (mem_support_divisor_riemannZeta₁_iff (Set.mem_univ rho₀)).2 hzero
    rw [Function.mem_support,
      divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
        (Set.mem_univ rho₀)] at hsupp
    exact_mod_cast hsupp
  have horder : 0 < analyticOrderNatAt riemannZeta₁ rho₀ :=
    Nat.pos_of_ne_zero horderNe
  have hZrho₀ : Z rho₀ ≠ 0 := by
    dsimp [Z]
    rw [zetaSmallDiskZeroMultiplicity,
      if_pos (hrho.trans (by linarith : 2 * eta ≤ 4 * eta))]
    exact horder.ne'
  have hK : 1 ≤ K := by
    dsimp [K]
    exact Finset.card_pos.mpr ⟨rho₀, Finsupp.mem_support_iff.mpr hZrho₀⟩
  have hcoeff :
      zetaPointwiseSecondErrorCoefficient Al Af Ad h ≤ Cerr * H := by
    unfold zetaPointwiseSecondErrorCoefficient
    dsimp [Cerr]
    have hconst : 0 ≤ 96 * (Real.log 4 + 4) := by positivity
    have hslope : 0 ≤ 4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) +
        64 * (Ad : ℝ) / 3 := by positivity
    nlinarith
  have hCerrH : (8 : ℝ) ≤ Cerr * H := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
    dsimp [Cerr]
    have htailNonneg :
        0 ≤ 4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) +
          64 * (Ad : ℝ) / 3 := by positivity
    nlinarith [mul_nonneg htailNonneg (show (0 : ℝ) ≤ H by positivity)]
  have hbudget :
      ∀ j ∈ Finset.Icc (D * H + 1) (D * H + K),
        turanSecondLoss K (D * H) * (2 * eta) ^ j *
          zetaPointwiseZeroDetectorError Al Af Ad t eta j ≤ 1 / 4 := by
    intro j hj
    have hjPos : 1 ≤ j :=
      (Nat.succ_le_succ (Nat.zero_le (D * H))).trans
        (Finset.mem_Icc.mp hj).1
    have hscaled := zetaPointwiseZeroDetectorError_second_scaled_le
      Al Af Ad j t eta heta heta8 hjPos (by simpa only [B] using hlog)
    have hlossNonneg : 0 ≤ turanSecondLoss K (D * H) :=
      (turanSecondLoss_pos (by omega : 0 < K)).le
    calc
      turanSecondLoss K (D * H) * (2 * eta) ^ j *
          zetaPointwiseZeroDetectorError Al Af Ad t eta j =
          turanSecondLoss K (D * H) *
            ((2 * eta) ^ j *
              zetaPointwiseZeroDetectorError Al Af Ad t eta j) := by ring
      _ ≤ turanSecondLoss K (D * H) *
          ((1 / 2 : ℝ) ^ j *
            zetaPointwiseSecondErrorCoefficient Al Af Ad h) := by gcongr
      _ ≤ turanSecondLoss K (D * H) *
          ((1 / 2 : ℝ) ^ j * (Cerr * H)) := by gcongr
      _ = turanSecondLoss K (D * H) * (1 / 2 : ℝ) ^ j *
          (Cerr * H) := by ring
      _ ≤ 1 / 4 := hcontract H K j hH hK hKκ (Finset.mem_Icc.mp hj).1
  obtain ⟨j, hj, hjlarge⟩ :=
    hdetector t eta heta heta8 rho₀ hzero hrho
      (D * H) (Nat.mul_pos (by omega) (by omega))
        (by simpa only [K, Z] using hbudget)
  refine ⟨j, by simpa only [Z, K] using hj,
    by simpa only [Z, K] using hKκ, ?_, ?_, ?_⟩
  · have hjupper := (Finset.mem_Icc.mp hj).2
    calc
      j ≤ D * H + K := hjupper
      _ ≤ D * H + κ * H := Nat.add_le_add_left hKκ _
      _ = (D + κ) * H := by rw [add_mul]
  · have hjPos : 1 ≤ j :=
      (Nat.succ_le_succ (Nat.zero_le (D * H))).trans
        (Finset.mem_Icc.mp hj).1
    have htwoeta : 0 ≤ 2 * eta := by positivity
    have htwoetaHalf : 2 * eta ≤ (1 / 2 : ℝ) := by linarith
    have hpow : (2 * eta) ^ j ≤ (1 / 2 : ℝ) ^ j :=
      pow_le_pow_left₀ htwoeta htwoetaHalf j
    have hlossNonneg : 0 ≤ turanSecondLoss K (D * H) :=
      (turanSecondLoss_pos (by omega : 0 < K)).le
    have hscaledContract :
        turanSecondLoss K (D * H) * (2 * eta) ^ j *
            (Cerr * H) ≤ 1 / 4 := by
      calc
        turanSecondLoss K (D * H) * (2 * eta) ^ j * (Cerr * H) ≤
            turanSecondLoss K (D * H) * (1 / 2 : ℝ) ^ j *
              (Cerr * H) := by gcongr
        _ ≤ 1 / 4 :=
          hcontract H K j hH hK hKκ (Finset.mem_Icc.mp hj).1
    have hscaleNonneg :
        0 ≤ turanSecondLoss K (D * H) * (2 * eta) ^ j := by
      positivity
    have hscale8 :
        (turanSecondLoss K (D * H) * (2 * eta) ^ j) * 8 ≤ 1 / 4 :=
      calc
        (turanSecondLoss K (D * H) * (2 * eta) ^ j) * 8 ≤
            (turanSecondLoss K (D * H) * (2 * eta) ^ j) *
              (Cerr * H) := by gcongr
        _ ≤ 1 / 4 := by simpa only [mul_assoc] using hscaledContract
    nlinarith
  · simpa only [Z, K] using hjlarge

/-- Away from the pole, removing the regularization costs at most one
thirty-second of the factorial once the Turán scale is normalized. -/
theorem zeta_scaled_regularized_derivative_to_weightedLSeries
    {j : ℕ} {t eta X : ℝ}
    (hj2 : 2 ≤ j) (ht : 1 ≤ |t|) (heta : 0 < eta)
    (hX0 : 0 ≤ X) (hX : X ≤ 1 / 32)
    (hlarge :
      ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
        X * ‖iteratedDeriv (j - 1)
          (fun w ↦ -logDeriv riemannZeta₁ w)
          (((1 + eta : ℝ) : ℂ) + t * I)‖) :
    ((j - 1).factorial : ℝ) * (15 / 32 : ℝ) <
      X * ‖LSeries (fun n : ℕ ↦
          (Real.log n : ℂ) ^ (j - 1) *
            (1 : DirichletCharacter ℂ 1) n *
            (ArithmeticFunction.vonMangoldt n : ℂ))
        (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let k : ℕ := j - 1
  have hzre : z.re = 1 + eta := by simp [z]
  have hz1 : 1 < z.re := by rw [hzre]; linarith
  have hzOne : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hzeta : riemannZeta z ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hz1.le
  have hzeta₁ : riemannZeta₁ z ≠ 0 := by
    intro hzero₁
    have hfactor := riemannZeta_eq_inv_sub_mul hzOne
    rw [hzero₁, mul_zero] at hfactor
    exact hzeta hfactor
  let U : Set ℂ := {w | 1 < w.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have heq : Set.EqOn
      (fun w : ℂ ↦ -logDeriv riemannZeta w)
      (fun w : ℂ ↦ (w - 1)⁻¹ + (-logDeriv riemannZeta₁ w)) U := by
    intro w hw
    change 1 < w.re at hw
    have hwOne : w ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hwzeta : riemannZeta w ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hw.le
    simpa [sub_eq_add_neg] using
      neg_logDeriv_riemannZeta_eq_pole_sub_regularized_of_ne_zero
        w hwOne hwzeta
  have hderivEq := heq.iteratedDeriv_of_isOpen hUopen k hz1
  have hpoleAnalytic : AnalyticAt ℂ (fun w : ℂ ↦ (w - 1)⁻¹) z :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzOne)
  have hregAnalytic : AnalyticAt ℂ
      (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z := by
    have hf := differentiable_riemannZeta₁.analyticAt z
    have hlog : AnalyticAt ℂ (logDeriv riemannZeta₁) z := by
      simpa [logDeriv] using hf.deriv.div hf hzeta₁
    have hlog' : AnalyticAt ℂ
        (fun w : ℂ ↦ logDeriv riemannZeta₁ w) z := by
      simpa only using hlog
    exact hlog'.neg
  have hadd :
      iteratedDeriv k
          (fun w : ℂ ↦ (w - 1)⁻¹ + (-logDeriv riemannZeta₁ w)) z =
        iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z +
          iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z := by
    exact iteratedDeriv_add hpoleAnalytic.contDiffAt hregAnalytic.contDiffAt
  rw [hadd] at hderivEq
  have hregEq :
      iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z =
        iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta w) z -
          iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z := by
    rw [hderivEq]
    ring
  have hpoleFormula :
      iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z =
        (-1 : ℂ) ^ k * k.factorial *
          (z - 1) ^ (-1 - (k : ℤ)) := by
    have hinv := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1
    simp only [one_mul, one_pow] at hinv
    simpa [iteratedDeriv_eq_iterate] using congrFun (hinv (1 : ℂ)) z
  have hnormz : 1 ≤ ‖z - 1‖ := by
    calc
      1 ≤ |t| := ht
      _ = |(z - 1).im| := by simp [z]
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hzpow : ‖(z - 1) ^ (-1 - (k : ℤ))‖ ≤ 1 := by
    have hexp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast, norm_inv, norm_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hnormz)
  have hpoleNorm :
      ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ ≤ k.factorial := by
    rw [hpoleFormula, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_natCast]
    simpa only [Nat.cast_nonneg] using
      mul_le_of_le_one_right (Nat.cast_nonneg k.factorial) hzpow
  have htri :
      ‖iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z‖ ≤
        ‖iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta w) z‖ +
          ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ := by
    rw [hregEq]
    exact norm_sub_le _ _
  have hpoleScaled :
      X * ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ ≤
        ((j - 1).factorial : ℝ) * (1 / 32 : ℝ) := by
    have hfac :
        ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ ≤
          ((j - 1).factorial : ℝ) := by simpa only [k] using hpoleNorm
    calc
      X * ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ ≤
          X * ((j - 1).factorial : ℝ) := by gcongr
      _ ≤ (1 / 32 : ℝ) * ((j - 1).factorial : ℝ) := by gcongr
      _ = ((j - 1).factorial : ℝ) * (1 / 32 : ℝ) := by ring
  have htriScaled := mul_le_mul_of_nonneg_left htri hX0
  have hzetalarge :
      ((j - 1).factorial : ℝ) * (15 / 32 : ℝ) <
        X * ‖iteratedDeriv (j - 1)
          (fun w : ℂ ↦ -logDeriv riemannZeta w) z‖ := by
    simpa only [k] using (show
      ((j - 1).factorial : ℝ) * (15 / 32 : ℝ) <
        X * ‖iteratedDeriv k
          (fun w : ℂ ↦ -logDeriv riemannZeta w) z‖ by
      nlinarith)
  have hseries :=
    iteratedDeriv_neg_logDeriv_LFunction_eq_weighted_LSeries
      (k := j - 1) (1 : DirichletCharacter ℂ 1) hz1
  rw [DirichletCharacter.LFunction_modOne_eq] at hseries
  rw [hseries] at hzetalarge
  simpa only [z, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul] using hzetalarge

/-- Variable-order conductor-one detector after truncation to a finite
weighted von Mangoldt polynomial. -/
theorem exists_zeta_variable_finite_series_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (t eta : ℝ), 1 ≤ |t| → 0 < eta → eta ≤ 1 / 8 →
        ∀ (rho₀ : ℂ), riemannZeta₁ rho₀ = 0 →
          dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
          ∀ H J : ℕ, zetaVariableDetectorHeight t eta ≤ H →
          (D + κ) * H ≤ J →
            let Z := zetaSmallDiskZeroFinsupp t eta
            let K := Z.support.card
            let M := D * H
            let R := variableZeroDetectorTailRadius J
            let N := zeroDetectorCutoff R eta
            ∃ j ∈ Finset.Icc (M + 1) (M + K),
              K ≤ κ * H ∧ j ≤ J ∧
                ((j - 1).factorial : ℝ) * (7 / 32 : ℝ) <
                  turanSecondLoss K M * (2 * eta) ^ j *
                    ‖∑ n ∈ Finset.Icc 1 N,
                      LSeries.term (fun m : ℕ ↦
                        (Real.log m : ℂ) ^ (j - 1) *
                          (1 : DirichletCharacter ℂ 1) m *
                          (ArithmeticFunction.vonMangoldt m : ℂ))
                        (((1 + eta : ℝ) : ℂ) + t * I) n‖ := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_zeta_variable_pointwise_zero_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro t eta ht heta heta8 rho₀ hzero hrho H J hHeight hJ
  dsimp only
  let Z := zetaSmallDiskZeroFinsupp t eta
  let K := Z.support.card
  let M := D * H
  let R := variableZeroDetectorTailRadius J
  let N := zeroDetectorCutoff R eta
  obtain ⟨j, hj, hKκ, hjBound, hscaleBound, hjfullDeriv⟩ :=
    hdetector t eta heta heta8 rho₀ hzero hrho H hHeight
  have hjJ : j ≤ J := hjBound.trans hJ
  have hjLocal : j ∈ Finset.Icc (M + 1) (M + K) := by
    simpa only [Z, K, M] using hj
  have hK : 1 ≤ K := by
    have hjLower := (Finset.mem_Icc.mp hjLocal).1
    have hjUpper := (Finset.mem_Icc.mp hjLocal).2
    omega
  have hjPos : 1 ≤ j :=
    (Nat.succ_le_succ (Nat.zero_le M)).trans
      (Finset.mem_Icc.mp hjLocal).1
  have hj2 : 2 ≤ j := by
    have hHpos : 1 ≤ H := by
      have hheightPos : 1 ≤ zetaVariableDetectorHeight t eta := by
        have hlog : 0 ≤ Real.log (|t| + 2) :=
          Real.log_nonneg (by linarith [abs_nonneg t])
        have hcast : (1 : ℝ) ≤ zetaVariableDetectorHeight t eta := by
          exact (by nlinarith [mul_nonneg heta.le hlog] :
              (1 : ℝ) ≤ 1 + eta * Real.log (|t| + 2)).trans
            (by simpa only [zetaVariableDetectorHeight] using
              Nat.le_ceil (1 + eta * Real.log (|t| + 2)))
        exact_mod_cast hcast
      exact hheightPos.trans hHeight
    have hMpos : 1 ≤ M := by
      dsimp [M]
      exact Nat.mul_pos (by omega) hHpos
    have htwoM : 2 ≤ M + 1 := Nat.succ_le_succ hMpos
    exact htwoM.trans (Finset.mem_Icc.mp hjLocal).1
  let X : ℝ := turanSecondLoss K M * (2 * eta) ^ j
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
      (by positivity)
  have hX : X ≤ 1 / 32 := by
    simpa only [X, Z, K, M] using hscaleBound
  have hweighted :
      ((j - 1).factorial : ℝ) * (15 / 32 : ℝ) <
        X * ‖LSeries (fun n : ℕ ↦
            (Real.log n : ℂ) ^ (j - 1) *
              (1 : DirichletCharacter ℂ 1) n *
              (ArithmeticFunction.vonMangoldt n : ℂ))
          (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
    apply zeta_scaled_regularized_derivative_to_weightedLSeries
      hj2 ht heta hX0 hX
    simpa only [X, Z, K, M] using hjfullDeriv
  let chi : DirichletCharacter ℂ 1 := 1
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let c : ℕ → ℂ := fun m ↦
    (Real.log m : ℂ) ^ (j - 1) * chi m *
      (ArithmeticFunction.vonMangoldt m : ℂ)
  let P : ℂ := ∑ n ∈ Finset.Icc 1 N, LSeries.term c z n
  have hNpos : 0 < N := by
    simpa only [N] using zeroDetectorCutoff_pos R eta
  have hNexp : Real.exp (R / eta) ≤ (N : ℝ) := by
    simpa only [N] using exp_div_le_zeroDetectorCutoff R eta
  have htailRaw := norm_weighted_vonMangoldt_LSeries_sub_sum_le
    chi eta R t heta (by linarith : eta ≤ 1) N (j - 1)
      hNpos hNexp
  have hKJ : K ≤ J := by
    have hKH : K ≤ κ * H := by simpa only [Z, K] using hKκ
    exact hKH.trans (by
      calc
        κ * H ≤ (D + κ) * H := by gcongr <;> omega
        _ ≤ J := hJ)
  have hMJ : M ≤ J := by
    dsimp [M]
    calc
      D * H ≤ (D + κ) * H := by gcongr <;> omega
      _ ≤ J := hJ
  have htailBudget := variable_weighted_vonMangoldt_tail_budget
    hK hKJ hMJ hjJ hjPos heta (by linarith : eta ≤ 1)
  have htailScaled : X * ‖LSeries c z - P‖ ≤
      ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left htailRaw hX0).trans
      (by simpa only [X, R, c, z, N, P] using htailBudget)
  have hfull :
      ((j - 1).factorial : ℝ) * (15 / 32 : ℝ) <
        X * ‖LSeries c z‖ := by
    simpa only [chi, c, z] using hweighted
  have htri : ‖LSeries c z‖ ≤ ‖P‖ + ‖LSeries c z - P‖ := by
    calc
      ‖LSeries c z‖ = ‖P + (LSeries c z - P)‖ := by congr 1; ring
      _ ≤ ‖P‖ + ‖LSeries c z - P‖ := norm_add_le _ _
  refine ⟨j, by simpa only [Z, K, M] using hj,
    by simpa only [Z, K] using hKκ, hjJ, ?_⟩
  have hscaledTri := mul_le_mul_of_nonneg_left htri hX0
  change ((j - 1).factorial : ℝ) * (7 / 32 : ℝ) < X * ‖P‖
  nlinarith

/-- The variable conductor-one detector remains large on its natural short
interval around the detected ordinate. -/
theorem exists_zeta_variable_propagated_finite_series_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (t eta : ℝ), 1 ≤ |t| → 0 < eta → eta ≤ 1 / 8 →
        ∀ (rho₀ : ℂ), riemannZeta₁ rho₀ = 0 →
          dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
          ∀ H J : ℕ, zetaVariableDetectorHeight t eta ≤ H →
            (D + κ) * H ≤ J →
            let Z := zetaSmallDiskZeroFinsupp t eta
            let K := Z.support.card
            let M := D * H
            let R := variableZeroDetectorTailRadius J
            let N := zeroDetectorCutoff R eta
            ∃ j ∈ Finset.Icc (M + 1) (M + K),
              K ≤ κ * H ∧ j ≤ J ∧
                ∀ u : ℝ,
                  |u - t| ≤ variableDetectorPropagationRadius J * eta →
                  ((j - 1).factorial : ℝ) * (3 / 32 : ℝ) <
                    turanSecondLoss K M * (2 * eta) ^ j *
                      ‖finiteZeroDetectorPolynomial
                        (1 : DirichletCharacter ℂ 1)
                        eta (j - 1) N u‖ := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_zeta_variable_finite_series_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro t eta ht heta heta8 rho₀ hzero hrho H J hHeight hJ
  dsimp only
  let chi : DirichletCharacter ℂ 1 := 1
  let Z := zetaSmallDiskZeroFinsupp t eta
  let K := Z.support.card
  let M := D * H
  let R := variableZeroDetectorTailRadius J
  let N := zeroDetectorCutoff R eta
  obtain ⟨j, hj, hKκ, hjJ, hjlarge⟩ :=
    hdetector t eta ht heta heta8 rho₀ hzero hrho H J hHeight hJ
  have hjLocal : j ∈ Finset.Icc (M + 1) (M + K) := by
    simpa only [Z, K, M] using hj
  have hK : 1 ≤ K := by
    have hlower := (Finset.mem_Icc.mp hjLocal).1
    have hupper := (Finset.mem_Icc.mp hjLocal).2
    omega
  have hjPos : 1 ≤ j :=
    (Nat.succ_le_succ (Nat.zero_le M)).trans
      (Finset.mem_Icc.mp hjLocal).1
  have hKH : K ≤ κ * H := by simpa only [Z, K] using hKκ
  have hKJ : K ≤ J := hKH.trans <| by
    calc
      κ * H ≤ (D + κ) * H := by gcongr <;> omega
      _ ≤ J := hJ
  have hMJ : M ≤ J := by
    dsimp [M]
    calc
      D * H ≤ (D + κ) * H := by gcongr <;> omega
      _ ≤ J := hJ
  let P : ℝ → ℂ := fun u ↦
    finiteZeroDetectorPolynomial chi eta (j - 1) N u
  have htlarge : ((j - 1).factorial : ℝ) * (7 / 32 : ℝ) <
      turanSecondLoss K M * (2 * eta) ^ j * ‖P t‖ := by
    rw [show P t =
        ∑ n ∈ Finset.Icc 1 N,
          LSeries.term (fun m : ℕ ↦
            (Real.log m : ℂ) ^ (j - 1) * chi m *
              (ArithmeticFunction.vonMangoldt m : ℂ))
            (((1 + eta : ℝ) : ℂ) + t * I) n by
      dsimp [P]
      exact (weighted_vonMangoldt_LSeries_sum_eq_polynomial
        chi eta t (j - 1) N).symm]
    simpa only [chi, R, N, Z, K, M] using hjlarge
  refine ⟨j, by simpa only [Z, K, M] using hj, hKH, hjJ, ?_⟩
  intro u hu
  have heta1 : eta ≤ 1 := by linarith
  have hsum := weightedVonMangoldtMajorant_tsum_le eta heta heta1 j
  have hsum0 : 0 ≤ ∑' n, weightedVonMangoldtMajorant eta j n :=
    tsum_nonneg fun n ↦ by unfold weightedVonMangoldtMajorant; positivity
  have htu : |t - u| ≤ variableDetectorPropagationRadius J * eta := by
    simpa only [abs_sub_comm] using hu
  have hlip := norm_finiteZeroDetectorPolynomial_sub_le_tsum
    chi eta heta (j - 1) N t u
  have hlip' :
      ‖P t - P u‖ ≤ |t - u| *
        ∑' n, weightedVonMangoldtMajorant eta j n := by
    simpa only [P, show j - 1 + 1 = j by omega] using hlip
  have hdiffScaled :
      turanSecondLoss K M * (2 * eta) ^ j * ‖P t - P u‖ ≤
        ((j - 1).factorial : ℝ) * (1 / 8 : ℝ) := by
    have hlipBudget : ‖P t - P u‖ ≤
        variableDetectorPropagationRadius J * eta *
          (3 * (Real.log 4 + 4) * j.factorial *
            (2 / eta) ^ j / eta) :=
      hlip'.trans (mul_le_mul htu hsum hsum0
        (mul_nonneg (variableDetectorPropagationRadius_pos
          (hjPos.trans hjJ)).le heta.le))
    exact (mul_le_mul_of_nonneg_left hlipBudget
      (mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
        (by positivity))).trans
      (variable_detector_propagation_budget hK hKJ hMJ hjPos hjJ heta)
  have htri : ‖P t‖ ≤ ‖P u‖ + ‖P t - P u‖ := by
    calc
      ‖P t‖ = ‖P u + (P t - P u)‖ := by congr 1; ring
      _ ≤ ‖P u‖ + ‖P t - P u‖ := norm_add_le _ _
  have hscale : 0 ≤ turanSecondLoss K M * (2 * eta) ^ j :=
    mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
      (by positivity)
  have hscaledTri := mul_le_mul_of_nonneg_left htri hscale
  dsimp only [P, chi] at htlarge hscaledTri ⊢
  nlinarith

/-- The propagated conductor-one detector may be restricted to its long
band while retaining an explicit positive normalized lower bound. -/
theorem exists_zeta_variable_propagated_band_series_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (t eta : ℝ), 1 ≤ |t| → 0 < eta → eta ≤ 1 / 8 →
        ∀ (rho₀ : ℂ), riemannZeta₁ rho₀ = 0 →
          dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
          ∀ H J : ℕ, zetaVariableDetectorHeight t eta ≤ H →
            (D + κ) * H ≤ J →
            let E := D + κ
            let Z := zetaSmallDiskZeroFinsupp t eta
            let K := Z.support.card
            let M := D * H
            let R := variableZeroDetectorTailRadius J
            let N := zeroDetectorCutoff R eta
            ∃ j ∈ Finset.Icc (M + 1) (M + K),
              K ≤ κ * H ∧ j ≤ J ∧
              variableDetectorLowerCutoff E eta j ≤ N ∧
                ∀ u : ℝ,
                  |u - t| ≤ variableDetectorPropagationRadius J * eta →
                  ((j - 1).factorial : ℝ) / 32 <
                    turanSecondLoss K M * (2 * eta) ^ j *
                      ‖variableBandZeroDetectorPolynomial
                        (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_zeta_variable_propagated_finite_series_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro t eta ht heta heta8 rho₀ hzero hrho H J hHeight hJ
  dsimp only
  let chi : DirichletCharacter ℂ 1 := 1
  let E := D + κ
  let Z := zetaSmallDiskZeroFinsupp t eta
  let K := Z.support.card
  let M := D * H
  let R := variableZeroDetectorTailRadius J
  let N := zeroDetectorCutoff R eta
  obtain ⟨j, hjLocal, hKH, hjJ, hjlarge⟩ :=
    hdetector t eta ht heta heta8 rho₀ hzero hrho H J hHeight hJ
  have hheightOne : 1 ≤ zetaVariableDetectorHeight t eta := by
    have hlog : 0 ≤ Real.log (|t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    have hcast : (1 : ℝ) ≤ zetaVariableDetectorHeight t eta := by
      exact (by nlinarith [mul_nonneg heta.le hlog] :
          (1 : ℝ) ≤ 1 + eta * Real.log (|t| + 2)).trans
        (by simpa only [zetaVariableDetectorHeight] using
          Nat.le_ceil (1 + eta * Real.log (|t| + 2)))
    exact_mod_cast hcast
  have hH : 1 ≤ H := hheightOne.trans hHeight
  have hK : 1 ≤ K := by
    have hjLower := (Finset.mem_Icc.mp hjLocal).1
    have hjUpper := (Finset.mem_Icc.mp hjLocal).2
    have hMK : M + 1 ≤ M + K := hjLower.trans hjUpper
    exact Nat.add_le_add_iff_left.mp hMK
  have hjTwo : 2 ≤ j := by
    have hjLower := (Finset.mem_Icc.mp hjLocal).1
    have hDH : 1 ≤ D * H := Nat.mul_pos (by omega) (by omega)
    omega
  have hHj : H ≤ j - 1 := by
    have hHDH : H ≤ D * H := by
      simpa only [one_mul] using Nat.mul_le_mul_right H hD
    have hDHj : D * H ≤ j - 1 := by
      have hjLower := (Finset.mem_Icc.mp hjLocal).1
      omega
    exact hHDH.trans hDHj
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hKloss : K ≤ E * (j - 1) := by
    calc
      K ≤ κ * H := hKH
      _ ≤ κ * (j - 1) := Nat.mul_le_mul_left κ hHj
      _ ≤ E * (j - 1) := by
        apply Nat.mul_le_mul_right
        dsimp [E]
        omega
  have hMloss : M ≤ E * (j - 1) := by
    dsimp [M, E]
    calc
      D * H ≤ D * (j - 1) := Nat.mul_le_mul_left D hHj
      _ ≤ (D + κ) * (j - 1) := by gcongr <;> omega
  have hcut : variableDetectorLowerCutoff E eta j ≤ N := by
    simpa only [N, R] using
      variableDetectorLowerCutoff_le_zeroDetectorCutoff
        (E := E) hjJ heta
  refine ⟨j, by simpa only [Z, K, M] using hjLocal,
    by simpa only [Z, K] using hKH, hjJ, hcut, ?_⟩
  intro u hu
  have hfull := hjlarge u hu
  let lowPart : ℂ :=
    ∑ n ∈ Finset.Icc 1 (variableDetectorLowerCutoff E eta j),
      (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
        Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))
  have hprefixNorm :
      turanSecondLoss K M * (2 * eta) ^ j * ‖lowPart‖ ≤
        ((j - 1).factorial : ℝ) / 16 := by
    calc
      turanSecondLoss K M * (2 * eta) ^ j * ‖lowPart‖ ≤
          turanSecondLoss K M * (2 * eta) ^ j *
            (∑ n ∈ Finset.Icc 1
                (variableDetectorLowerCutoff E eta j),
              weightedVonMangoldtMajorant eta (j - 1) n) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_variable_detector_prefix_le_majorant
            chi eta (j - 1) (variableDetectorLowerLog E eta j) u
        · exact mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
            (by positivity)
      _ ≤ ((j - 1).factorial : ℝ) / 16 :=
        variable_detector_prefix_small hE hK hjTwo
          hKloss hMloss le_rfl heta
  have hdecomp := full_variable_detector_eq_prefix_add_band
    chi E eta j N u hcut
  have htriangle :
      ‖finiteZeroDetectorPolynomial chi eta (j - 1) N u‖ ≤
        ‖lowPart‖ +
          ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ := by
    rw [hdecomp]
    simpa only [lowPart] using
      norm_add_le lowPart
        (variableBandZeroDetectorPolynomial chi E eta j N u)
  have hscale : 0 ≤ turanSecondLoss K M * (2 * eta) ^ j :=
    mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
      (by positivity)
  have hscaledTriangle := mul_le_mul_of_nonneg_left htriangle hscale
  nlinarith

/-- A maximal separated family of conductor-one zero ordinates, labelled by
the variable detector order and normalized for the mean-square estimate. -/
theorem exists_zeta_variable_detected_zero_selection :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (T : ℕ), 1 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := 2 * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
            S ⊆ zetaHighZeroOrdinates eta T ∧
            (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
              2 * delta * eta < dist x y) ∧
            (∀ x ∈ zetaHighZeroOrdinates eta T,
              ∃ y ∈ S, dist x y ≤ 2 * delta * eta) ∧
            (∀ t ∈ S,
              D * H + 1 ≤ order t ∧ order t ≤ J ∧
              zeroDetectorLowerCutoff B ≤
                variableDetectorLowerCutoff E eta (order t) ∧
              variableDetectorLowerCutoff E eta (order t) ≤ N ∧
              ∀ u : ℝ, |u - t| ≤ delta * eta →
                ((order t - 1).factorial : ℝ) / 32 <
                    ((578 : ℝ) ^ J / 2) * (2 * eta) ^ (order t) *
                      ‖variableBandZeroDetectorPolynomial
                        (1 : DirichletCharacter ℂ 1) E eta
                        (order t) N u‖ ∧
                1 / (16 * (578 : ℝ) ^ J) <
                    ‖variableBandZeroDetectorPolynomial
                      (1 : DirichletCharacter ℂ 1) E eta
                      (order t) N u‖) := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_zeta_variable_propagated_band_series_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  have hB : (1 : ℝ) ≤ B := by
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [B]
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact Nat.mul_pos (by omega) (by omega)
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJpos
  have hdelta1 : delta ≤ 1 := by
    simpa only [delta] using variableDetectorPropagationRadius_le_one hJpos
  obtain ⟨S, hSsub, hsep, hcover⟩ :=
    exists_separated_zetaHighZeroOrdinates eta T
      (2 * delta * eta) (by positivity)
  have hdata : ∀ t ∈ S, ∃ j : ℕ,
      D * H + 1 ≤ j ∧ j ≤ J ∧
      zeroDetectorLowerCutoff B ≤ variableDetectorLowerCutoff E eta j ∧
      variableDetectorLowerCutoff E eta j ≤ N ∧
      ∀ u : ℝ, |u - t| ≤ delta * eta →
        ((j - 1).factorial : ℝ) / 32 <
            ((578 : ℝ) ^ J / 2) * (2 * eta) ^ j *
              ‖variableBandZeroDetectorPolynomial
                (1 : DirichletCharacter ℂ 1) E eta j N u‖ ∧
        1 / (16 * (578 : ℝ) ^ J) <
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
    intro t ht
    have htOrd := hSsub ht
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht1, htT⟩ :=
      (mem_zetaHighZeroOrdinates_iff (by linarith) (by exact_mod_cast hT) t).mp
        htOrd
    have hinside : (0 : ℝ) < |t| + 2 := by positivity
    have hprod : |t| + 2 ≤ B := by
      rw [abs_of_nonneg (by linarith : 0 ≤ t)]
      dsimp [B]
      have htTR : t ≤ (T : ℝ) := by simpa only using htT
      nlinarith
    have hlog : Real.log (|t| + 2) ≤ Real.log B :=
      Real.log_le_log hinside hprod
    have hheight₀ : zetaVariableDetectorHeight t eta ≤ H₀ := by
      unfold zetaVariableDetectorHeight
      dsimp [H₀]
      apply Nat.ceil_mono
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hlog heta.le) 1
    have hheight : zetaVariableDetectorHeight t eta ≤ H := by
      exact hheight₀.trans <| by
        dsimp [H]
        calc
          H₀ = 1 * H₀ := by omega
          _ ≤ variableDetectorHeightDilation E * H₀ :=
            Nat.mul_le_mul_right H₀
              (variableDetectorHeightDilation_pos E).nat_succ_le
    have htAbs : 1 ≤ |t| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ t)]
      exact ht1
    have hrho : dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta :=
      highZero_dist_variable_detector_center_le hrelo hrehi hrhoim heta
    obtain ⟨j, hj, hKH, hjJ, hcut, hlarge⟩ :=
      hdetector t eta htAbs heta heta8 rho hzero hrho
        H J hheight (by exact le_rfl)
    let Z := zetaSmallDiskZeroFinsupp t eta
    let K := Z.support.card
    let M := D * H
    have hjLocal : j ∈ Finset.Icc (M + 1) (M + K) := by
      simpa only [Z, K, M] using hj
    have hK : 1 ≤ K := by
      have hMK : M + 1 ≤ M + K :=
        (Finset.mem_Icc.mp hjLocal).1.trans (Finset.mem_Icc.mp hjLocal).2
      exact Nat.add_le_add_iff_left.mp hMK
    have hKJ : K ≤ J := by
      calc
        K ≤ κ * H := by simpa only [Z, K] using hKH
        _ ≤ (D + κ) * H := by gcongr <;> omega
        _ = J := by rfl
    have hMJ : M ≤ J := by
      dsimp [M, J]
      gcongr <;> omega
    have hloss := turanSecondLoss_le_orderEnvelope hK hKJ hMJ
    have hpow : (2 * eta) ^ j ≤ (1 : ℝ) :=
      pow_le_one₀ (by positivity) (by linarith)
    have hscale : turanSecondLoss K M * (2 * eta) ^ j ≤
        (578 : ℝ) ^ J / 2 := by
      calc
        turanSecondLoss K M * (2 * eta) ^ j ≤
            ((578 : ℝ) ^ J / 2) * 1 := by gcongr
        _ = (578 : ℝ) ^ J / 2 := mul_one _
    have hfac : (1 : ℝ) ≤ (j - 1).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hfixedCut := zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
      (D := D) (E := E) (H₀ := H₀) (H := H) (j := j)
      (B := B) (eta := eta) hD hB heta le_rfl le_rfl
        (Finset.mem_Icc.mp hjLocal).1
    refine ⟨j, (Finset.mem_Icc.mp hjLocal).1, hjJ,
      hfixedCut, hcut, ?_⟩
    intro u hu
    have hlargeU := hlarge u (by simpa only [delta] using hu)
    have hscaledLoss :
        turanSecondLoss K M * (2 * eta) ^ j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ ≤
          ((578 : ℝ) ^ J / 2) * (2 * eta) ^ j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
      gcongr
    have hscaledUpper := mul_le_mul_of_nonneg_right hscale
      (norm_nonneg (variableBandZeroDetectorPolynomial
        (1 : DirichletCharacter ℂ 1) E eta j N u))
    have hfacDiv : (1 / 32 : ℝ) ≤
        ((j - 1).factorial : ℝ) / 32 := by nlinarith
    have hmid : (1 / 32 : ℝ) <
        ((578 : ℝ) ^ J / 2) *
          ‖variableBandZeroDetectorPolynomial
            (1 : DirichletCharacter ℂ 1) E eta j N u‖ :=
      hfacDiv.trans_lt (hlargeU.trans_le hscaledUpper)
    have hp578 : 0 < (578 : ℝ) ^ J := by positivity
    refine ⟨hlargeU.trans_le hscaledLoss, ?_⟩
    rw [div_lt_iff₀ (mul_pos (by norm_num) hp578)]
    nlinarith
  let order : ℝ → ℕ := fun t ↦
    if ht : t ∈ S then Classical.choose (hdata t ht) else D * H + 1
  have horder : ∀ t ∈ S,
      D * H + 1 ≤ order t ∧ order t ≤ J ∧
      zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta (order t) ∧
      variableDetectorLowerCutoff E eta (order t) ≤ N ∧
      ∀ u : ℝ, |u - t| ≤ delta * eta →
        ((order t - 1).factorial : ℝ) / 32 <
            ((578 : ℝ) ^ J / 2) * (2 * eta) ^ (order t) *
              ‖variableBandZeroDetectorPolynomial
                (1 : DirichletCharacter ℂ 1) E eta (order t) N u‖ ∧
        1 / (16 * (578 : ℝ) ^ J) <
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta (order t) N u‖ := by
    intro t ht
    rw [show order t = Classical.choose (hdata t ht) by simp [order, ht]]
    exact Classical.choose_spec (hdata t ht)
  exact ⟨S, order, hSsub, hsep, hcover, horder⟩

noncomputable local instance zetaVariablePrimitiveCharactersOneUnique :
    Unique (primitiveCharacters 1) where
  default := zetaPrimitiveCharacter
  uniq psi := by
    apply Subtype.ext
    exact DirichletCharacter.level_one psi.1

theorem intervalIntegral_zetaVariableDetector_eq_primitiveNegativeDirichletMass
    (Y N T : ℕ) (c : ℕ → ℂ) :
    (∫ u in (0 : ℝ)..(T : ℝ),
        ‖∑ n ∈ Finset.Ioc Y N,
          c n * (1 : DirichletCharacter ℂ 1) n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
      ∫ u in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass 1 (Finset.Ioc Y N) c u := by
  have hdefault : (default : primitiveCharacters 1).1 =
      (1 : DirichletCharacter ℂ 1) := DirichletCharacter.level_one _
  rw [intervalIntegral_primitiveNegativeDirichletMass_eq]
  norm_num [zetaPrimitiveCharacter, hdefault]

/-- Raw conductor-one log-free density inequality at variable detector
order.  This is the exact zeta analogue of the primitive-character raw
density estimate. -/
theorem exists_zeta_variable_raw_logFreeDensity_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (T : ℕ), 1 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := 2 * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (zetaHighZeroRectangleMass eta T : ℝ) *
                (delta * eta) * (1 / 32 : ℝ) ^ 2 ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                variableRawLogFreeDensityTerm T E N J j eta := by
  obtain ⟨κ, D, hκ, hD, hselection⟩ :=
    exists_zeta_variable_detected_zero_selection
  obtain ⟨A, hA, hcoverBound⟩ :=
    exists_zetaHighZeroRectangleMass_cover_bound
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Y : ℕ → ℕ := fun j ↦ variableDetectorLowerCutoff E eta j
  let c : ℕ → ℕ → ℂ := fun j ↦
    variableNormalizedDetectorCoefficient eta J j
  let Klocal : ℝ := 48 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  have hB : (1 : ℝ) ≤ B := by
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [B]
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact Nat.mul_pos (by omega) (by omega)
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJpos
  have hdelta1 : delta ≤ 1 := by
    simpa only [delta] using variableDetectorPropagationRadius_le_one hJpos
  have heta1 : eta ≤ 1 := by linarith
  have hKlocal : 0 ≤ Klocal := by
    dsimp [Klocal]
    have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
    positivity
  obtain ⟨S, order, hSsub, hsep, hcover, horder⟩ :=
    hselection T hT eta heta heta8
  have hSrange : ∀ t ∈ S, 0 ≤ t ∧ t ≤ T := by
    intro t ht
    have htOrd := hSsub ht
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht1, htT⟩ :=
      (mem_zetaHighZeroOrdinates_iff heta1 (by exact_mod_cast hT) t).mp
        htOrd
    exact ⟨by linarith, by simpa only using htT⟩
  have horderRange : ∀ t ∈ S, L ≤ order t ∧ order t ≤ J := by
    intro t ht
    exact ⟨by simpa only [L] using (horder t ht).1,
      (horder t ht).2.1⟩
  have hlower : ∀ t ∈ S, ∀ u : ℝ,
      |u - t| ≤ delta * eta →
      (1 / 32 : ℝ) ≤
        ‖∑ n ∈ Finset.Ioc (Y (order t)) N,
          c (order t) n * (1 : DirichletCharacter ℂ 1) n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ := by
    intro t ht u hu
    have hlarge := (horder t ht).2.2.2.2 u hu
    let j := order t
    let f : ℝ := ((j - 1).factorial : ℝ)
    let G : ℝ := (578 : ℝ) ^ J / 2
    have hf : 0 < f := by
      dsimp [f]
      exact_mod_cast Nat.factorial_pos (j - 1)
    have hscaled : f / 32 <
        G * (2 * eta) ^ j *
          ‖variableBandZeroDetectorPolynomial
            (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
      simpa only [j, f, G] using hlarge.1
    have hdiv := div_lt_div_of_pos_right hscaled hf
    have hnormScale :
        ‖(variableDetectorNormalization eta J j : ℂ) *
            variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ =
          variableDetectorNormalization eta J j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg
          (variableDetectorNormalization_nonneg heta.le J j)]
    apply le_of_lt
    calc
      (1 / 32 : ℝ) = (f / 32) / f := by field_simp
      _ < (G * (2 * eta) ^ j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖) / f := hdiv
      _ = variableDetectorNormalization eta J j *
            ‖variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := by
        dsimp [variableDetectorNormalization, G, f]
        ring
      _ = ‖(variableDetectorNormalization eta J j : ℂ) *
            variableBandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) E eta j N u‖ := hnormScale.symm
      _ = ‖∑ n ∈ Finset.Ioc (Y (order t)) N,
            c (order t) n * (1 : DirichletCharacter ℂ 1) n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ := by
        rw [variable_normalized_polynomial_eq_smul]
  have hselected := selectedOrdinates_card_mul_le_variableDetector_integrals
    zetaPrimitiveCharacter Y c N T L J eta delta (1 / 32 : ℝ)
      heta heta1 hdelta hdelta1 (by norm_num) S order
      hSrange hsep horderRange hlower
  have hselectedMass :
      (S.card : ℝ) * (delta * eta) * (1 / 32 : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
              (c j) u := by
    calc
      (S.card : ℝ) * (delta * eta) * (1 / 32 : ℝ) ^ 2 ≤
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc (Y j) N,
                c j n * (1 : DirichletCharacter ℂ 1) n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 :=
        hselected
      _ = ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
              (c j) u := by
        apply Finset.sum_congr rfl
        intro j hj
        exact intervalIntegral_zetaVariableDetector_eq_primitiveNegativeDirichletMass
          (Y j) N (T + 1) (c j)
  have hlogGlobal : eta * Real.log ((T : ℝ) + 2) ≤
      eta * Real.log B := by
    apply mul_le_mul_of_nonneg_left _ heta.le
    apply Real.log_le_log (by positivity)
    dsimp [B]
    nlinarith
  have hmass := hcoverBound eta (T : ℝ) (eta * Real.log B) delta
    heta heta1 (by exact_mod_cast hT) hdelta.le hdelta1 hlogGlobal
    S hSsub hcover
  have hmass' : (zetaHighZeroRectangleMass eta T : ℝ) ≤
      (S.card : ℝ) * Klocal := by
    simpa only [Klocal] using hmass
  let c₀ : ℝ := (delta * eta) * (1 / 32 : ℝ) ^ 2
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hmassSelected :
      (zetaHighZeroRectangleMass eta T : ℝ) * c₀ ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
                (c j) u := by
    calc
      (zetaHighZeroRectangleMass eta T : ℝ) * c₀ ≤
          ((S.card : ℝ) * Klocal) * c₀ :=
        mul_le_mul_of_nonneg_right hmass' hc₀
      _ = Klocal * ((S.card : ℝ) * c₀) := by ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
                (c j) u := by
        apply mul_le_mul_of_nonneg_left _ hKlocal
        simpa only [c₀, mul_assoc] using hselectedMass
  have hintegrals :
      (∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
              (c j) u) ≤
        ∑ j ∈ Finset.Icc L J,
          variableRawLogFreeDensityTerm T E N J j eta := by
    apply Finset.sum_le_sum
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hYcompare : zeroDetectorLowerCutoff B ≤ Y j := by
      dsimp [Y]
      exact zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have hYone : 1 ≤ Y j := by
      exact (show 1 ≤ zeroDetectorLowerCutoff B by
        unfold zeroDetectorLowerCutoff
        have : 0 < 2 ^ zeroDetectorLowerLog B := pow_pos (by omega) _
        omega).trans hYcompare
    have hbase := (detectorLowerCutoff_hybrid_bound 2 T (by norm_num)).trans
      hYcompare
    have hhybrid : 2 * ((T + 1) + 1) * 1 ^ 2 ≤ Y j := by
      omega
    have hweighted := intervalIntegral_weightedDetectorBand_hybrid_le
      1 (Y j) N (T + 1) (j - 1) (by omega) hYone hhybrid
        eta heta.le
    calc
      (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
            (c j) u) =
        variableDetectorNormalization eta J j ^ 2 *
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
              (fun n ↦
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) u := by
          simpa only [c] using
            intervalIntegral_variableNormalizedDetector_eq
              1 (Y j) N (T + 1) eta J j heta.le
      _ ≤ variableDetectorNormalization eta J j ^ 2 *
          ((2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
            ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
              (2 * ((j - 1) + 1))) *
            (((Y j : ℝ) / 2) ^ (-(2 * eta)))) :=
        mul_le_mul_of_nonneg_left hweighted (sq_nonneg _)
      _ = variableRawLogFreeDensityTerm T E N J j eta := by rfl
  calc
    (zetaHighZeroRectangleMass eta T : ℝ) *
          (delta * eta) * (1 / 32 : ℝ) ^ 2 =
        (zetaHighZeroRectangleMass eta T : ℝ) * c₀ := by
      dsimp [c₀]
      ring
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveNegativeDirichletMass 1 (Finset.Ioc (Y j) N)
              (c j) u := hmassSelected
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          variableRawLogFreeDensityTerm T E N J j eta :=
      mul_le_mul_of_nonneg_left hintegrals hKlocal
    _ = _ := by rfl

/-- The conductor-one variable-density estimate with the finite order sum
removed. -/
theorem exists_zeta_variable_logFreeDensity_envelope_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (T : ℕ), 1 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := 2 * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let Klocal := 48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (zetaHighZeroRectangleMass eta T : ℝ) ≤
            (Klocal * ((J + 1 : ℕ) : ℝ) *
                variableLogFreeDensityEnvelope T N J eta) /
              ((delta * eta) * (1 / 32 : ℝ) ^ 2) := by
  obtain ⟨κ, D, A, hκ, hD, hA, hraw⟩ :=
    exists_zeta_variable_raw_logFreeDensity_parameters
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Klocal : ℝ := 48 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  have hB : (1 : ℝ) ≤ B := by
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [B]
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact Nat.mul_pos (by omega) (by omega)
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJpos
  have hden : 0 < (delta * eta) * (1 / 32 : ℝ) ^ 2 := by positivity
  have hraw' := hraw T hT eta heta heta8
  have hY : ∀ j ∈ Finset.Icc L J,
      2 ≤ variableDetectorLowerCutoff E eta j := by
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have htwo : 2 ≤ zeroDetectorLowerCutoff B := by
      unfold zeroDetectorLowerCutoff
      have hlarge : 1 ≤ zeroDetectorLowerLog B := by
        unfold zeroDetectorLowerLog
        have hBtwo : (2 : ℝ) ≤ B := by
          dsimp [B]
          have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
          nlinarith
        have hlogLower : Real.log 2 ≤ Real.log B :=
          Real.log_le_log (by norm_num) hBtwo
        have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
          lt_trans (by norm_num) Real.log_two_gt_d9
        have hone : (1 : ℝ) ≤ 8 * Real.log B := by nlinarith
        exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ 8 * Real.log B by
          simpa using hone)
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hlarge)
    exact htwo.trans hcompare
  have hsum := sum_variableRawLogFreeDensityTerm_le_envelope
    (T := T) (E := E) (N := N) (L := L) (J := J)
      heta.le hY (by dsimp [L]; omega)
  have hKlocal : 0 ≤ Klocal := by
    dsimp [Klocal]
    have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
    positivity
  have hcombined :
      (zetaHighZeroRectangleMass eta T : ℝ) *
          ((delta * eta) * (1 / 32 : ℝ) ^ 2) ≤
        Klocal * (((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) := by
    calc
      (zetaHighZeroRectangleMass eta T : ℝ) *
          ((delta * eta) * (1 / 32 : ℝ) ^ 2) =
          (zetaHighZeroRectangleMass eta T : ℝ) *
            (delta * eta) * (1 / 32 : ℝ) ^ 2 := by ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            variableRawLogFreeDensityTerm T E N J j eta := by
        simpa only [E, B, H₀, H, J, delta, R, N, L, Klocal] using hraw'
      _ ≤ Klocal * (((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) :=
        mul_le_mul_of_nonneg_left hsum hKlocal
  apply (le_div_iff₀ hden).2
  simpa only [mul_assoc] using hcombined

/-- Power-form conductor-one log-free zero-density estimate. -/
theorem exists_zeta_variable_logFreeDensity_power_bound
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (T : ℕ), 2 ≤ T →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let B := 2 * ((T : ℝ) + 2)
          lambda ≤ eta * Real.log B →
          (zetaHighZeroRectangleMass eta T : ℝ) ≤
            C * Real.log B ^ 3 * B ^ (c * eta) := by
  obtain ⟨κ, D, A, hκ, hD, hA, hdensity⟩ :=
    exists_zeta_variable_logFreeDensity_envelope_parameters
  let E : ℕ := D + κ
  let a : ℕ := (D + κ) * variableDetectorHeightDilation E
  let C₀ : ℝ := Real.log 4 + 4
  let cTail : ℝ := 12 * C₀
  let rCoeff : ℝ := 4 * (Real.log (1 + cTail) + Real.log 4624)
  let pCoeff : ℝ := rCoeff * (a : ℝ) + 1
  let base : ℝ := (578 : ℝ) ^ 2 * 2312
  let kCoeff : ℝ := 48 * C₀ + 256 * (A : ℝ) / 3
  let envCoeff : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
  let c : ℝ := Real.log base * (a : ℝ) + 4 * pCoeff + 7
  let Craw : ℝ := 1024 * kCoeff * ((a : ℝ) + 1) * (a : ℝ) *
    (12 * C₀) * (16 * pCoeff ^ 4) * envCoeff
  let C : ℝ := Craw * Real.exp (2 * c) / lambda ^ 3
  have haNat : 1 ≤ a := by
    dsimp [a, E]
    exact Nat.mul_pos (by omega) (variableDetectorHeightDilation_pos (D + κ))
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hcTail : 0 < cTail := by dsimp [cTail]; positivity
  have hrCoeff : 0 < rCoeff := by
    dsimp [rCoeff]
    have hlogOne : 0 < Real.log (1 + cTail) :=
      Real.log_pos (by linarith)
    have hlogBase : 0 < Real.log (4624 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hpCoeff : 0 < pCoeff := by dsimp [pCoeff]; positivity
  have hbase : 1 < base := by dsimp [base]; norm_num
  have hkCoeff : 0 < kCoeff := by dsimp [kCoeff]; positivity
  have henvCoeff : 0 < envCoeff := by dsimp [envCoeff]; positivity
  have hc : 0 < c := by
    dsimp [c]
    have hlogBase : 0 < Real.log base := Real.log_pos hbase
    positivity
  have hCraw : 0 < Craw := by dsimp [Craw]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT eta heta heta8
  dsimp only
  intro hlower
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let h : ℝ := eta * Real.log B
  let H₀ : ℕ := Nat.ceil (1 + h)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let Klocal : ℝ := 48 * C₀ + (256 * (A : ℝ) / 3) * h
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hh : 0 < h := by dsimp [h]; positivity
  have hlambdaH : lambda ≤ h := by simpa only [h, B] using hlower
  obtain ⟨hJ, hJbound, hJexp, hJoneExp, _hKgeneric, henv⟩ :=
    variable_envelope_parameter_bounds (A := A) hκ hD
      (by norm_num : 2 ≤ (2 : ℕ)) hT heta heta8
  change (J : ℝ) ≤ (a : ℝ) * (h + 2) at hJbound
  change (J : ℝ) ≤ (a : ℝ) * Real.exp (h + 2) at hJexp
  change ((J + 1 : ℕ) : ℝ) ≤
      ((a : ℝ) + 1) * Real.exp (h + 2) at hJoneExp
  change variableLogFreeDensityEnvelope T N J eta ≤
      (16 * pCoeff ^ 4) * envCoeff / eta ^ 2 *
        Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
          4 * pCoeff + 4) * (h + 2)) at henv
  have hKlocal : Klocal ≤ kCoeff * Real.exp (h + 2) := by
    have hpre : Klocal ≤ kCoeff * (h + 2) := by
      let k₀ : ℝ := 48 * C₀
      let k₁ : ℝ := 256 * (A : ℝ) / 3
      have hk₀ : 0 ≤ k₀ := by dsimp [k₀]; positivity
      have hk₁ : 0 ≤ k₁ := by dsimp [k₁]; positivity
      have hdiff : 0 ≤ k₀ * (h + 1) + 2 * k₁ := by positivity
      have hsmall : k₀ + k₁ * h ≤ (k₀ + k₁) * (h + 2) := by
        calc
          k₀ + k₁ * h ≤ k₀ + k₁ * h + (k₀ * (h + 1) + 2 * k₁) :=
            le_add_of_nonneg_right hdiff
          _ = (k₀ + k₁) * (h + 2) := by ring
      simpa only [Klocal, kCoeff, k₀, k₁] using hsmall
    exact hpre.trans (mul_le_mul_of_nonneg_left
      add_two_le_exp_add_two hkCoeff.le)
  have hraw := hdensity T (by omega) eta heta heta8
  have hraw' : (zetaHighZeroRectangleMass eta T : ℝ) ≤
      (Klocal * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
        ((delta * eta) * (1 / 32 : ℝ) ^ 2) := by
    simpa only [E, B, h, H₀, H, J, delta, R, N, Klocal] using hraw
  have hdeltaInv : delta⁻¹ =
      12 * C₀ * (J : ℝ) * (2312 : ℝ) ^ J := by
    dsimp [delta, variableDetectorPropagationRadius, C₀]
    rw [inv_inv]
  have hrawRewrite :
      (Klocal * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
        ((delta * eta) * (1 / 32 : ℝ) ^ 2) =
      1024 * Klocal * ((J + 1 : ℕ) : ℝ) * (J : ℝ) *
        (12 * C₀) * (2312 : ℝ) ^ J *
          variableLogFreeDensityEnvelope T N J eta / eta := by
    rw [div_eq_mul_inv, mul_inv, mul_inv, hdeltaInv]
    field_simp
    ring
  rw [hrawRewrite] at hraw'
  have hboundBeforeEta :
      (zetaHighZeroRectangleMass eta T : ℝ) ≤
        Craw / eta ^ 3 * Real.exp (c * (h + 2)) := by
    calc
      (zetaHighZeroRectangleMass eta T : ℝ) ≤
          1024 * Klocal * ((J + 1 : ℕ) : ℝ) * (J : ℝ) *
            (12 * C₀) * (2312 : ℝ) ^ J *
              variableLogFreeDensityEnvelope T N J eta / eta := hraw'
      _ ≤ 1024 * (kCoeff * Real.exp (h + 2)) *
          (((a : ℝ) + 1) * Real.exp (h + 2)) *
          ((a : ℝ) * Real.exp (h + 2)) *
          (12 * C₀) * (2312 : ℝ) ^ J *
          (((16 * pCoeff ^ 4) * envCoeff / eta ^ 2) *
            Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
              4 * pCoeff + 4) * (h + 2))) / eta := by
        gcongr
        exact variableLogFreeDensityEnvelope_nonneg T N J heta.le
      _ = Craw / eta ^ 3 *
          ((2312 : ℝ) ^ J *
            Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
              4 * pCoeff + 7) * (h + 2))) := by
        have he : Real.exp (h + 2) * Real.exp (h + 2) *
              Real.exp (h + 2) *
              Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                4 * pCoeff + 4) * (h + 2)) =
            Real.exp (3 * (h + 2) +
              (Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                4 * pCoeff + 4) * (h + 2)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc
          1024 * (kCoeff * Real.exp (h + 2)) *
              (((a : ℝ) + 1) * Real.exp (h + 2)) *
              ((a : ℝ) * Real.exp (h + 2)) *
              (12 * C₀) * (2312 : ℝ) ^ J *
              (((16 * pCoeff ^ 4) * envCoeff / eta ^ 2) *
                Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                  4 * pCoeff + 4) * (h + 2))) / eta =
            Craw / eta ^ 3 * ((2312 : ℝ) ^ J *
              (Real.exp (h + 2) * Real.exp (h + 2) *
                Real.exp (h + 2) *
                Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                  4 * pCoeff + 4) * (h + 2)))) := by
            dsimp [Craw]
            field_simp
          _ = Craw / eta ^ 3 * ((2312 : ℝ) ^ J *
              Real.exp (3 * (h + 2) +
                (Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                  4 * pCoeff + 4) * (h + 2))) := by rw [he]
          _ = Craw / eta ^ 3 * ((2312 : ℝ) ^ J *
              Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
                4 * pCoeff + 7) * (h + 2))) := by
            congr 3
            ring
      _ ≤ Craw / eta ^ 3 *
          (Real.exp (Real.log 2312 * ((a : ℝ) * (h + 2))) *
            Real.exp ((Real.log ((578 : ℝ) ^ 2) * (a : ℝ) +
              4 * pCoeff + 7) * (h + 2))) := by
        gcongr
        exact nat_pow_le_exp_of_cast_le (by norm_num) hJbound
      _ = Craw / eta ^ 3 * Real.exp (c * (h + 2)) := by
        congr 1
        rw [← Real.exp_add]
        have hlogBase : Real.log base =
            Real.log ((578 : ℝ) ^ 2) + Real.log 2312 := by
          dsimp [base]
          rw [Real.log_mul (by norm_num : (578 : ℝ) ^ 2 ≠ 0)
            (by norm_num : (2312 : ℝ) ≠ 0)]
        dsimp only [c]
        rw [hlogBase]
        congr 1
        ring_nf
  have hetaInv : eta⁻¹ ≤ Real.log B / lambda := by
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ heta hlambda]
    simpa only [h, one_mul, mul_one, mul_comm] using hlambdaH
  have hetaInvCube : eta⁻¹ ^ 3 ≤
      Real.log B ^ 3 / lambda ^ 3 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ eta⁻¹)
      hetaInv 3
    calc
      eta⁻¹ ^ 3 ≤ (Real.log B / lambda) ^ 3 := hpow
      _ = Real.log B ^ 3 / lambda ^ 3 := by rw [div_pow]
  have hpowB : Real.exp (c * h) = B ^ (c * eta) := by
    dsimp [h]
    rw [Real.rpow_def_of_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hB8)]
    congr 1
    ring
  calc
    (zetaHighZeroRectangleMass eta T : ℝ) ≤
        Craw / eta ^ 3 * Real.exp (c * (h + 2)) := hboundBeforeEta
    _ = Craw * eta⁻¹ ^ 3 *
          (Real.exp (2 * c) * Real.exp (c * h)) := by
      rw [show c * (h + 2) = 2 * c + c * h by ring, Real.exp_add]
      field_simp
    _ ≤ Craw * (Real.log B ^ 3 / lambda ^ 3) *
          (Real.exp (2 * c) * Real.exp (c * h)) := by gcongr
    _ = C * Real.log B ^ 3 * B ^ (c * eta) := by
      rw [hpowB]
      dsimp [C]
      field_simp

end

end Erdos381
