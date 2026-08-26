import ErdosProblems.Erdos67b.MRCofactorHigherMassLimits
import ErdosProblems.Erdos67b.MRGSA10OrdinaryMovingProjectionAverage

/-! # Vanishing of the full ordinary projection at a fixed power cutoff -/

open Filter
open scoped Topology

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrTendsto_cofactorNearPrime_div {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun X : ℕ ↦ gsA10OrdinaryNearPrimeAverageBound
      (mrCofactorPowerCutoff delta X) X (Real.log (X : ℝ) ^ 2) / X) atTop (𝓝 0) := by
  have hC := gsA10NearChebyshevConstant_nonneg
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hlogy : 0 < Real.log (mrCofactorPowerCutoff delta X : ℝ) :=
      (mul_pos hdelta hL).trans_le (mrCofactorPowerCutoff_log_lower delta X)
    have hR := PrimeEstimates.primeReciprocals_nonneg (2 * X)
    have hhar : 0 ≤ (harmonic (2 * X) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg (fun i hi ↦ by positivity)
    unfold gsA10OrdinaryNearPrimeAverageBound
    positivity
  · filter_upwards [eventually_ge_atTop 2,
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)] with X hX hlog
    let L := Real.log (X : ℝ)
    let y := mrCofactorPowerCutoff delta X
    let R := PrimeEstimates.primeReciprocals (2 * X)
    have hL : 0 < L := zero_lt_one.trans_le hlog
    have hXpos : (0 : ℝ) < X := by positivity
    have hR : 0 ≤ R := PrimeEstimates.primeReciprocals_nonneg (2 * X)
    have hlogy : 0 < Real.log (y : ℝ) :=
      (mul_pos hdelta hL).trans_le (mrCofactorPowerCutoff_log_lower delta X)
    have hfirst : 4 * gsA10NearChebyshevConstant * R / Real.log (y : ℝ) ≤
        (4 * gsA10NearChebyshevConstant / delta) * (R / L) := by
      calc
        _ ≤ (4 * gsA10NearChebyshevConstant * R) / (delta * L) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hdelta hL)
            (mrCofactorPowerCutoff_log_lower delta X)
        _ = _ := by ring
    have hsecond : 4 * (harmonic (2 * X) : ℝ) / L ^ 2 * R ^ 2 ≤ 12 * (R ^ 2 / L) := by
      calc
        _ ≤ 4 * (3 * L) / L ^ 2 * R ^ 2 := by
          gcongr
          exact mrCofactor_harmonic_two_mul_le hX hlog
        _ = _ := by field_simp; ring
    calc
      _ = 4 * gsA10NearChebyshevConstant * R / Real.log (y : ℝ) +
          4 * (harmonic (2 * X) : ℝ) / L ^ 2 * R ^ 2 := by
        unfold gsA10OrdinaryNearPrimeAverageBound
        dsimp only [R, L, y]
        push_cast
        field_simp
        ring
      _ ≤ _ := add_le_add hfirst hsecond
  · simpa only [mul_zero, zero_add] using
      (mrTendsto_primeReciprocals_two_mul_div_log.const_mul (4 * gsA10NearChebyshevConstant / delta)).add
        (mrTendsto_primeReciprocals_two_mul_sq_div_log.const_mul 12)

theorem mrTendsto_cofactorNearHPPMass {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun X : ℕ ↦ gsA10OrdinaryNearHPPMassBudget (mrCofactorPowerCutoff delta X) X) atTop (𝓝 0) := by
  have hZ : ∀ᶠ X : ℕ in atTop, 2 ≤ 2 * X ∧ 2 * X ≤ 2 * X := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact ⟨by omega, le_rfl⟩
  have hG := mrTendsto_higherMass_at_cofactorPowerCutoff hdelta (fun X ↦ 2 * X) hZ
  have hHG := mrTendsto_harmonic_mul_higherMass_at_cofactorPowerCutoff hdelta (fun X ↦ 2 * X) hZ
  simpa only [gsA10OrdinaryNearHPPMassBudget, mul_assoc, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    using (hHG.const_mul 2).add (hG.pow 2)

theorem mrTendsto_cofactorNearHPP_div {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun X : ℕ ↦ gsA10OrdinaryNearHPPAverageBound
      (mrCofactorPowerCutoff delta X) X (Real.log (X : ℝ) ^ 2)
      (Real.log (mrCofactorPowerCutoff delta X : ℝ))⁻¹ / X) atTop (𝓝 0) := by
  have heta := (mrTendsto_inv_log_cofactorPowerCutoff hdelta).pow 2
  have hB := mrTendsto_cofactorNearHPPMass hdelta
  have hmain := (heta.mul hB).const_mul 8
  have hrec := ((mrTendsto_harmonic_two_mul_div_log_sq.mul heta).mul hB).const_mul 8
  have ht := hmain.add hrec
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXpos : (0 : ℝ) < X := by positivity
  unfold gsA10OrdinaryNearHPPAverageBound
  push_cast
  field_simp
  ring

theorem mrTendsto_cofactorHalfEndpoint {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun X : ℕ ↦ gsA10OrdinaryHalfEndpointBound (mrCofactorPowerCutoff delta X) X) atTop (𝓝 0) := by
  have hZ : ∀ᶠ X : ℕ in atTop, 2 ≤ X ∧ X ≤ 2 * X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact ⟨hX, by omega⟩
  have hG := mrTendsto_higherMass_at_cofactorPowerCutoff hdelta id hZ
  have hHG := mrTendsto_harmonic_mul_higherMass_at_cofactorPowerCutoff hdelta id hZ
  have ht := ((MRHalaszBands.tendsto_log_pow_div_self 2).div_const 2).add hHG
  have hsum := ht.add ((hG.pow 2).div_const 2)
  simp only [id_eq, zero_div, zero_add, zero_pow (by norm_num : 2 ≠ 0)] at hsum
  convert hsum using 1
  funext X
  unfold gsA10OrdinaryHalfEndpointBound gsA10HalfEndpointPrimeMass gsA10PrimeLambdaHarmonicBudget
  ring

theorem mrTendsto_cofactorOrdinaryProjection {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun X : ℕ ↦ gsA10OrdinaryMovingProjectionAveragedBound (mrCofactorPowerCutoff delta X) X
      (Real.log (mrCofactorPowerCutoff delta X : ℝ))⁻¹) atTop (𝓝 0) := by
  have heta := mrTendsto_inv_log_cofactorPowerCutoff hdelta
  have hnear := (mrTendsto_cofactorNearPrime_div hdelta).add (mrTendsto_cofactorNearHPP_div hdelta)
  have hmass := heta.const_mul gsA10MovingPerronAveragedMassConstant
  have hend := ((heta.pow 2).mul (mrTendsto_cofactorHalfEndpoint hdelta)).const_mul 2
  simpa only [gsA10OrdinaryMovingProjectionAveragedBound, add_div, mul_assoc,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] using (hnear.add hmass).add hend

end

end Erdos67b
