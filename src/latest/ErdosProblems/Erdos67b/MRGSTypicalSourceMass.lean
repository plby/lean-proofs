import ErdosProblems.Erdos67b.MRGSMaskedEulerAllowance

/-!
# Source prime-mask masses with their Mertens allowances

Every deleted prime has logarithm at most `sqrt (log N)`. Rounding down
the exponential cutoff gives a mass bound with a fixed Mertens allowance,
and hence a uniform quantitative GS renormalization error for each mask.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrGS_primeBandMass_le_cutoff
    (Q : ℕ → Prop) [DecidablePred Q] (N Y : ℕ)
    (hsmall : ∀ p, p.Prime → Q p → p ≤ Y) :
    primeBandReciprocalMass Q N ≤ PrimeEstimates.primeReciprocals Y := by
  have hfull := primeBandReciprocalMass_add_compl (fun _ ↦ True) Y
  have hsum : (∑ p ∈ primesUpTo Y, 1 / (p : ℝ)) = PrimeEstimates.primeReciprocals Y := by
    simpa only [primeBandReciprocalMass, Finset.filter_true, not_true_eq_false,
      Finset.filter_false, Finset.sum_empty, add_zero] using hfull
  rw [← hsum]
  unfold primeBandReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := Finset.mem_filter.mp hp
    have hprime := (mem_primesUpTo.mp hpN).1
    exact mem_primesUpTo.mpr ⟨hprime, hsmall p hprime hpQ⟩
  · intro p hp hnot
    positivity

theorem mrGS_primeBandMass_le_half_add_mertens
    (Q : ℕ → Prop) [DecidablePred Q] {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hsmall : ∀ p, p.Prime → Q p → Real.log (p : ℝ) ≤ Real.sqrt (Real.log (N : ℝ))) :
    primeBandReciprocalMass Q N ≤
      PrimeEstimates.primeReciprocals N / 2 + (3 / 2 : ℝ) * PrimeEstimates.mertensBound := by
  let Y : ℕ := ⌊Real.exp (Real.sqrt (Real.log (N : ℝ)))⌋₊
  have hs : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlog
  have hY : 2 ≤ Y := by
    apply Nat.le_floor
    have hh := Real.add_one_le_exp (Real.sqrt (Real.log (N : ℝ)))
    norm_num only [Nat.cast_ofNat]
    linarith
  have hmass := mrGS_primeBandMass_le_cutoff Q N Y (by
    intro p hp hQ
    apply Nat.le_floor
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hp.pos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hsmall p hp hQ))
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlogY : Real.log (Y : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := by
    have hh := Real.log_le_log hYpos
      (Nat.floor_le (Real.exp_pos (Real.sqrt (Real.log (N : ℝ)))).le)
    simpa only [Real.log_exp] using hh
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hloglogY := Real.log_le_log hlogYpos hlogY
  rw [Real.log_sqrt (by linarith : 0 ≤ Real.log (N : ℝ))] at hloglogY
  have hMY := (abs_le.mp (PrimeEstimates.abs_primeReciprocals_sub_log_log_le hY)).2
  have hMN := (abs_le.mp (PrimeEstimates.abs_primeReciprocals_sub_log_log_le hN)).1
  linarith

def mrGSTypicalSourceErrorConstant : ℝ :=
  10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
    Real.exp ((119 / 8 : ℝ) * PrimeEstimates.mertensBound + 8)

theorem mrGSTypicalSourceErrorConstant_nonneg : 0 ≤ mrGSTypicalSourceErrorConstant := by
  have hC := HalberstamScratch.explicitMassConstant_nonneg
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)
  unfold mrGSTypicalSourceErrorConstant
  positivity

theorem mrGS_sourceMasked_linearError_le_log_rpow_of_distanceAllowance
    {f : ℕ → ℂ} (hbound : ∀ n, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (t₁ u : ℝ) {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hsmall : ∀ p, p.Prime → Q p → Real.log (p : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)))
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      Real.log (Real.log (N : ℝ)) / 8 + L) :
    gsPrefixRenormalizationLinearError (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) u N ≤
      (mrGSTypicalSourceErrorConstant * Real.exp (7 * L)) * (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
  have hB := PrimeEstimates.mertensBound_nonneg
  have hmass := mrGS_primeBandMass_le_half_add_mertens Q hN hlog hsmall
  have hM := abs_le.mp (PrimeEstimates.abs_primeReciprocals_sub_log_log_le hN)
  have hEuler := mrGS_maskedEulerExponent_le_with_allowance hbound Q t₁ N
    (show 0 ≤ 2 * PrimeEstimates.mertensBound + L by positivity)
    (by linarith) (by linarith [hM.1])
  have hEuler' : gsEulerExponent (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) N ≤
      (7 / 8 : ℝ) * Real.log (Real.log (N : ℝ)) +
        ((119 / 8 : ℝ) * PrimeEstimates.mertensBound + 8 + 7 * L) := by
    rw [gsDeletePrimeBand_archimedeanUntwist]
    linarith [hM.2]
  have herror := mrGS_linearError_le_log_rpow_of_euler_bound _ u hN hEuler'
  simpa only [Real.exp_add, mrGSTypicalSourceErrorConstant, mul_assoc] using herror

theorem mrGS_sourceMasked_linearError_le_log_rpow
    {f : ℕ → ℂ} (hbound : ∀ n, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hsmall : ∀ p, p.Prime → Q p → Real.log (p : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)))
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      Real.log (Real.log (N : ℝ)) / 8) :
    gsPrefixRenormalizationLinearError (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) u N ≤
      mrGSTypicalSourceErrorConstant * (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
  simpa only [mul_zero, Real.exp_zero, mul_one, add_zero] using
    mrGS_sourceMasked_linearError_le_log_rpow_of_distanceAllowance hbound Q t₁ u
      (L := 0) le_rfl hN hlog hsmall (by simpa only [add_zero] using hdist)

end

end Erdos67b
