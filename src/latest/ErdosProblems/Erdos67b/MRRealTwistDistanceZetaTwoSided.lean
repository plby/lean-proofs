import ErdosProblems.Erdos67b.MRRealTwistSeparationQuantitative
import ErdosProblems.Erdos67b.TruncatedEulerLSeries

/-!
# The reverse finite Euler comparison near the zeta pole

The twist-separation files use the upper finite-Euler comparison, which turns
an upper bound for `ζ` into a lower bound for a twist distance.  Close to the
pole one also needs the reverse comparison: a lower bound for `ζ` gives an
upper bound for the distance from the zero twist.  This file proves that
reverse inequality with the same absolute finite-Euler errors.
-/

open scoped BigOperators ComplexConjugate LSeries.notation

namespace Erdos67b

noncomputable section

open TruncatedEulerLSeries

/-- The reverse prime-power comparison. -/
theorem truncatedEulerLog_le_linear_add_remainder
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v ≤
      truncatedPolynomialHeightEulerLinear ψ Y v +
        polynomialHeightPrimePowerRemainderBound := by
  have hsummable : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hfinite :
      ∑ p ∈ primesUpTo Y, (p : ℝ) ^ (-(2 : ℝ)) ≤
        polynomialHeightPrimePowerRemainderBound := by
    exact hsummable.sum_le_tsum (primesUpTo Y)
      (fun n hn ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
  unfold truncatedPolynomialHeightEulerLinear
    truncatedPolynomialHeightEulerLog
  calc
    ∑ p ∈ primesUpTo Y,
        (-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p)).re ≤
      ∑ p ∈ primesUpTo Y,
        ((polynomialHeightEulerPrimeTerm ψ Y v p).re +
          (p : ℝ) ^ (-(2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := (mem_primesUpTo.mp hp).1
      have hnorm := norm_eulerLog_sub_linear_le_inv_sq ψ v hY hpPrime
      have hre := Complex.abs_re_le_norm
        (-Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p) -
          polynomialHeightEulerPrimeTerm ψ Y v p)
      have habs := hre.trans hnorm
      rw [abs_le] at habs
      simp only [Complex.sub_re, Complex.neg_re] at habs
      rw [Complex.neg_re]
      linarith
    _ = (∑ p ∈ primesUpTo Y,
          (polynomialHeightEulerPrimeTerm ψ Y v p).re) +
        ∑ p ∈ primesUpTo Y, (p : ℝ) ^ (-(2 : ℝ)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ p ∈ primesUpTo Y,
          (polynomialHeightEulerPrimeTerm ψ Y v p).re) +
        polynomialHeightPrimePowerRemainderBound := by gcongr

/-- The full Euler logarithm is at most its finite part plus the absolute
Euler tail. -/
theorem log_norm_LFunction_le_truncated_add_shiftedEulerTail
    {N Y : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (v : ℝ)
    (hY : 4 ≤ Y) :
    Real.log ‖DirichletCharacter.LFunction ψ
        (polynomialHeightEulerPoint Y v)‖ ≤
      truncatedPolynomialHeightEulerLog ψ Y v +
        shiftedEulerTailConstant + polynomialHeightPrimePowerRemainderBound := by
  have hdecomp := truncated_add_tail_eq_log_norm_LFunction ψ v (by omega : 2 ≤ Y)
  let tail := ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
    (localEulerLog ψ Y v p).re
  have hs := (summable_localEulerLog ψ v (by omega : 2 ≤ Y)).subtype
      (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
  have hre : Summable (fun p : {p : Nat.Primes //
      p ∉ primeSubtypesUpTo Y} ↦ (localEulerLog ψ Y v p).re) :=
    (Complex.hasSum_re hs.hasSum).summable
  have hnorm := hs.norm
  have htailNorm :
      tail ≤ ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
        ‖localEulerLog ψ Y v p‖ := by
    calc
      tail ≤ |tail| := le_abs_self tail
      _ = ‖∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          (localEulerLog ψ Y v p).re‖ := by simp [tail]
      _ ≤ ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖(localEulerLog ψ Y v p).re‖ := norm_tsum_le_tsum_norm hre.norm
      _ ≤ ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖ := by
        exact Summable.tsum_le_tsum
          (fun p ↦ by simpa using Complex.abs_re_le_norm (localEulerLog ψ Y v p))
          hre.norm hnorm
  have hweight := (summable_shiftedPrimeWeight (by omega : 2 ≤ Y)).subtype
    (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
  have hsq := summable_prime_inv_sq.subtype
    (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
  have hlocal := hs.norm
  have htailMajorant :
      (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖) ≤
        shiftedEulerTail Y +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (p : ℝ) ^ (-(2 : ℝ)) := by
    calc
      (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖) ≤
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (shiftedPrimeWeight Y p + (p : ℝ) ^ (-(2 : ℝ))) := by
        exact Summable.tsum_le_tsum
          (fun p ↦ norm_localEulerLog_le_shiftedPrimeWeight_add_inv_sq
            ψ v (by omega : 2 ≤ Y) p)
          hlocal (hweight.add hsq)
      _ = shiftedEulerTail Y +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (p : ℝ) ^ (-(2 : ℝ)) := by
        unfold shiftedEulerTail
        simpa only [Function.comp_apply] using hweight.tsum_add hsq
  have htailConst := shiftedEulerTail_le_constant hY
  have hsqConst := tail_prime_inv_sq_le_remainderBound Y
  change truncatedPolynomialHeightEulerLog ψ Y v + tail = _ at hdecomp
  calc
    Real.log ‖DirichletCharacter.LFunction ψ
        (polynomialHeightEulerPoint Y v)‖ =
        truncatedPolynomialHeightEulerLog ψ Y v + tail := hdecomp.symm
    _ ≤ truncatedPolynomialHeightEulerLog ψ Y v +
        (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖) := by gcongr
    _ ≤ truncatedPolynomialHeightEulerLog ψ Y v +
        (shiftedEulerTail Y +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (p : ℝ) ^ (-(2 : ℝ))) := by gcongr
    _ ≤ truncatedPolynomialHeightEulerLog ψ Y v +
        shiftedEulerTailConstant + polynomialHeightPrimePowerRemainderBound := by
      linarith

private theorem one_sub_rpow_neg_inv_log_le_reverse
    {Y p : ℕ} (hY : 2 ≤ Y) (hp : p.Prime) :
    1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) ≤
      Real.log (p : ℝ) / Real.log (Y : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  rw [Real.rpow_def_of_pos hpPos]
  have hexp := Real.add_one_le_exp
    (-(Real.log (p : ℝ) / Real.log (Y : ℝ)))
  have hexponent :
      Real.log (p : ℝ) * (-(Real.log (Y : ℝ))⁻¹) =
        -(Real.log (p : ℝ) / Real.log (Y : ℝ)) := by field_simp
  rw [hexponent]
  linarith

private theorem inv_sub_rpow_shift_le_log_div_reverse
    {Y p : ℕ} (hY : 2 ≤ Y) (hp : p.Prime) :
    (p : ℝ)⁻¹ - (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) ≤
      Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hphase := one_sub_rpow_neg_inv_log_le_reverse hY hp
  have hmul := mul_le_mul_of_nonneg_left hphase (by positivity : 0 ≤ (p : ℝ)⁻¹)
  rw [show -(1 + (Real.log (Y : ℝ))⁻¹) =
      (-(1 : ℝ)) + (-(Real.log (Y : ℝ))⁻¹) by ring,
    Real.rpow_add hpPos, Real.rpow_neg (by positivity), Real.rpow_one]
  calc
    (p : ℝ)⁻¹ - (p : ℝ)⁻¹ *
        (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) =
        (p : ℝ)⁻¹ *
          (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) := by ring
    _ ≤ (p : ℝ)⁻¹ *
        (Real.log (p : ℝ) / Real.log (Y : ℝ)) := hmul
    _ = Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ) := by field_simp

/-- Reverse removal of the small real shift. -/
theorem eulerLinear_le_quotientCorrelation_add_weightBound
    {q q' Y : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLinear (quotientCharacter χ χ') Y v ≤
      characterTwistPrimeCorrelation χ χ' v Y +
        polynomialHeightWeightRemovalBound := by
  rw [characterTwistPrimeCorrelation_eq_quotientCharacter hq hq' χ χ']
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hsumLog :
      ∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ) =
        BoundedGaps.Maynard.primeLogHarmonicSum Y := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum primesUpTo
    rw [Nat.primesLE_eq_filter_range]
  have hlogBound := primeLogHarmonicSum_le_log_add_bound Y
  have herror :
      (∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)) /
          Real.log (Y : ℝ) ≤ polynomialHeightWeightRemovalBound := by
    rw [hsumLog]
    calc
      BoundedGaps.Maynard.primeLogHarmonicSum Y / Real.log (Y : ℝ) ≤
          (Real.log (Y : ℝ) + polynomialHeightPrimeLogMertensBound) /
            Real.log (Y : ℝ) := div_le_div_of_nonneg_right hlogBound hlogY.le
      _ = 1 + polynomialHeightPrimeLogMertensBound /
            Real.log (Y : ℝ) := by field_simp
      _ ≤ 1 + polynomialHeightPrimeLogMertensBound / Real.log 2 := by
        have hcast : (2 : ℝ) ≤ Y := by exact_mod_cast hY
        have hlogle : Real.log 2 ≤ Real.log (Y : ℝ) :=
          Real.log_le_log (by norm_num) hcast
        simpa only [add_comm] using add_le_add_left
          (div_le_div_of_nonneg_left
            polynomialHeightPrimeLogMertensBound_nonneg
            (Real.log_pos one_lt_two) hlogle) 1
      _ = polynomialHeightWeightRemovalBound := rfl
  unfold truncatedPolynomialHeightEulerLinear
  calc
    ∑ p ∈ primesUpTo Y,
        (polynomialHeightEulerPrimeTerm
          (quotientCharacter χ χ') Y v p).re ≤
      ∑ p ∈ primesUpTo Y,
        ((quotientCharacter χ χ' p *
            (p : ℂ) ^ (-(Complex.I * (v : ℂ)))).re / (p : ℝ) +
          Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp := (mem_primesUpTo.mp hpMem).1
      let phase := quotientCharacter χ χ' p *
        (p : ℂ) ^ (-(Complex.I * (v : ℂ)))
      have hphaseEq : phase = characterTwistPhase χ χ' v p :=
        (characterTwistPhase_eq_quotientCharacter hq hq' χ χ' v).symm
      have hphaseLower : -1 ≤ phase.re := by
        have habs := neg_le_of_abs_le (Complex.abs_re_le_norm phase)
        have hnorm : ‖phase‖ ≤ 1 := by
          rw [hphaseEq]
          exact norm_characterTwistPhase_le_one χ χ' v hp.pos
        linarith
      have hshiftNonneg :
          0 ≤ (p : ℝ)⁻¹ -
            (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
        have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have hdelta : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlogY
        have hpow := Real.rpow_lt_rpow_of_exponent_lt hpOne
          (show -(1 + (Real.log (Y : ℝ))⁻¹) < -(1 : ℝ) by linarith)
        have hone : (p : ℝ) ^ (-(1 : ℝ)) = (p : ℝ)⁻¹ := by
          rw [Real.rpow_neg (by positivity), Real.rpow_one]
        linarith
      have hscaled := mul_le_mul_of_nonneg_right hphaseLower hshiftNonneg
      have hdiff := inv_sub_rpow_shift_le_log_div_reverse hY hp
      rw [polynomialHeightEulerPrimeTerm_eq_shifted_phase
        (quotientCharacter χ χ') v hp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      change phase.re * (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) ≤
        phase.re / (p : ℝ) +
          Real.log (p : ℝ) / (p : ℝ) / Real.log (Y : ℝ)
      rw [div_eq_mul_inv]
      nlinarith
    _ = (∑ p ∈ primesUpTo Y,
          (quotientCharacter χ χ' p *
            (p : ℂ) ^ (-(Complex.I * (v : ℂ)))).re / (p : ℝ)) +
        (∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)) /
          Real.log (Y : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (∑ p ∈ primesUpTo Y,
          (quotientCharacter χ χ' p *
            (p : ℂ) ^ (-(Complex.I * (v : ℂ)))).re / (p : ℝ)) +
        polynomialHeightWeightRemovalBound := by gcongr

/-- Two-sided finite Euler comparison specialized to the level-one twist.
It gives the upper distance estimate needed in the shrinking pole window. -/
theorem pretentiousDistSq_twist_zero_le_loglog_sub_log_zeta_add
    {Y : ℕ} (hY : 4 ≤ Y) (t : ℝ) :
    pretentiousDistSq (archimedeanTwist t) (archimedeanTwist 0) Y ≤
      Real.log (Real.log (Y : ℝ)) -
        Real.log ‖riemannZeta (polynomialHeightEulerPoint Y (-t))‖ +
        (PrimeEstimates.mertensBound + shiftedEulerTailConstant +
          2 * polynomialHeightPrimePowerRemainderBound +
          polynomialHeightWeightRemovalBound) := by
  let chi : DirichletCharacter ℂ 1 := 1
  let psi : DirichletCharacter ℂ 1 := quotientCharacter chi chi
  have hpsi : psi = 1 := by
    dsimp only [psi, chi]
    exact quotientCharacter_one_one
  have hlogFull := log_norm_LFunction_le_truncated_add_shiftedEulerTail
    psi (-t) hY
  have hprimePower := truncatedEulerLog_le_linear_add_remainder
    psi (-t) (by omega : 2 ≤ Y)
  have hweight := eulerLinear_le_quotientCorrelation_add_weightBound
    (by norm_num : 0 < 1) (by norm_num : 0 < 1) chi chi (-t)
      (by omega : 2 ≤ Y)
  have hcorrLower :
      Real.log ‖riemannZeta (polynomialHeightEulerPoint Y (-t))‖ -
          (shiftedEulerTailConstant +
            2 * polynomialHeightPrimePowerRemainderBound +
            polynomialHeightWeightRemovalBound) ≤
        characterTwistPrimeCorrelation chi chi (-t) Y := by
    rw [hpsi,
      DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1)
        (one_lt_polynomialHeightEulerPoint_re (by omega : 2 ≤ Y) (-t)),
      LSeries_dirichletCharacter_one_eq_riemannZeta
        (one_lt_polynomialHeightEulerPoint_re (by omega : 2 ≤ Y) (-t))]
      at hlogFull
    rw [hpsi] at hprimePower
    dsimp only [psi, chi] at hweight
    rw [quotientCharacter_one_one] at hweight
    linarith
  have hmassAbs := PrimeEstimates.abs_primeReciprocals_sub_log_log_le
    (by omega : 2 ≤ Y)
  rw [abs_le] at hmassAbs
  have hmassUpper : characterTwistPrimeMass Y ≤
      Real.log (Real.log (Y : ℝ)) + PrimeEstimates.mertensBound := by
    rw [characterTwistPrimeMass_eq_primeReciprocals]
    linarith
  calc
    pretentiousDistSq (archimedeanTwist t) (archimedeanTwist 0) Y =
        characterTwistDistSq chi chi (-t) Y := by
      rw [show -t = 0 - t by ring,
        characterTwistDistSq_eq_pretentiousDistSq chi chi t 0 Y]
      dsimp only [chi]
      rw [dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact,
        dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact]
    _ = characterTwistPrimeMass Y -
        characterTwistPrimeCorrelation chi chi (-t) Y :=
      characterTwistDistSq_eq_mass_sub_correlation chi chi (-t) Y
    _ ≤ Real.log (Real.log (Y : ℝ)) -
        Real.log ‖riemannZeta (polynomialHeightEulerPoint Y (-t))‖ +
        (PrimeEstimates.mertensBound + shiftedEulerTailConstant +
          2 * polynomialHeightPrimePowerRemainderBound +
          polynomialHeightWeightRemovalBound) := by linarith

end

end Erdos67b

#print axioms Erdos67b.pretentiousDistSq_twist_zero_le_loglog_sub_log_zeta_add
