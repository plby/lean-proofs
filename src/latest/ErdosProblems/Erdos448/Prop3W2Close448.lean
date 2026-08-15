import ErdosProblems.Erdos448.Prop3ClosePair448

open scoped BigOperators ArithmeticFunction.Omega
open Finset

namespace Prop3W2Close448

open Prop3WeightedT448
open Prop3ClosePair448

/-- The second correction weight in the Proposition 3 iteration, bundled
as an arithmetic function for use by the shifted mean-value theorem. -/
noncomputable def secondCorrectionWeightAF (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨hybridCorrectionWeight sharpShiftedReciprocalWeightAF (omegaWeightAF k),
    hybridCorrectionWeight_zero _ _⟩

@[simp] lemma secondCorrectionWeightAF_apply (k n : ℕ) :
    secondCorrectionWeightAF k n =
      hybridCorrectionWeight sharpShiftedReciprocalWeightAF
        (omegaWeightAF k) n := rfl

@[simp] lemma secondCorrectionWeightAF_one (k : ℕ) :
    secondCorrectionWeightAF k 1 = 1 := by
  simp [secondCorrectionWeightAF]

lemma secondCorrectionWeightAF_multiplicative (k : ℕ) :
    (secondCorrectionWeightAF k).IsMultiplicative := by
  refine ⟨secondCorrectionWeightAF_one k, ?_⟩
  intro m n hmn
  exact hybridCorrectionWeight_mul_of_coprime _ _ hmn

/-- The sharp first correction is relatively trapped between `1/tau(p^nu)`
and `(4/3)/tau(p^nu)` at every prime power. -/
lemma sharpShiftedReciprocalWeightAF_relativeType :
    TauInvCorrection448.IsTauInverseRelativeType
      sharpShiftedReciprocalWeightAF 1 (4 / 3) := by
  refine
    { A_pos := by norm_num
      A_le_one := by norm_num
      one_le_B := by norm_num
      prime_pow_lower := ?_
      prime_pow_upper := ?_ }
  · intro p nu hp hnu
    rw [sharpShiftedReciprocalWeightAF_prime_pow hp hnu]
    have hden : (0 : ℝ) < (nu + 1 : ℕ) := by positivity
    have hlocal := Prop3ShiftedMean448.one_le_sharpLocalCorrection hp
    push_cast
    exact div_le_div_of_nonneg_right hlocal (by positivity)
  · intro p nu hp hnu
    rw [sharpShiftedReciprocalWeightAF_prime_pow hp hnu]
    have hden : (0 : ℝ) < (nu + 1 : ℕ) := by positivity
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlocal :
        Prop3ShiftedMean448.sharpLocalCorrection p ≤ 4 / 3 := by
      unfold Prop3ShiftedMean448.sharpLocalCorrection
      have hpos : (0 : ℝ) < 2 * p - 1 := by nlinarith
      rw [div_le_iff₀ hpos]
      nlinarith
    push_cast
    exact div_le_div_of_nonneg_right hlocal (by positivity)

/-- The concrete second correction has the uniform relative prime-power
bounds `3/35` and `12`. -/
lemma secondCorrectionWeightAF_relativeType (k : ℕ) :
    TauInvCorrection448.IsTauInverseRelativeType
      (secondCorrectionWeightAF k) (3 / 35) 12 := by
  let u : ArithmeticFunction ℝ := sharpShiftedReciprocalWeightAF
  let v : ArithmeticFunction ℝ := omegaWeightAF k
  have hvOne : v 1 = 1 := by
    simpa [v] using omegaWeightAF_one k
  have hvNonneg : ∀ n, 0 ≤ v n := by
    intro n
    exact omegaWeightAF_nonneg k n
  have hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1 := by
    intro p hp j
    exact omegaWeightAF_le_one k (p ^ j)
  have hraw := TauInvCorrection448.correctionHybrid_isTauInverseRelativeType
    u v sharpShiftedReciprocalWeightAF_one hvOne
      sharpShiftedReciprocalWeightAF_nonneg hvNonneg
      sharpShiftedReciprocalWeightAF_relativeType hvPowLe
  have hrel : TauInvCorrection448.IsTauInverseRelativeType
      (TauInvCorrection448.maxPrimePowerWeight
        (TauInvCorrection448.correctionWeight u v) u) (3 / 35) 12 := by
    convert hraw using 1 <;> norm_num
  refine
    { A_pos := hrel.A_pos
      A_le_one := hrel.A_le_one
      one_le_B := hrel.one_le_B
      prime_pow_lower := ?_
      prime_pow_upper := ?_ }
  · intro p nu hp hnu
    have h := hrel.prime_pow_lower hp hnu
    rw [TauInvCorrection448.maxPrimePowerWeight_prime_pow _ _ hp hnu,
      TauInvCorrection448.correctionWeight_prime_pow u v hp hnu] at h
    simpa [secondCorrectionWeightAF, u, v,
      hybridCorrectionWeight_prime_pow _ _ hp hnu] using h
  · intro p nu hp hnu
    have h := hrel.prime_pow_upper hp hnu
    rw [TauInvCorrection448.maxPrimePowerWeight_prime_pow _ _ hp hnu,
      TauInvCorrection448.correctionWeight_prime_pow u v hp hnu] at h
    simpa [secondCorrectionWeightAF, u, v,
      hybridCorrectionWeight_prime_pow _ _ hp hnu] using h

lemma secondCorrectionWeightAF_nonneg (k n : ℕ) :
    0 ≤ secondCorrectionWeightAF k n := by
  exact hybridCorrectionWeight_nonneg
    sharpShiftedReciprocalWeightAF (omegaWeightAF k)
    sharpShiftedReciprocalWeightAF_one (omegaWeightAF_one k)
    sharpShiftedReciprocalWeightAF_nonneg (omegaWeightAF_nonneg k)
    sharpShiftedReciprocalWeightAF_logType
    (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) n

lemma secondCorrectionWeightAF_pos (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    0 < secondCorrectionWeightAF k n := by
  classical
  rw [secondCorrectionWeightAF_apply, hybridCorrectionWeight, if_neg hn]
  apply Finset.prod_pos
  intro p hpSupport
  by_cases hi : n.factorization p = 0
  · simp [hi]
  · simp only [hi, if_false]
    have hpMem : p ∈ n.primeFactors := by
      simpa only [Nat.support_factorization] using hpSupport
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    exact lt_of_lt_of_le
      (sharpShiftedReciprocalWeightAF_pos
        (pow_ne_zero _ hpPrime.ne_zero))
      (le_max_right _ _)

/-- Literal logarithmic tau-inverse error for the second correction. -/
lemma secondCorrectionWeightAF_logType (k : ℕ) :
    TauInvCorrection448.IsTauInverseLogType
      (secondCorrectionWeightAF k) 33 := by
  change TauInvCorrection448.IsTauInverseLogType
    (hybridCorrectionWeight sharpShiftedReciprocalWeightAF
      (omegaWeightAF k)) 33
  have h := hybridCorrectionWeight_isTauInverseLogType
    sharpShiftedReciprocalWeightAF (omegaWeightAF k)
    sharpShiftedReciprocalWeightAF_one (omegaWeightAF_one k)
    sharpShiftedReciprocalWeightAF_nonneg (omegaWeightAF_nonneg k)
    sharpShiftedReciprocalWeightAF_logType
    (fun {p} hp j => omegaWeightAF_le_one k (p ^ j))
  convert h using 1 <;> norm_num

/-- Power-saving tau-inverse error used to establish local summability in
the next shifted application. -/
lemma secondCorrectionWeightAF_powType (k : ℕ) :
    Prop3WeightedT448.IsTauInverseType
      (secondCorrectionWeightAF k) 99 (1 / 2) := by
  have h := (secondCorrectionWeightAF_logType k).isTauInverseType
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro p nu hp hnu
  have hlocal := h.2.2 hp hnu
  norm_num at hlocal ⊢
  exact hlocal

/-- The relative bounds give the exact normalized prime-power hypothesis
for the third shifted application, uniformly with `lambda1 = 140` and
`lambda2 = 1`. -/
lemma secondCorrectionWeightAF_weighted_normalized_le
    (k : ℕ) {p i j : ℕ} (hp : p.Prime) :
    secondCorrectionWeightAF k (p ^ (i + (j + 1))) *
          omegaWeightAF k (p ^ (j + 1)) /
        secondCorrectionWeightAF k (p ^ i) ≤ 140 := by
  have h := TauInvCorrection448.relative_normalized_prime_power_ratio
    (secondCorrectionWeightAF k) (omegaWeightAF k)
    (secondCorrectionWeightAF_one k) (secondCorrectionWeightAF_nonneg k)
    (omegaWeightAF_nonneg k) (secondCorrectionWeightAF_relativeType k)
    hp (fun j => omegaWeightAF_le_one k (p ^ j)) i j
  norm_num at h ⊢
  exact h

/-- The unconditional dyadic shifted estimate with the second correction
as input. -/
theorem secondCorrectionWeightedTSum_dyadic_le
    {q : ℕ} (hq : q ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    weightedTSum (secondCorrectionWeightAF k) q k 2
        (2 ^ (k + 2) + 1) ≤
      weightedShiftedDyadicConstant 33 140 1 *
        ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(3 : ℝ) / 4) *
          hybridCorrectionWeight (secondCorrectionWeightAF k)
            (omegaWeightAF k) q := by
  apply weightedTSum_dyadic_le (secondCorrectionWeightAF k)
    (secondCorrectionWeightAF_multiplicative k)
    (secondCorrectionWeightAF_one k)
    (secondCorrectionWeightAF_nonneg k)
    (fun n hn => secondCorrectionWeightAF_pos k hn)
    (Cpow := 99) (delta := 1 / 2) (by norm_num) (by norm_num)
    (secondCorrectionWeightAF_powType k)
    (secondCorrectionWeightAF_logType k) hq
    140 1 (by norm_num) (by norm_num) (by norm_num) k hk
  intro p hp j
  simpa using secondCorrectionWeightAF_weighted_normalized_le
    k (p := p) (i := q.factorization p) (j := j) hp

/-- The correction emitted by the third shifted application has an ordinary
dyadic mean of tau-inverse order, uniformly in the scale. -/
lemma thirdCorrection_meanType (k : ℕ) :
    TauInvTypeMean448.IsTauInverseLogType
      (hybridCorrectionWeight (secondCorrectionWeightAF k)
        (omegaWeightAF k)) 1731 := by
  let u : ArithmeticFunction ℝ := secondCorrectionWeightAF k
  let w : ℕ → ℝ := hybridCorrectionWeight u (omegaWeightAF k)
  have hlocal : TauInvCorrection448.IsTauInverseLogType w 577 := by
    have h := hybridCorrectionWeight_isTauInverseLogType
      u (omegaWeightAF k) (secondCorrectionWeightAF_one k)
      (omegaWeightAF_one k) (secondCorrectionWeightAF_nonneg k)
      (omegaWeightAF_nonneg k) (secondCorrectionWeightAF_logType k)
      (fun {p} hp j => omegaWeightAF_le_one k (p ^ j))
    change TauInvCorrection448.IsTauInverseLogType
      (hybridCorrectionWeight u (omegaWeightAF k)) 577
    convert h using 1 <;> norm_num
  refine
    { C_nonneg := by norm_num
      map_zero := hybridCorrectionWeight_zero _ _
      map_one := hybridCorrectionWeight_one _ _
      map_mul_of_coprime := fun hmn =>
        hybridCorrectionWeight_mul_of_coprime _ _ hmn
      nonneg := fun n => hybridCorrectionWeight_nonneg
        u (omegaWeightAF k) (secondCorrectionWeightAF_one k)
        (omegaWeightAF_one k) (secondCorrectionWeightAF_nonneg k)
        (omegaWeightAF_nonneg k) (secondCorrectionWeightAF_logType k)
        (fun {p} hp j => omegaWeightAF_le_one k (p ^ j)) n
      prime_pow_close := ?_ }
  intro p nu hp hnu
  have h := hlocal.2 hp hnu
  have hscale := TauInvCorrection448.one_add_log_le_three_log hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    |w (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)| ≤
        577 * (1 + Real.log (p : ℝ)) / (p : ℝ) := h
    _ ≤ 577 * (3 * Real.log (p : ℝ)) / (p : ℝ) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      exact mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = 1731 * Real.log (p : ℝ) / (p : ℝ) := by ring

/-- Explicit uniform constant in the close-pair estimate for the second
correction weight. -/
noncomputable def secondFormalClosePairConstant : ℝ :=
  weightedShiftedDyadicConstant 33 140 1 *
    (4 * TauInvTypeMean448.meanConstant 1731 / Real.sqrt (Real.log 2))

lemma secondFormalClosePairConstant_nonneg :
    0 ≤ secondFormalClosePairConstant := by
  unfold secondFormalClosePairConstant
  exact mul_nonneg
    (weightedShiftedDyadicConstant_nonneg
      (by norm_num) (by norm_num) (by norm_num))
    (div_nonneg
      (mul_nonneg (by norm_num)
        (TauInvTypeMean448.meanConstant_nonneg (by norm_num)))
      (Real.sqrt_nonneg _))

/-- Fully unconditional close-pair bound with the genuine second
correction weight `w₂` as input. -/
theorem formalDyadicClosePairMean_secondCorrection_le
    (k : ℕ) (hk : 1 ≤ k) :
    formalDyadicClosePairMean
        (hybridCorrectionWeight sharpShiftedReciprocalWeightAF
          (omegaWeightAF k)) k ≤
      secondFormalClosePairConstant * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  let u : ArithmeticFunction ℝ := secondCorrectionWeightAF k
  let w₄ : ℕ → ℝ := hybridCorrectionWeight u (omegaWeightAF k)
  change formalDyadicClosePairMean u k ≤ _
  apply formalDyadicClosePairMean_le_of_HR
    u w₄ (weightedShiftedDyadicConstant 33 140 1)
      (4 * TauInvTypeMean448.meanConstant 1731 / Real.sqrt (Real.log 2))
      k hk
  · exact weightedShiftedDyadicConstant_nonneg
      (by norm_num) (by norm_num) (by norm_num)
  · intro d' hd'
    have hd'Pos : 0 < d' :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd').1
    have hd'0 : d' ≠ 0 := hd'Pos.ne'
    let D : Finset ℕ :=
      (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d)
    have hsub : D ⊆ Finset.Ico 1 (2 ^ (k + 2) + 1) := by
      intro d hd
      have hdBin : d ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) :=
        (Finset.mem_filter.mp hd).1
      have hdBounds := Finset.mem_Ico.mp hdBin
      apply Finset.mem_Ico.mpr
      constructor
      · have hpowPos : 0 < 2 ^ k := by positivity
        omega
      · have hpowLe : 2 ^ (k + 1) ≤ 2 ^ (k + 2) := by
          exact Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hrestricted :
        (∑ d ∈ D, halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) ≤
          weightedTSum u d' k 2 (2 ^ (k + 2) + 1) := by
      calc
        (∑ d ∈ D,
            halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) =
            ∑ d ∈ D, weightedTKernel u d' k 2 d := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdBin : d ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) :=
            (Finset.mem_filter.mp hd).1
          have hdPos : 0 < d := by
            have hpowPos : 0 < 2 ^ k := by positivity
            have hdLower := (Finset.mem_Ico.mp hdBin).1
            omega
          rw [halfTruncatedOmegaWeight_two_pow, weightedTKernel,
            roughIndicator_two_of_ne_zero hdPos.ne']
          ring
        _ ≤ ∑ d ∈ Finset.Ico 1 (2 ^ (k + 2) + 1),
              weightedTKernel u d' k 2 d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro d hd hnot
          exact weightedTKernel_nonneg u
            (secondCorrectionWeightAF_nonneg k) d' k 2 d
        _ = weightedTSum u d' k 2 (2 ^ (k + 2) + 1) := by
          rfl
    change (∑ d ∈ D,
        halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) ≤ _
    exact hrestricted.trans
      (secondCorrectionWeightedTSum_dyadic_le hd'0 k hk)
  · have hmean := TauInvTypeMean448.mean_dyadic_le
      (thirdCorrection_meanType k) k hk
    simpa [w₄, u] using hmean

end Prop3W2Close448

#print axioms Prop3W2Close448.secondCorrectionWeightAF_relativeType
#print axioms Prop3W2Close448.secondCorrectionWeightedTSum_dyadic_le
#print axioms Prop3W2Close448.thirdCorrection_meanType
#print axioms Prop3W2Close448.secondFormalClosePairConstant_nonneg
#print axioms Prop3W2Close448.formalDyadicClosePairMean_secondCorrection_le
