import ErdosProblems.Erdos587.HooleyWeakMean
import ErdosProblems.Erdos587.HooleyDyadicMean

/-!
# Strong harmonic mean on squarefree smooth numbers

Only `O(log log X)` dyadic levels are needed: the weighted second moment
is bounded by the divisor-square Euler product, of size `O(log X)^4`.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def deltaDivisorSquareConstant : ℝ :=
  Classical.choose (exists_squarefree_divisorPower_log_bound 2)

lemma deltaDivisorSquareConstant_pos : 0 < deltaDivisorSquareConstant :=
  (Classical.choose_spec (exists_squarefree_divisorPower_log_bound 2)).1

lemma sum_deltaSmoothNumbers_delta_sq_le {X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ deltaSmoothNumbers X, (hooleyDelta n : ℝ) ^ 2 * ((1 : ℝ) / n)) ≤
      deltaDivisorSquareConstant * Real.log (X : ℝ) ^ 4 := by
  have h := (Classical.choose_spec (exists_squarefree_divisorPower_log_bound 2)).2
    X (deltaPrimeProduct X) hX (deltaPrimeProduct_squarefree X)
  change (deltaPrimeProduct X).primeFactors ⊆ Nat.primesLE X →
    (∑ n ∈ deltaSmoothNumbers X, (n.divisors.card : ℝ) ^ 2 / n) ≤
      deltaDivisorSquareConstant * Real.log (X : ℝ) ^ (2 ^ 2 : ℕ) at h
  norm_num only [Nat.reducePow] at h
  apply le_trans _ (h (by
    rw [primeFactors_deltaPrimeProduct]
    intro p hp
    obtain ⟨hpX, hp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpX.le, hp⟩))
  apply Finset.sum_le_sum
  intro n hn
  have hdelta : (hooleyDelta n : ℝ) ≤ n.divisors.card := by
    exact_mod_cast hooleyDelta_le_card_divisors n
  simpa only [mul_one_div] using div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hdelta 2) (show (0 : ℝ) ≤ n by positivity)

noncomputable def deltaDyadicLevelConstant : ℝ := 4 / Real.log 2 + 1

lemma deltaDyadicLevelConstant_pos : 0 < deltaDyadicLevelConstant := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold deltaDyadicLevelConstant
  positivity

lemma exists_delta_dyadic_level {X : ℕ} (hX : 2 ≤ X) {L : ℝ} (hL : 1 ≤ L)
    (hloglog : Real.log (Real.log (X : ℝ)) ≤ L) :
    ∃ k : ℕ, (k : ℝ) ≤ deltaDyadicLevelConstant * L ∧
      Real.log (X : ℝ) ^ 4 ≤ (2 : ℝ) ^ k := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let k := ⌈4 * L / Real.log 2⌉₊
  have hklo : 4 * L / Real.log 2 ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi := Nat.ceil_lt_add_one (show 0 ≤ 4 * L / Real.log 2 by positivity)
  refine ⟨k, ?_, ?_⟩
  · dsimp only [k, deltaDyadicLevelConstant]
    rw [show 4 * L / Real.log 2 = (4 / Real.log 2) * L by ring] at hkhi
    rw [show 4 * L / Real.log 2 = (4 / Real.log 2) * L by ring]
    nlinarith only [hkhi, hL]
  · have hexp : 4 * Real.log (Real.log (X : ℝ)) ≤ (k : ℝ) * Real.log 2 := by
      have hmul := (div_le_iff₀ hlog2).mp hklo
      linarith
    calc
      _ = Real.exp (4 * Real.log (Real.log (X : ℝ))) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hlogX]
      _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_monotone hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

noncomputable def deltaSmoothMeanConstant : ℝ :=
  deltaWeakThresholdConstant * deltaReciprocalMeanConstant +
    deltaDyadicLevelConstant * deltaWeakThresholdConstant *
      (deltaReciprocalMeanConstant + deltaHarmonicMomentConstant) +
        deltaDivisorSquareConstant / (deltaWeakThresholdConstant * Real.log 2)

lemma deltaSmoothMeanConstant_pos : 0 < deltaSmoothMeanConstant := by
  have hK := deltaWeakThresholdConstant_pos
  have hV := deltaReciprocalMeanConstant_pos
  have hC := deltaHarmonicMomentConstant_bounds.1
  have hD := deltaDyadicLevelConstant_pos
  have hW := deltaDivisorSquareConstant_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold deltaSmoothMeanConstant
  positivity

theorem deltaSmooth_harmonic_mean {X : ℕ} (hX : 2 ≤ X) {L : ℝ} (hL : 1 ≤ L)
    (hbudget : (∑ p ∈ X.primesBelow, (1 : ℝ) / p) ≤ L)
    (hloglog : Real.log (Real.log (X : ℝ)) ≤ L) :
    (∑ n ∈ deltaSmoothNumbers X, (hooleyDelta n : ℝ) / n) ≤
      deltaSmoothMeanConstant * Real.log (X : ℝ) * L ^ 5 := by
  classical
  have hK := deltaWeakThresholdConstant_pos
  have hV := deltaReciprocalMeanConstant_pos
  have hC := deltaHarmonicMomentConstant_bounds.1
  have hD := deltaDyadicLevelConstant_pos
  have hW := deltaDivisorSquareConstant_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogX2 : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  obtain ⟨k, hk, hpow⟩ := exists_delta_dyadic_level hX hL hloglog
  let T := deltaWeakThresholdConstant * L ^ 4
  let M := (deltaReciprocalMeanConstant + deltaHarmonicMomentConstant) * Real.log (X : ℝ)
  let B := deltaDivisorSquareConstant * Real.log (X : ℝ) ^ 4
  have hT : 0 < T := by dsimp only [T]; positivity
  have hTlo : deltaWeakThresholdConstant ≤ T := by
    have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
    dsimp only [T]
    nlinarith only [hL4, hK]
  have hmass : (∑ n ∈ deltaSmoothNumbers X, (1 : ℝ) / n) ≤
      deltaReciprocalMeanConstant * Real.log (X : ℝ) := by
    rw [deltaSmoothNumbers,
      sum_reciprocal_divisors_eq_eulerProduct (deltaPrimeProduct_squarefree X),
      primeFactors_deltaPrimeProduct]
    exact delta_prime_eulerProduct_le hX _ (fun p hp =>
      Nat.mem_primesLE.mpr ⟨(Nat.mem_primesBelow.mp hp).1.le, (Nat.mem_primesBelow.mp hp).2⟩)
  have hweak (j : ℕ) (_hj : j < k) :
      (∑ n ∈ (deltaSmoothNumbers X).filter (fun n => T * 2 ^ j < (hooleyDelta n : ℝ)),
        (1 : ℝ) / n) ≤ M / 2 ^ j := by
    have h := deltaSmooth_weak_mean hX (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      hL hbudget hloglog (A := (2 : ℝ) ^ j)
    have heq : T * 2 ^ j = deltaWeakThresholdConstant * 2 ^ j * L ^ 4 := by
      dsimp only [T]
      ring
    simpa only [heq] using h
  have hmean := finite_delta_weak_to_strong (deltaSmoothNumbers X)
    (fun n => (hooleyDelta n : ℝ)) (fun n => (1 : ℝ) / n)
    (fun n _ => by positivity) hT k hweak (sum_deltaSmoothNumbers_delta_sq_le hX)
  have htail : B / (T * 2 ^ k) ≤ deltaDivisorSquareConstant / deltaWeakThresholdConstant := by
    calc
      _ = (deltaDivisorSquareConstant / T) * (Real.log (X : ℝ) ^ 4 / 2 ^ k) := by
        dsimp only [B]
        ring
      _ ≤ (deltaDivisorSquareConstant / T) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (by positivity : (0 : ℝ) < 2 ^ k)).mpr hpow
      _ ≤ _ := by
        rw [mul_one]
        exact div_le_div_of_nonneg_left hW.le hK hTlo
  have hL45 : L ^ 4 ≤ L ^ 5 := pow_le_pow_right₀ hL (by norm_num)
  have hmain : T * (∑ n ∈ deltaSmoothNumbers X, (1 : ℝ) / n) ≤
      (deltaWeakThresholdConstant * deltaReciprocalMeanConstant) * Real.log (X : ℝ) * L ^ 5 := by
    calc
      _ ≤ T * (deltaReciprocalMeanConstant * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass hT.le
      _ ≤ _ := by
        dsimp only [T]
        have h := mul_le_mul_of_nonneg_left hL45
          (show 0 ≤ deltaWeakThresholdConstant * deltaReciprocalMeanConstant * Real.log (X : ℝ)
            by positivity)
        nlinarith only [h]
  have hmiddle : (k : ℝ) * T * M ≤
      (deltaDyadicLevelConstant * deltaWeakThresholdConstant *
        (deltaReciprocalMeanConstant + deltaHarmonicMomentConstant)) *
          Real.log (X : ℝ) * L ^ 5 := by
    calc
      _ ≤ (deltaDyadicLevelConstant * L) * T * M := by
        dsimp only [T, M]
        gcongr
      _ = _ := by dsimp only [T, M]; ring
  have htail' : deltaDivisorSquareConstant / deltaWeakThresholdConstant ≤
      (deltaDivisorSquareConstant / (deltaWeakThresholdConstant * Real.log 2)) *
        Real.log (X : ℝ) * L ^ 5 := by
    have hL5 : (1 : ℝ) ≤ L ^ 5 := one_le_pow₀ hL
    have hlogscale : Real.log 2 ≤ Real.log (X : ℝ) * L ^ 5 := by
      nlinarith only [hlogX2, mul_le_mul_of_nonneg_left hL5 hlogX.le]
    calc
      _ = (deltaDivisorSquareConstant / (deltaWeakThresholdConstant * Real.log 2)) *
          Real.log 2 := by field_simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hlogscale
          (show 0 ≤ deltaDivisorSquareConstant / (deltaWeakThresholdConstant * Real.log 2)
            by positivity)
        simpa only [mul_assoc] using h
  simp only [mul_one_div] at hmean
  apply hmean.trans
  have h := add_le_add (add_le_add hmain hmiddle) (htail.trans htail')
  apply h.trans_eq
  unfold deltaSmoothMeanConstant
  ring

/-- Mertens supplies the prime budget, giving the fifth log-log power
without any hypotheses beyond the cutoff being at least two. -/
theorem exists_deltaSmooth_harmonic_loglog_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (∑ n ∈ deltaSmoothNumbers X, (hooleyDelta n : ℝ) / n) ≤
        C * Real.log (X : ℝ) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 5 := by
  obtain ⟨C₀, hC₀, hprime⟩ := Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log
  refine ⟨deltaSmoothMeanConstant * (C₀ + 1) ^ 5, ?_, ?_⟩
  · exact mul_pos deltaSmoothMeanConstant_pos (pow_pos (by linarith) _)
  · intro X hX
    let L := max 1 (Real.log (Real.log (X : ℝ)) + C₀)
    let U := max 1 (Real.log (Real.log (X : ℝ)))
    have hL : 1 ≤ L := le_max_left _ _
    have hU : 1 ≤ U := le_max_left _ _
    have hlogU : Real.log (Real.log (X : ℝ)) ≤ U := le_max_right _ _
    have hlogL : Real.log (Real.log (X : ℝ)) ≤ L := by
      have h := le_max_right 1 (Real.log (Real.log (X : ℝ)) + C₀)
      dsimp only [L]
      linarith
    have hbudget : (∑ p ∈ X.primesBelow, (1 : ℝ) / p) ≤ L := by
      have hsum : (∑ p ∈ X.primesBelow, (1 : ℝ) / p) ≤
          Erdos697.PrimeHarmonic.sum X := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpX, hp⟩ := Nat.mem_primesBelow.mp hp
          exact Nat.mem_primesLE.mpr ⟨hpX.le, hp⟩
        · intro p hp hnot
          positivity
      have hup := (abs_le.mp (hprime X hX)).2
      have hmax := le_max_right 1 (Real.log (Real.log (X : ℝ)) + C₀)
      dsimp only [L]
      linarith
    have hLU : L ≤ (C₀ + 1) * U := by
      have hmul := mul_le_mul_of_nonneg_left hU hC₀
      apply max_le <;> nlinarith only [hU, hlogU, hmul, hC₀]
    calc
      _ ≤ deltaSmoothMeanConstant * Real.log (X : ℝ) * L ^ 5 :=
        deltaSmooth_harmonic_mean hX hL hbudget hlogL
      _ ≤ deltaSmoothMeanConstant * Real.log (X : ℝ) * ((C₀ + 1) * U) ^ 5 := by
        have hlogX : 0 ≤ Real.log (X : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hLU 5)
          (mul_nonneg deltaSmoothMeanConstant_pos.le hlogX)
      _ = _ := by dsimp only [U]; ring

end Erdos587
