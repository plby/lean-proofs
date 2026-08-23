import ErdosProblems.Erdos248.CorrelationBounds
import ErdosProblems.Erdos248.PrimeSumBounds

/-!
# Erdős Problem 248: sums of medium-prime displacement factors

This file translates the displacement parameter used by the finite-prime
transforms into the normalized logarithm appearing in the elementary prime
sum estimates.  It also records coarse summable bounds for the `(p - 1)`
remainders in the one- and two-prime transforms.
-/

noncomputable section

open scoped BigOperators

namespace Erdos248

/-- On a near coordinate the transform displacement is exactly logarithm
normalized by that coordinate's radius. -/
theorem primeLogDisplacement_eq_log_div_log_shiftRadius
    {K p : ℕ} (m : nearShifts K) :
    primeLogDisplacement K m p =
      Real.log (p : ℝ) / Real.log (shiftRadius K m : ℝ) := by
  have hmK : (m : ℕ) ≤ K := (mem_nearShifts.mp m.2).2
  have hglobal : Real.log (globalRadius K : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast one_lt_globalRadius K))
  have hradius : Real.log (shiftRadius K m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast one_lt_shiftRadius K m))
  have hpow : (((100 ^ (m : ℕ) : ℕ) : ℝ)) ≠ 0 := by positivity
  have hscale := log_shiftRadius_div_log_globalRadius (K := K) hmK
  have hscaleEq :
      Real.log (shiftRadius K m : ℝ) *
          (((100 ^ (m : ℕ) : ℕ) : ℝ)) =
        Real.log (globalRadius K : ℝ) := by
    have hraw := (div_eq_iff hglobal).mp hscale
    calc
      Real.log (shiftRadius K m : ℝ) *
            (((100 ^ (m : ℕ) : ℕ) : ℝ)) =
          ((1 : ℝ) / (((100 ^ (m : ℕ) : ℕ) : ℝ)) *
              Real.log (globalRadius K : ℝ)) *
            (((100 ^ (m : ℕ) : ℕ) : ℝ)) := by rw [hraw]
      _ = Real.log (globalRadius K : ℝ) := by field_simp
  have hRadiusEq :
      Real.log (shiftRadius K m : ℝ) =
        Real.log (globalRadius K : ℝ) /
          (((100 ^ (m : ℕ) : ℕ) : ℝ)) :=
    (eq_div_iff hpow).2 hscaleEq
  unfold primeLogDisplacement
  rw [hRadiusEq]
  field_simp [hglobal, hpow]

/-- A medium-prime displacement lies in the unit interval. -/
theorem primeLogDisplacement_le_one_of_mem_mediumPrimes
    {K k p : ℕ} (m : nearShifts K) (hmk : (m : ℕ) = k)
    (hp : p ∈ mediumPrimes K k) :
    primeLogDisplacement K m p ≤ 1 := by
  rw [primeLogDisplacement_eq_log_div_log_shiftRadius, hmk]
  have hpData := mem_primesBetween.mp hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.2.2.pos
  have hRPos : (0 : ℝ) < shiftRadius K k := by
    exact_mod_cast shiftRadius_pos K k
  have hlogR : 0 < Real.log (shiftRadius K k : ℝ) :=
    Real.log_pos (by exact_mod_cast one_lt_shiftRadius K k)
  have hlogLe : Real.log (p : ℝ) ≤
      Real.log (shiftRadius K k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hpPos)
      (by simpa only [Set.mem_Ioi] using hRPos)
      (by exact_mod_cast hpData.2.1)
  exact (div_le_iff₀ hlogR).2 (by nlinarith)

/-- The quadratic displacement sum is the normalized logarithmic prime sum. -/
theorem sum_mediumPrimes_primeLogDisplacement_sq_div_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p ^ 2 / (p : ℝ)) ≤
      normalizedPrimeLogSquareConstant := by
  simpa only [primeLogDisplacement_eq_log_div_log_shiftRadius] using
    sum_mediumPrimes_normalized_log_sq_le K (m : ℕ)

/-- The linear displacement sum has the same uniform majorant. -/
theorem sum_mediumPrimes_primeLogDisplacement_div_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p / (p : ℝ)) ≤
      normalizedPrimeLogSquareConstant := by
  have hlogR : 0 < Real.log (shiftRadius K m : ℝ) :=
    Real.log_pos (by exact_mod_cast one_lt_shiftRadius K m)
  simp_rw [primeLogDisplacement_eq_log_div_log_shiftRadius]
  calc
    (∑ p ∈ mediumPrimes K m,
        (Real.log (p : ℝ) / Real.log (shiftRadius K m : ℝ)) /
          (p : ℝ)) =
        (1 / Real.log (shiftRadius K m : ℝ)) *
          (∑ p ∈ mediumPrimes K m,
            Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (1 / Real.log (shiftRadius K m : ℝ)) *
        BoundedGaps.Maynard.primeLogHarmonicSum (shiftRadius K m) := by
      apply mul_le_mul_of_nonneg_left
      · unfold BoundedGaps.Maynard.primeLogHarmonicSum
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (primesBetween_subset_primesLE (tinyCutoff K) (shiftRadius K m))
        intro p hp hpnot
        have hpPrime := Nat.prime_of_mem_primesLE hp
        positivity
      · positivity
    _ ≤ (1 / Real.log (shiftRadius K m : ℝ)) *
        (Real.log (shiftRadius K m : ℝ) + primeLogMertensBound) := by
      gcongr
      exact primeLogHarmonicSum_le (shiftRadius K m)
    _ = 1 + primeLogMertensBound /
        Real.log (shiftRadius K m : ℝ) := by
      field_simp
    _ ≤ 1 + primeLogMertensBound / Real.log 2 := by
      have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have htwoR : (2 : ℝ) ≤ shiftRadius K m := by
        exact_mod_cast (one_lt_shiftRadius K m)
      have hlogTwoR : Real.log (2 : ℝ) ≤
          Real.log (shiftRadius K m : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; norm_num)
          (by simp only [Set.mem_Ioi]; positivity) htwoR
      have hquot := div_le_div_of_nonneg_left primeLogMertensBound_nonneg
        hlogTwo hlogTwoR
      linarith
    _ = normalizedPrimeLogSquareConstant := rfl

/-- For `p ≥ 2`, replacing `p - 1` by `p` costs at most a factor four
in a reciprocal square. -/
theorem one_div_nat_mul_pred_sq_le_four_div_sq
    {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ) /
        ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2)) ≤
      4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < p := by positivity
  have hpredPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hp))
  have hpred : (p : ℝ) / 2 ≤ ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    linarith
  have hsq : (p : ℝ) ^ 2 ≤
      4 * (((p - 1 : ℕ) : ℝ) ^ 2) := by
    have := (sq_le_sq₀ (by positivity) (by positivity)).mpr hpred
    nlinarith
  rw [show 4 * ((1 : ℝ) / (p : ℝ) ^ 2) =
      4 / (p : ℝ) ^ 2 by ring]
  apply (div_le_div_iff₀
    (mul_pos hpPos (sq_pos_of_pos hpredPos))
    (sq_pos_of_pos hpPos)).2
  have hpOne : (1 : ℝ) ≤ p := by linarith
  have hpredSq : 0 ≤ (((p - 1 : ℕ) : ℝ) ^ 2) := sq_nonneg _
  nlinarith

/-- The basic `(p - 1)^{-2}` remainder in a medium-prime event has one
inverse-cutoff of saving. -/
theorem sum_mediumPrimes_one_div_mul_pred_sq_le
    (K k : ℕ) :
    (∑ p ∈ mediumPrimes K k,
        (1 : ℝ) /
          ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) ≤
      8 / ((tinyCutoff K + 1 : ℕ) : ℝ) := by
  calc
    (∑ p ∈ mediumPrimes K k,
        (1 : ℝ) /
          ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) ≤
        ∑ p ∈ mediumPrimes K k,
          4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_nat_mul_pred_sq_le_four_div_sq
        (mem_primesBetween.mp hp).2.2.two_le
    _ = 4 * (∑ p ∈ mediumPrimes K k,
        (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (2 / ((tinyCutoff K + 1 : ℕ) : ℝ)) := by
      gcongr
      exact sum_mediumPrimes_inv_sq_le K k
    _ = 8 / ((tinyCutoff K + 1 : ℕ) : ℝ) := by ring

/-- The analogous estimate with a single factor of `p - 1`. -/
theorem one_div_nat_mul_pred_le_two_div_sq
    {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ) / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
      2 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < p := by positivity
  have hpredPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hp))
  have hpred : (p : ℝ) / 2 ≤ ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    linarith
  rw [show 2 * ((1 : ℝ) / (p : ℝ) ^ 2) =
      2 / (p : ℝ) ^ 2 by ring]
  apply (div_le_div_iff₀ (mul_pos hpPos hpredPos)
    (sq_pos_of_pos hpPos)).2
  nlinarith

theorem sum_mediumPrimes_one_div_mul_pred_le
    (K k : ℕ) :
    (∑ p ∈ mediumPrimes K k,
        (1 : ℝ) / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) ≤
      4 / ((tinyCutoff K + 1 : ℕ) : ℝ) := by
  calc
    (∑ p ∈ mediumPrimes K k,
        (1 : ℝ) / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) ≤
        ∑ p ∈ mediumPrimes K k,
          2 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_nat_mul_pred_le_two_div_sq
        (mem_primesBetween.mp hp).2.2.two_le
    _ = 2 * (∑ p ∈ mediumPrimes K k,
        (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (2 / ((tinyCutoff K + 1 : ℕ) : ℝ)) := by
      gcongr
      exact sum_mediumPrimes_inv_sq_le K k
    _ = 4 / ((tinyCutoff K + 1 : ℕ) : ℝ) := by ring

/-- A displacement factor does not enlarge the singly shifted reciprocal
tail. -/
theorem sum_mediumPrimes_displacement_div_mul_pred_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p /
          ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) ≤
      4 / ((tinyCutoff K + 1 : ℕ) : ℝ) := by
  calc
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p /
          ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) ≤
        ∑ p ∈ mediumPrimes K m,
          (1 : ℝ) /
            ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hδ0 := primeLogDisplacement_nonneg
        (mem_primesBetween.mp hp).2.2.one_le m
      have hδ1 := primeLogDisplacement_le_one_of_mem_mediumPrimes
        m rfl hp
      have hden : 0 ≤ (p : ℝ) * ((p - 1 : ℕ) : ℝ) := by positivity
      exact div_le_div_of_nonneg_right hδ1 hden
    _ ≤ 4 / ((tinyCutoff K + 1 : ℕ) : ℝ) :=
      sum_mediumPrimes_one_div_mul_pred_le K m

/-- Two displacement factors likewise do not enlarge the squared
`(p - 1)` tail. -/
theorem sum_mediumPrimes_displacement_sq_div_mul_pred_sq_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p ^ 2 /
          ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) ≤
      8 / ((tinyCutoff K + 1 : ℕ) : ℝ) := by
  calc
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p ^ 2 /
          ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) ≤
        ∑ p ∈ mediumPrimes K m,
          (1 : ℝ) /
            ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hδ0 := primeLogDisplacement_nonneg
        (mem_primesBetween.mp hp).2.2.one_le m
      have hδ1 := primeLogDisplacement_le_one_of_mem_mediumPrimes
        m rfl hp
      have hδsq : primeLogDisplacement K m p ^ 2 ≤ 1 := by nlinarith
      have hden : 0 ≤
          (p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2) := by positivity
      exact div_le_div_of_nonneg_right hδsq hden
    _ ≤ 8 / ((tinyCutoff K + 1 : ℕ) : ℝ) :=
      sum_mediumPrimes_one_div_mul_pred_sq_le K m

/-- The pure `(K/(p-1))^2` contribution to the one-prime transform has an
inverse-cutoff saving. -/
theorem sum_mediumPrimes_K_div_pred_sq_div_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        ((K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ)) ≤
      8 * (K : ℝ) ^ 2 /
        ((tinyCutoff K + 1 : ℕ) : ℝ) := by
  calc
    (∑ p ∈ mediumPrimes K m,
        ((K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ)) =
        (K : ℝ) ^ 2 *
          (∑ p ∈ mediumPrimes K m,
            (1 : ℝ) /
              ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (K : ℝ) ^ 2 *
        (8 / ((tinyCutoff K + 1 : ℕ) : ℝ)) := by
      gcongr
      exact sum_mediumPrimes_one_div_mul_pred_sq_le K m
    _ = 8 * (K : ℝ) ^ 2 /
        ((tinyCutoff K + 1 : ℕ) : ℝ) := by ring

/-- Bundled bound for the squared one-prime displacement appearing in
`mediumSinglePrimeEventMass_le`. -/
theorem sum_mediumPrimes_singleDisplacementCost_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        (2 * primeLogDisplacement K m p +
          (K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ)) ≤
      8 * normalizedPrimeLogSquareConstant +
        16 * (K : ℝ) ^ 2 /
          ((tinyCutoff K + 1 : ℕ) : ℝ) := by
  let δ : ℕ → ℝ := fun p => primeLogDisplacement K m p
  let a : ℕ → ℝ := fun p => (K : ℝ) / ((p - 1 : ℕ) : ℝ)
  calc
    (∑ p ∈ mediumPrimes K m, (2 * δ p + a p) ^ 2 / (p : ℝ)) ≤
        ∑ p ∈ mediumPrimes K m,
          (8 * δ p ^ 2 / (p : ℝ) + 2 * a p ^ 2 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPos : (0 : ℝ) < p := by
        exact_mod_cast (mem_primesBetween.mp hp).2.2.pos
      rw [← add_div]
      apply (div_le_div_iff_of_pos_right hpPos).2
      nlinarith [sq_nonneg (2 * δ p - a p)]
    _ = 8 * (∑ p ∈ mediumPrimes K m, δ p ^ 2 / (p : ℝ)) +
        2 * (∑ p ∈ mediumPrimes K m, a p ^ 2 / (p : ℝ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ ≤ 8 * normalizedPrimeLogSquareConstant +
        2 * (8 * (K : ℝ) ^ 2 /
          ((tinyCutoff K + 1 : ℕ) : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (sum_mediumPrimes_primeLogDisplacement_sq_div_le m) (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (by simpa [a] using sum_mediumPrimes_K_div_pred_sq_div_le m)
          (by norm_num)
    _ = 8 * normalizedPrimeLogSquareConstant +
        16 * (K : ℝ) ^ 2 /
          ((tinyCutoff K + 1 : ℕ) : ℝ) := by ring

/-- Product form used for the leading two-prime displacement term. -/
theorem sq_sum_mediumPrimes_primeLogDisplacement_div_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p / (p : ℝ)) ^ 2 ≤
      normalizedPrimeLogSquareConstant ^ 2 := by
  have hsum0 : 0 ≤ ∑ p ∈ mediumPrimes K m,
      primeLogDisplacement K m p / (p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg
      (primeLogDisplacement_nonneg
        (mem_primesBetween.mp hp).2.2.one_le m)
      (by positivity)
  exact (sq_le_sq₀ hsum0 normalizedPrimeLogSquareConstant_nonneg).mpr
    (sum_mediumPrimes_primeLogDisplacement_div_le m)

/-- Product form for the first `(p - 1)^{-2}` cross remainder. -/
theorem mul_sum_mediumPredSq_sum_displacementSq_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        (1 : ℝ) /
          ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
      (∑ p ∈ mediumPrimes K m,
        primeLogDisplacement K m p ^ 2 / (p : ℝ)) ≤
      (8 / ((tinyCutoff K + 1 : ℕ) : ℝ)) *
        normalizedPrimeLogSquareConstant := by
  apply mul_le_mul
    (sum_mediumPrimes_one_div_mul_pred_sq_le K m)
    (sum_mediumPrimes_primeLogDisplacement_sq_div_le m)
  · apply Finset.sum_nonneg
    intro p hp
    positivity
  · positivity

/-- Product form for the second two-prime cross remainder. -/
theorem mul_sum_mediumPredSq_sum_singleDisplacementCost_le
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
        (1 : ℝ) /
          ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
      (∑ p ∈ mediumPrimes K m,
        (2 * primeLogDisplacement K m p +
          (K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ)) ≤
      (8 / ((tinyCutoff K + 1 : ℕ) : ℝ)) *
        (8 * normalizedPrimeLogSquareConstant +
          16 * (K : ℝ) ^ 2 /
            ((tinyCutoff K + 1 : ℕ) : ℝ)) := by
  apply mul_le_mul
    (sum_mediumPrimes_one_div_mul_pred_sq_le K m)
    (sum_mediumPrimes_singleDisplacementCost_le m)
  · apply Finset.sum_nonneg
    intro p hp
    positivity
  · positivity

end Erdos248
