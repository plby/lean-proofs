import ErdosProblems.Erdos587.HooleyMomentInduction

/-!
# The normalized second moment

At order two the mixed product is just the divisor function. Its exact
Euler product, followed by square-root cutoff iteration, supplies the
base case of the higher-moment induction.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def deltaDivisorMeanConstant : ℝ :=
  Classical.choose (exists_squarefree_divisorPower_log_bound 1)

lemma deltaDivisorMeanConstant_pos : 0 < deltaDivisorMeanConstant :=
  (Classical.choose_spec (exists_squarefree_divisorPower_log_bound 1)).1

lemma sum_deltaSmoothNumbers_divisors_le {x : ℕ} (hx : 2 ≤ x) :
    (∑ n ∈ deltaSmoothNumbers x, (n.divisors.card : ℝ) / n) ≤
      deltaDivisorMeanConstant * Real.log (x : ℝ) ^ 2 := by
  have h := (Classical.choose_spec (exists_squarefree_divisorPower_log_bound 1)).2
    x (deltaPrimeProduct x) hx (deltaPrimeProduct_squarefree x)
  change (deltaPrimeProduct x).primeFactors ⊆ Nat.primesLE x →
    (∑ n ∈ deltaSmoothNumbers x, (n.divisors.card : ℝ) ^ 1 / n) ≤
      deltaDivisorMeanConstant * Real.log (x : ℝ) ^ (2 ^ 1 : ℕ) at h
  simp only [pow_one] at h
  apply h
  rw [primeFactors_deltaPrimeProduct]
  intro p hp
  obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesLE.mpr ⟨hpx.le, hp⟩

lemma restrictedDeltaPrimeError_two_sqrt_step (G : ℕ → Prop) [DecidablePred G]
    {x : ℕ} (hx : 4 ≤ x) :
    restrictedDeltaPrimeError G 2 x ≤ restrictedDeltaPrimeError G 2 x.sqrt +
      (16 * deltaPrimeWindowConstant * deltaDivisorMeanConstant) * Real.log (x : ℝ) := by
  have hD := deltaPrimeWindowConstant_pos
  have hW := deltaDivisorMeanConstant_pos
  have hy := (delta_sqrt_cutoff_bounds hx).1
  have hyx := (delta_sqrt_cutoff_bounds hx).2.le
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogy : 0 < Real.log (x.sqrt : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x.sqrt by omega))
  have hprod : (∑ n ∈ (deltaSmoothNumbers x).filter G,
      ∑ b ∈ Finset.Icc 1 (2 / 2), 2 ^ b * (Nat.choose 2 b : ℝ) *
        (deltaMoment n (2 - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n)) ≤
      4 * deltaDivisorMeanConstant * Real.log (x : ℝ) ^ 2 := by
    have heq (n : ℕ) (hn : n ∈ deltaSmoothNumbers x) :
        (∑ b ∈ Finset.Icc 1 (2 / 2), 2 ^ b * (Nat.choose 2 b : ℝ) *
          (deltaMoment n (2 - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n)) =
        4 * ((n.divisors.card : ℝ) / n) := by
      have hn0 := (mem_deltaSmoothNumbers.mp hn).1.ne_zero
      have hc : (n.divisors.card : ℝ) ≠ 0 := by
        have hcN := Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩⟩
        exact_mod_cast Nat.ne_of_gt hcN
      norm_num [deltaMoment_one]
      field_simp
    calc
      _ = 4 * ∑ n ∈ (deltaSmoothNumbers x).filter G, (n.divisors.card : ℝ) / n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n hn => heq n (Finset.mem_filter.mp hn).1)
      _ ≤ 4 * ∑ n ∈ deltaSmoothNumbers x, (n.divisors.card : ℝ) / n := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (sum_deltaSmoothNumbers_divisors_le (by omega : 2 ≤ x)) (by norm_num : (0 : ℝ) ≤ 4)
        simpa only [mul_assoc] using h
  apply (restrictedDeltaPrimeError_block_le G 2 hy hyx).trans
  apply add_le_add le_rfl
  calc
    _ ≤ (deltaPrimeWindowConstant / Real.log (x.sqrt : ℝ)) *
        (4 * deltaDivisorMeanConstant * Real.log (x : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ _ := by
      have hratio : Real.log (x : ℝ) / Real.log (x.sqrt : ℝ) ≤ 4 :=
        (div_le_iff₀ hlogy).mpr (delta_sqrt_cutoff_log_bounds hx).1
      calc
        _ = (4 * deltaPrimeWindowConstant * deltaDivisorMeanConstant * Real.log (x : ℝ)) *
            (Real.log (x : ℝ) / Real.log (x.sqrt : ℝ)) := by ring
        _ ≤ (4 * deltaPrimeWindowConstant * deltaDivisorMeanConstant * Real.log (x : ℝ)) * 4 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by ring

noncomputable def deltaSecondErrorConstant : ℝ :=
  5 / Real.log 2 + 32 * deltaPrimeWindowConstant * deltaDivisorMeanConstant

lemma deltaSecondErrorConstant_pos : 0 < deltaSecondErrorConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD := deltaPrimeWindowConstant_pos
  have hW := deltaDivisorMeanConstant_pos
  unfold deltaSecondErrorConstant
  positivity

lemma restrictedDeltaPrimeError_two_le (G : ℕ → Prop) [DecidablePred G]
    {x : ℕ} (hx : 2 ≤ x) :
    1 + restrictedDeltaPrimeError G 2 x ≤ deltaSecondErrorConstant * Real.log (x : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD := deltaPrimeWindowConstant_pos
  have hW := deltaDivisorMeanConstant_pos
  apply delta_sqrt_recursion_log_bound (fun y => 1 + restrictedDeltaPrimeError G 2 y)
    deltaSecondErrorConstant_pos.le
    (K := 16 * deltaPrimeWindowConstant * deltaDivisorMeanConstant) _ _ _ x hx
  · unfold deltaSecondErrorConstant
    have hdiv : 0 ≤ (5 : ℝ) / Real.log 2 := by positivity
    linarith
  · intro y hy hy3
    have hsmall := restrictedDeltaPrimeError_small G 2 hy3
    have hlog : Real.log 2 ≤ Real.log (y : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    have hbase : (5 : ℝ) ≤ deltaSecondErrorConstant * Real.log 2 := by
      unfold deltaSecondErrorConstant
      have hnonneg : 0 ≤ 32 * deltaPrimeWindowConstant * deltaDivisorMeanConstant *
          Real.log 2 := by positivity
      have hcancel : (5 / Real.log 2 : ℝ) * Real.log 2 = 5 := by field_simp
      nlinarith only [hnonneg, hcancel]
    have hmono := mul_le_mul_of_nonneg_left hlog deltaSecondErrorConstant_pos.le
    norm_num at hsmall
    linarith
  · intro y hy
    have h := restrictedDeltaPrimeError_two_sqrt_step G hy
    linarith

noncomputable def deltaSecondMomentConstant : ℝ :=
  (1 + deltaTailEulerConstant) * deltaSecondErrorConstant

lemma deltaSecondMomentConstant_pos : 0 < deltaSecondMomentConstant :=
  mul_pos (by linarith [deltaTailEulerConstant_pos]) deltaSecondErrorConstant_pos

/-- Unrestricted normalized second moment, with a uniform constant and
only one reciprocal-prime budget. -/
theorem sum_deltaSmoothNumbers_harmonicDeltaMoment_two_le {x : ℕ} (hx : 2 ≤ x)
    {L : ℝ} (hL : 1 ≤ L) (hbudget : (∑ p ∈ x.primesBelow, (1 : ℝ) / p) ≤ L) :
    (∑ n ∈ deltaSmoothNumbers x, harmonicDeltaMoment n 2) ≤
      deltaSecondMomentConstant * L * Real.log (x : ℝ) := by
  have h := restrictedHarmonicDeltaMoment_of_error_bound (fun _ => True) trivial
    (fun _ _ _ => trivial) (by norm_num : 2 ≠ 0) hx deltaSecondErrorConstant_pos.le hL hbudget
    (fun y hy _ => restrictedDeltaPrimeError_two_le (fun _ => True) hy)
  simpa only [restrictedHarmonicDeltaMoment, Finset.filter_true, deltaSecondMomentConstant,
    mul_assoc] using h

end Erdos587
