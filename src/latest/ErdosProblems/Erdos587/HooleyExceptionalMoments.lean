import ErdosProblems.Erdos587.HooleyHigherMoments
import ErdosProblems.Erdos587.HooleyConcentration

/-!
# Exceptional mass and concentration after moment restriction

The summable order factor `1/q²` pays for imposing all lower-moment
constraints. On the remaining integers, one high moment controls Delta.
-/

open scoped BigOperators

namespace Erdos587

lemma sum_Icc_two_reciprocal_sq_le_one (q : ℕ) :
    (∑ j ∈ Finset.Icc 2 q, (1 : ℝ) / (j : ℝ) ^ 2) ≤ 1 := by
  by_cases hq : 1 ≤ q
  · have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (by norm_num : (1 : ℕ) ≠ 0) hq
    rw [← Finset.Icc_add_one_left_eq_Ioc] at h
    norm_num only [Nat.cast_one, inv_one, one_add_one_eq_two, ← one_div] at h
    have hinv : 0 ≤ (1 : ℝ) / q := by positivity
    linarith
  · have hq0 : q = 0 := by omega
    simp [hq0]

theorem deltaRestrictedSet_mass_bound (S : Finset ℕ) (E : ℕ → ℝ) (q : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hEone : 1 ≤ E 1) (hE : ∀ j, 2 ≤ j → j ≤ q → 0 < E j)
    (hmean : ∀ j, 2 ≤ j → j ≤ q →
      (∑ n ∈ deltaRestrictedSet S E (j - 1), harmonicDeltaMoment n j) ≤
        K * E j / (j : ℝ) ^ 2) :
    (∑ n ∈ S \ deltaRestrictedSet S E q, (1 : ℝ) / n) ≤ K := by
  by_cases hq : q = 0
  · simpa only [hq, deltaRestrictedSet_zero, Finset.sdiff_self, Finset.sum_empty] using hK
  · have hqeq : q - 1 + 1 = q := by omega
    have hbound := deltaRestrictedSet_mass_le S E (q - 1) hEone (by
      intro j hj
      rw [hqeq] at hj
      exact hE j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
    rw [hqeq] at hbound
    apply hbound.trans
    calc
      _ ≤ ∑ j ∈ Finset.Icc 2 q, K / (j : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj, hjq⟩ := Finset.mem_Icc.mp hj
        have hEj := hE j hj hjq
        calc
          _ ≤ (K * E j / (j : ℝ) ^ 2) / E j :=
            div_le_div_of_nonneg_right (hmean j hj hjq) hEj.le
          _ = _ := by field_simp
      _ = K * ∑ j ∈ Finset.Icc 2 q, (1 : ℝ) / (j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left (sum_Icc_two_reciprocal_sq_le_one q) hK
      _ = K := mul_one K

/-- A pointwise Delta bound from the retained moment and an exponential
divisor cap. The scale parameter `A` is absorbed by the envelope. -/
theorem hooleyDelta_le_of_meets_smooth_moments {n q : ℕ} (hn : n ≠ 0) (hq : q ≠ 0)
    {A B R : ℝ} (hB : 0 ≤ B) (hAB : A ≤ B) (hR : 0 ≤ R)
    (hdiv : (n.divisors.card : ℝ) ≤ A * R ^ q)
    (hmeets : MeetsDeltaMoments (deltaSmoothMomentEnvelope B) q n) :
    (hooleyDelta n : ℝ) ≤ 2 * R * (q : ℝ) ^ 3 * B := by
  have hE := deltaSmoothMomentEnvelope_nonneg hB q
  have hmoment := hmeets.moment_le hn (Nat.one_le_iff_ne_zero.mpr hq) le_rfl
  have hpower : (hooleyDelta n : ℝ) ^ q ≤ (2 * R * (q : ℝ) ^ 3 * B) ^ q := by
    calc
      _ ≤ 2 ^ q * deltaMoment n q := hooleyDelta_pow_le_two_pow_mul_deltaMoment n hq
      _ ≤ 2 ^ q * (deltaSmoothMomentEnvelope B q * (A * R ^ q)) :=
        mul_le_mul_of_nonneg_left
          (hmoment.trans (mul_le_mul_of_nonneg_left hdiv hE)) (by positivity)
      _ = (2 : ℝ) ^ q * R ^ q * (A * deltaSmoothMomentEnvelope B q) := by ring
      _ ≤ (2 : ℝ) ^ q * R ^ q * ((q : ℝ) ^ 3 * B) ^ q :=
        mul_le_mul_of_nonneg_left (mul_deltaSmoothMomentEnvelope_le_pow hB hAB hq)
          (by positivity)
      _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  exact le_of_pow_le_pow_left₀ hq (by positivity) hpower

end Erdos587
