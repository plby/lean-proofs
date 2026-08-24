import UnitFractions.ForMathlib.BasicEstimates

/-!
A uniform prime-reciprocal bound with an unspecified absolute constant.
The second Mertens theorem suffices for the fixed logarithmic losses used
here; no numerically optimized finite Mertens-product estimate is needed.
-/

open Filter
open scoped BigOperators

namespace Erdos587

theorem exists_prime_reciprocal_log_bound :
    ∃ R : ℝ, 0 < R ∧ ∀ N : ℕ, 3 ≤ N →
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p) ≤
        R * Real.log (3 * Real.log (N : ℝ)) := by
  obtain ⟨c, hc⟩ := prime_reciprocal.bound
  have hcnat := tendsto_natCast_atTop_atTop.eventually hc
  have hlarge : ∀ᶠ N : ℕ in atTop, max 1 |c| ≤ Real.log (N : ℝ) :=
    tendsto_log_coe_at_top.eventually_ge_atTop _
  have hlarge' : ∀ᶠ N : ℕ in atTop,
      max 0 (meissel_mertens + 1) ≤ Real.log (Real.log (N : ℝ)) :=
    tendsto_log_log_coe_at_top.eventually_ge_atTop _
  have hevent : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p) ≤
        2 * Real.log (3 * Real.log (N : ℝ)) := by
    filter_upwards [hcnat, hlarge, hlarge'] with N hN hlog hloglog
    have hlogpos : 0 < Real.log (N : ℝ) :=
      zero_lt_one.trans_le ((le_max_left 1 |c|).trans hlog)
    have hmul : c * ‖(Real.log (N : ℝ))⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hlogpos.le)]
      exact (div_le_one hlogpos).mpr
        ((le_abs_self c).trans ((le_max_right 1 |c|).trans hlog))
    have herr := (Real.le_norm_self _).trans (hN.trans hmul)
    have hsum : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p) ≤
        Real.log (Real.log (N : ℝ)) + meissel_mertens + 1 := by
      simpa [prime_summatory, one_div] using (sub_le_iff_le_add'.mp herr)
    have hnonneg := (le_max_left 0 (meissel_mertens + 1)).trans hloglog
    have hconst := (le_max_right 0 (meissel_mertens + 1)).trans hloglog
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogpos.ne']
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 (N₀ : ℝ), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro N hN
  have hlog : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ N by exact_mod_cast hN)
    linarith [Real.log_three_gt_d9]
  have hloglog : (1 : ℝ) ≤ Real.log (3 * Real.log (N : ℝ)) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ 3 * Real.log (N : ℝ) by linarith)
    linarith [Real.log_three_gt_d9]
  by_cases hbig : N₀ ≤ N
  · exact (hN₀ N hbig).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hsum : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p) ≤ N := by
      calc
        _ ≤ ∑ _p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact div_le_one_of_le₀ (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
            (Nat.cast_nonneg p)
        _ ≤ N := by
          simpa using (Nat.cast_le (α := ℝ)).mpr
            ((Finset.card_filter_le _ _).trans (by simp))
    have hR : (N : ℝ) ≤ max 2 (N₀ : ℝ) :=
      (Nat.cast_le.mpr (by omega)).trans (le_max_right _ _)
    exact hsum.trans (hR.trans (le_mul_of_one_le_right (by positivity) hloglog))

noncomputable def primeReciprocalConstant : ℝ :=
  Classical.choose exists_prime_reciprocal_log_bound

theorem primeReciprocalConstant_pos : 0 < primeReciprocalConstant :=
  (Classical.choose_spec exists_prime_reciprocal_log_bound).1

theorem reciprocal_prime_sum_le_log_bound (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p) ≤
      primeReciprocalConstant * Real.log (3 * Real.log (N : ℝ)) :=
  (Classical.choose_spec exists_prime_reciprocal_log_bound).2 N hN

end Erdos587
