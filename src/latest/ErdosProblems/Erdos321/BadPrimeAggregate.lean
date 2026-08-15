import ErdosProblems.Erdos321.BadPrimeLogBound

namespace Erdos321

/-- Aggregate cardinality-weighted bad-prime loss in the sharp lower
recurrence. -/
theorem sum_restrictedBad_mul_extremalSize_le
    {N T : ℕ} (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T,
      (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
        extremalSize t) ≤
      3 ^ T * T ^ 2 * (T + 1) := by
  have hlog : 0 < Real.log (T + 1) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < T + 1 by omega)
  have hPer (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
      ((badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
          extremalSize t : ℕ) * Real.log (T + 1) ≤
        (3 ^ T * T * (T + 1) : ℕ) * Real.log (T + 1) := by
    have htData := Finset.mem_Icc.mp ht
    have hbad := chosenExtremizer_restrictedBad_log_bound_coarse (N := N) ht
    have hR : extremalSize t ≤ T :=
      (extremalSize_le t).trans htData.2
    have h3 : 3 ^ t ≤ 3 ^ T := Nat.pow_le_pow_right (by omega) htData.2
    have hlogt : Real.log t ≤ Real.log (T + 1) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact_mod_cast htData.1)
        (by simp only [Set.mem_Ioi]; exact_mod_cast (show 0 < T + 1 by omega))
        (by exact_mod_cast (htData.2.trans (Nat.le_add_right T 1)))
    calc
      ((badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
          extremalSize t : ℕ) * Real.log (T + 1) =
        extremalSize t *
          ((badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
            Real.log (T + 1)) := by push_cast; ring
      _ ≤ extremalSize t * ((3 ^ t : ℕ) * (t + 1) * Real.log t) := by
        gcongr
      _ ≤ T * ((3 ^ t : ℕ) * (t + 1) * Real.log t) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hR
        · positivity
      _ ≤ T * ((3 ^ T : ℕ) * (t + 1) * Real.log t) := by
        gcongr
      _ ≤ T * ((3 ^ T : ℕ) * (T + 1) * Real.log t) := by
        gcongr
        exact_mod_cast htData.2
      _ ≤ T * ((3 ^ T : ℕ) * (T + 1) * Real.log (T + 1)) := by
        gcongr
      _ = (3 ^ T * T * (T + 1) : ℕ) * Real.log (T + 1) := by
        push_cast
        ring
  have hSumReal :
      ((∑ t ∈ Finset.Icc 1 T,
        (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
          extremalSize t : ℕ) : ℝ) * Real.log (T + 1) ≤
        (3 ^ T * T ^ 2 * (T + 1) : ℕ) * Real.log (T + 1) := by
    push_cast
    rw [Finset.sum_mul]
    calc
      (∑ t ∈ Finset.Icc 1 T,
        ((badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card : ℝ) *
          extremalSize t * Real.log (T + 1)) ≤
        ∑ _t ∈ Finset.Icc 1 T,
          (3 ^ T * T * (T + 1) : ℕ) * Real.log (T + 1) := by
        apply Finset.sum_le_sum
        intro t ht
        simpa [Nat.cast_mul] using hPer t ht
      _ = (3 : ℝ) ^ T * (T : ℝ) ^ 2 * (T + 1) *
          Real.log (T + 1) := by
        simp
        ring
  have hCast :
      ((∑ t ∈ Finset.Icc 1 T,
        (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
          extremalSize t : ℕ) : ℝ) ≤
        (3 ^ T * T ^ 2 * (T + 1) : ℕ) := by
    apply le_of_mul_le_mul_right (a := Real.log (T + 1))
      (b := ((∑ t ∈ Finset.Icc 1 T,
        (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
          extremalSize t : ℕ) : ℝ))
      (c := ((3 ^ T * T ^ 2 * (T + 1) : ℕ) : ℝ))
    · simpa using hSumReal
    · exact hlog
  exact_mod_cast hCast

end Erdos321
