import ErdosProblems.Erdos321.FiniteRecurrence

namespace Erdos321

/-- Logarithmic form of F-029's exact bad-prime power bound. -/
theorem chosenExtremizer_restrictedBad_log_bound
    {N T t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
        Real.log (T + 1) ≤
      (3 ^ extremalSize t : ℕ) *
        Real.log (extremalSize t * t.factorial) := by
  have hpow := chosenExtremizer_restrictedBad_power_bound (N := N) ht
  have hOne : 1 ≤ extremalSize t :=
    one_le_extremalSize (Finset.mem_Icc.mp ht).1
  have hBasePos : 0 < extremalSize t * t.factorial :=
    Nat.mul_pos hOne (Nat.factorial_pos t)
  have hpowR :
      (((T + 1) ^ (badPrimeSetFrom (T + 1) N
        (chosenExtremizer t)).card : ℕ) : ℝ) ≤
      (((extremalSize t * t.factorial) ^ (3 ^ extremalSize t) : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hLog := Real.log_le_log
    (by positivity : (0 : ℝ) < ((T + 1) ^
      (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card : ℕ))
    hpowR
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_mul, Real.log_pow] using hLog

/-- A closed elementary version using only the cofactor endpoint `t`. -/
theorem chosenExtremizer_restrictedBad_log_bound_coarse
    {N T t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card *
        Real.log (T + 1) ≤
      (3 ^ t : ℕ) * (t + 1) * Real.log t := by
  have htData := Finset.mem_Icc.mp ht
  have htOne : t ∈ Finset.Icc 1 T := ht
  have hR : extremalSize t ≤ t := extremalSize_le t
  have h3 : (3 ^ extremalSize t : ℕ) ≤ 3 ^ t :=
    Nat.pow_le_pow_right (by omega) hR
  have hFact : extremalSize t * t.factorial ≤ t ^ (t + 1) := by
    calc
      extremalSize t * t.factorial ≤ t * (t ^ t) :=
        Nat.mul_le_mul hR (Nat.factorial_le_pow t)
      _ = t ^ (t + 1) := by rw [pow_succ]; ac_rfl
  have hbasepos : 0 < extremalSize t * t.factorial :=
    Nat.mul_pos (one_le_extremalSize (by omega)) (Nat.factorial_pos t)
  have hLogBase : Real.log (extremalSize t * t.factorial) ≤
      (t + 1) * Real.log t := by
    calc
      Real.log (extremalSize t * t.factorial) ≤ Real.log (t ^ (t + 1)) :=
        Real.log_le_log (by exact_mod_cast hbasepos) (by exact_mod_cast hFact)
      _ = (t + 1) * Real.log t := by
        rw [Real.log_pow]
        norm_num
  calc
    _ ≤ (3 ^ extremalSize t : ℕ) *
        Real.log (extremalSize t * t.factorial) :=
      chosenExtremizer_restrictedBad_log_bound htOne
    _ ≤ (3 ^ t : ℕ) * Real.log (extremalSize t * t.factorial) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast h3
      · apply Real.log_nonneg
        exact_mod_cast hbasepos
    _ ≤ (3 ^ t : ℕ) * ((t + 1) * Real.log t) := by
      apply mul_le_mul_of_nonneg_left hLogBase
      positivity
    _ = _ := by ring

end Erdos321
