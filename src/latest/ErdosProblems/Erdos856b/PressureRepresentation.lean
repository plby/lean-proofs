import ErdosProblems.Erdos856b.UpperCapacity

/-! # The finite uniform representation of the cosunflower pressure -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

theorem uniformRoot_eq_exp {k n r : ℕ} (hk : 3 ≤ k) (hr : r ≤ n)
    {z : ℝ} (hz : 0 < z) :
    ((M k n r : ℝ) * z ^ r) ^ (1 / (n : ℝ)) =
      exp ((log (M k n r) + r * log z) / n) := by
  have hM : (0 : ℝ) < M k n r := by exact_mod_cast M_pos hk hr
  rw [rpow_def_of_pos (mul_pos hM (pow_pos hz _)),
    log_mul hM.ne' (pow_pos hz _).ne', log_pow]
  congr 1
  ring

/-- Equation (4.4): the pressure is exactly the supremum over finite uniform blocks.
The rank-zero layer is included here, unlike in the formula for the exponent. -/
theorem cosPressure_eq_uniform_sup {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    cosPressure k z = sSup {v : ℝ | ∃ n r : ℕ, 0 < n ∧ r ≤ n ∧
      v = ((M k n r : ℝ) * z ^ r) ^ (1 / (n : ℝ))} := by
  let S : Set ℝ := {v | ∃ n r : ℕ, 0 < n ∧ r ≤ n ∧
    v = ((M k n r : ℝ) * z ^ r) ^ (1 / (n : ℝ))}
  have hSne : (1 : ℝ) ∈ S := by
    refine ⟨1, 0, by omega, by omega, ?_⟩
    simp [M_rank_zero hk]
  have hbound : ∀ v ∈ S, v ≤ cosPressure k z := by
    rintro v ⟨n, r, hn, hr, rfl⟩
    rw [uniformRoot_eq_exp hk hr hz]
    exact exp_le_exp.mpr (log_M_weight_div_le_logPressure hk hn hr hz)
  have hSbdd : BddAbove S := ⟨cosPressure k z, hbound⟩
  have hSpos : 0 < sSup S := zero_lt_one.trans_le (le_csSup hSbdd hSne)
  apply le_antisymm
  · have hlog : logPressure k z ≤ log (sSup S) := by
      apply csSup_le ⟨0, zero_mem_logPressureScores hk z⟩
      rintro v ⟨n, r, hn, hr, rfl⟩
      have hmem : ((M k n r : ℝ) * z ^ r) ^ (1 / (n : ℝ)) ∈ S :=
        ⟨n, r, hn, hr, rfl⟩
      have h := le_csSup hSbdd hmem
      rw [uniformRoot_eq_exp hk hr hz] at h
      simpa only [log_exp] using log_le_log (exp_pos _) h
    exact (exp_le_exp.mpr hlog).trans_eq (exp_log hSpos)
  · exact csSup_le ⟨1, hSne⟩ hbound

end Erdos856b
