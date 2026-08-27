/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentVariation

/-!
# Coordinate support of the full majorant

Every one-long-factor summand vanishes if any coordinate is at least
two. At logarithmic integer coordinates the correct support is a full
box of side `R^2`; no product-radius cutoff is asserted.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem oneLongFactor_zero_of_two_le {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i q : Fin j) {t : ℝ} (ht : 2 ≤ t) :
    oneLongFactor k i q t = 0 := by
  unfold oneLongFactor
  split_ifs
  · exact sieveFactor_zero_of_ge (by norm_num : (0 : ℝ) < 2) ht (sieveProfileScale k)
  · exact dimensionProfileFactor_zero_of_one_le hk hlog (by linarith)

theorem oneLongTensor_zero_of_coord_ge_two {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i : Fin j) {t : Fin j → ℝ}
    (q : Fin j) (ht : 2 ≤ t q) : oneLongTensor k j i t = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ q) (oneLongFactor_zero_of_two_le hk hlog i q ht)

theorem sieveProfileMajorant_zero_of_coord_ge_two {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {t : Fin j → ℝ} (q : Fin j) (ht : 2 ≤ t q) :
    sieveProfileMajorant k j t = 0 :=
  Finset.sum_eq_zero fun i _hi => oneLongTensor_zero_of_coord_ge_two hk hlog i q ht

theorem sieveLogTuple_ge_two_of_sq_le {R j : ℕ} (hR : 1 < R)
    (r : Fin j → ℕ) (q : Fin j) (hq : R ^ 2 ≤ r q) :
    2 ≤ sieveLogTuple R r q := by
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  apply (le_div_iff₀ hL).mpr
  calc
    2 * Real.log R = Real.log (R ^ 2 : ℕ) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    _ ≤ Real.log (r q) := Real.log_le_log
      (by exact_mod_cast pow_pos (by omega : 0 < R) 2) (by exact_mod_cast hq)

theorem majorant_logTuple_zero_of_coord_ge_sq {k R j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hR : 1 < R) (r : Fin j → ℕ)
    (q : Fin j) (hq : R ^ 2 ≤ r q) :
    sieveProfileMajorant k j (sieveLogTuple R r) = 0 :=
  sieveProfileMajorant_zero_of_coord_ge_two hk hlog q (sieveLogTuple_ge_two_of_sq_le hR r q hq)

theorem primeAssignmentMajorant_coord_lt_sq {α : Type*} [Fintype α]
    {k R : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) (hR : 1 < R)
    (p : α → ℕ) {r : α → Option (Fin k)} (hr : primeAssignmentMajorant k R p r ≠ 0)
    (i : Fin k) : assignmentPrimeTuple p r i < R ^ 2 := by
  by_contra hnot
  exact hr (majorant_logTuple_zero_of_coord_ge_sq hk hlog hR _ i (by omega))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveProfileMajorant_zero_of_coord_ge_two
#print axioms Erdos4b.FGKMT.primeAssignmentMajorant_coord_lt_sq
