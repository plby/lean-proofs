/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedSlice
import ErdosProblems.Erdos4b.FGKMTMajorantSupport

/-! # Exact arbitrary-pin slices of the full long-cutoff majorant -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem oneLongTensor_insertNth_same (k m : ℕ) (j : Fin (m + 1))
    (x : ℝ) (t : Fin m → ℝ) :
    oneLongTensor k (m + 1) j (j.insertNth x t) =
      dimensionLongFactor k x * ∏ i, dimensionProfileFactor k (t i) := by
  rw [oneLongTensor, Fin.prod_univ_succAbove _ j]
  simp [oneLongFactor, Fin.succAbove_ne]

theorem oneLongTensor_insertNth_succAbove (k m : ℕ) (j : Fin (m + 1))
    (i : Fin m) (x : ℝ) (t : Fin m → ℝ) :
    oneLongTensor k (m + 1) (j.succAbove i) (j.insertNth x t) =
      dimensionProfileFactor k x * oneLongTensor k m i t := by
  rw [oneLongTensor, Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, oneLongFactor,
    if_neg (Ne.symm (Fin.succAbove_ne j i))]
  congr 1
  apply Finset.prod_congr rfl
  intro q _hq
  simp [oneLongFactor]

theorem sieveProfileMajorant_insertNth (k m : ℕ) (j : Fin (m + 1))
    (x : ℝ) (t : Fin m → ℝ) :
    sieveProfileMajorant k (m + 1) (j.insertNth x t) =
      sieveProfileMajorant k (m + 1) (Fin.cons x t) := by
  rw [sieveProfileMajorant, Fin.sum_univ_succAbove _ j, oneLongTensor_insertNth_same]
  simp_rw [oneLongTensor_insertNth_succAbove]
  rw [← Finset.mul_sum, sieveProfileMajorant_cons]
  rfl

theorem sieveProfileMajorant_pinnedBaseTuple {α : Type*} [Fintype α]
    (k R : ℕ) {m : ℕ} (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    sieveProfileMajorant k (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) =
      sieveProfileMajorant k (m + 1) (Fin.cons
        (Real.log (assignmentPrimeProduct p a) / Real.log R)
        (sieveLogTuple R (assignmentPrimeTuple p r))) := by
  rw [pinnedBaseTuple_eq_insertNth, sieveLogTuple_insertNth, sieveProfileMajorant_insertNth]

theorem sieveProfileMajorant_logSlice_zero_of_sq_le {k R : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hR : 1 < R) (m : ℕ) (t : Fin m → ℝ)
    {a : ℕ} (ha : R ^ 2 ≤ a) :
    sieveProfileMajorant k (m + 1) (Fin.cons (Real.log a / Real.log R) t) = 0 := by
  apply sieveProfileMajorant_zero_of_coord_ge_two hk hlog (0 : Fin (m + 1))
  simp only [Fin.cons_zero]
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  apply (le_div_iff₀ hL).mpr
  calc
    2 * Real.log R = Real.log (R ^ 2 : ℕ) := by
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    _ ≤ Real.log a := Real.log_le_log
      (by exact_mod_cast pow_pos (by omega : 0 < R) 2) (by exact_mod_cast ha)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveProfileMajorant_pinnedBaseTuple
#print axioms Erdos4b.FGKMT.sieveProfileMajorant_logSlice_zero_of_sq_le
