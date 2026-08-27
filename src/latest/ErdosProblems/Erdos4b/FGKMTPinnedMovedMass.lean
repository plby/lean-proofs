/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMovedPrimeMass
import ErdosProblems.Erdos4b.FGKMTAssignmentEulerMoment
import ErdosProblems.Erdos4b.FGKMTSieveLocal
import Mathlib.Algebra.BigOperators.Field

/-!
# Uniform absolute masses in the pinned inverse transform

Each moved prime has `k-1` coordinate choices and denominator
`(p-1)*(p-k)`. The existing integer tails give total prime mass at
most `4/k` and logarithmic prime mass at most `16`, before any
coprimality restriction. Finite Euler expansion then gives dimension-
independent bounds for the complete moved-assignment sums.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def pinnedMovedWeight (k p : ℝ) : ℝ := 1 / ((p - 1) * (p - k))

theorem pinnedMovedWeight_nonneg {k p : ℝ} (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    0 ≤ pinnedMovedWeight k p := by
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hk hp
  unfold pinnedMovedWeight
  exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))

theorem pinnedMovedWeight_le {k p : ℝ} (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    (k - 1) * pinnedMovedWeight k p ≤ (k ^ 2 / (p - k) ^ 2) / k := by
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hk hp
  have hk0 : 0 < k := by linarith
  have hpk : 0 < p - k := by linarith
  have hden : (p - k) ^ 2 ≤ (p - 1) * (p - k) := by
    nlinarith
  calc
    _ = (k - 1) / ((p - 1) * (p - k)) := by rw [pinnedMovedWeight]; ring
    _ ≤ k / ((p - 1) * (p - k)) := div_le_div_of_nonneg_right
      (by linarith) (mul_nonneg (by linarith) hpk.le)
    _ ≤ k / (p - k) ^ 2 := div_le_div_of_nonneg_left hk0.le (sq_pos_of_pos hpk) hden
    _ = _ := by field_simp [hk0.ne']

variable {α : Type*} [Fintype α]

theorem pinnedMovedPrimeMass_le {k : ℕ} (hk : 2 ≤ k) {p : α → ℕ}
    (hinj : Function.Injective p) (hrough : ∀ q, 2 * k ^ 2 < p q) :
    (∑ q, ((k : ℝ) - 1) * pinnedMovedWeight k (p q)) ≤ 4 / (k : ℝ) := by
  calc
    _ ≤ ∑ q, ((k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) / k :=
      Finset.sum_le_sum fun q _hq => pinnedMovedWeight_le
        (by exact_mod_cast hk) (by exact_mod_cast hrough q)
    _ = (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) / k := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (movedPrimeMass_le_four hk hinj hrough)
      (Nat.cast_nonneg k)

theorem pinnedMovedPrimeLogMass_le {k : ℕ} (hk : 2 ≤ k) {p : α → ℕ}
    (hinj : Function.Injective p) (hrough : ∀ q, 2 * k ^ 2 < p q) :
    (∑ q, ((k : ℝ) - 1) * pinnedMovedWeight k (p q) * Real.log (p q)) ≤ 16 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  calc
    _ ≤ ∑ q, ((k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) / k := by
      apply Finset.sum_le_sum
      intro q _hq
      convert mul_le_mul_of_nonneg_right (pinnedMovedWeight_le (k := (k : ℝ)) (p := (p q : ℝ))
        (by exact_mod_cast hk) (by exact_mod_cast hrough q))
          (Real.log_natCast_nonneg (p q)) using 1
      ring
    _ = (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) / k :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (16 * k) / k := div_le_div_of_nonneg_right
      (movedPrimeLogMass_le hk hinj hrough) hk0.le
    _ = 16 := mul_div_cancel_right₀ _ hk0.ne'

theorem pinnedMovedAssignment_masses_le [DecidableEq α] {m : ℕ} (hm : 1 ≤ m)
    {p : α → ℕ} (hinj : Function.Injective p) (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q) :
    (∑ r : α → Option (Fin m), assignmentScalarWeight
      (fun q => pinnedMovedWeight (m + 1) (p q)) r) ≤ Real.exp 2 ∧
    (∑ r : α → Option (Fin m), assignmentScalarWeight
      (fun q => pinnedMovedWeight (m + 1) (p q)) r *
        Real.log (assignmentPrimeProduct p r)) ≤ 16 * Real.exp 2 := by
  let b := fun q => pinnedMovedWeight ((m : ℝ) + 1) (p q)
  have hk : 2 ≤ m + 1 := by omega
  have hp0 : ∀ q, 0 < p q := fun q => lt_of_le_of_lt (Nat.zero_le _) (hrough q)
  have hb : ∀ q, 0 ≤ b q := fun q => pinnedMovedWeight_nonneg
    (by exact_mod_cast hk) (by exact_mod_cast hrough q)
  have hmass : (∑ q, (m : ℝ) * b q) ≤ 4 / ((m : ℝ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, b] using
      pinnedMovedPrimeMass_le hk hinj hrough
  have hmass2 : (∑ q, (m : ℝ) * b q) ≤ 2 := hmass.trans (by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < m + 1)).mpr
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith)
  have hlog : (∑ q, (m : ℝ) * b q * Real.log (p q)) ≤ 16 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, b] using
      pinnedMovedPrimeLogMass_le hk hinj hrough
  constructor
  · rw [sum_assignmentScalarWeight]
    simp only [Fintype.card_fin]
    exact (Real.prod_one_add_le_exp_sum _ (fun q => mul_nonneg (Nat.cast_nonneg m) (hb q))).trans
      (Real.exp_le_exp.mpr hmass2)
  · calc
      _ ≤ Real.exp (∑ q, (m : ℝ) * b q) *
          ∑ q, (m : ℝ) * b q * Real.log (p q) := by
        simpa only [Fintype.card_fin] using
          sum_assignmentScalarWeight_logProduct_le (β := Fin m) hp0 hb
      _ ≤ Real.exp 2 * 16 := mul_le_mul (Real.exp_le_exp.mpr hmass2) hlog
        (Finset.sum_nonneg fun q _hq => mul_nonneg
          (mul_nonneg (Nat.cast_nonneg m) (hb q)) (Real.log_natCast_nonneg _))
        (Real.exp_nonneg _)
      _ = _ := mul_comm _ _

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedMovedPrimeLogMass_le
#print axioms Erdos4b.FGKMT.pinnedMovedAssignment_masses_le
