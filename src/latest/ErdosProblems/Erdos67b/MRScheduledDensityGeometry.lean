import ErdosProblems.Erdos67b.MRAuxiliaryDensity
import ErdosProblems.Erdos67b.MRLastBlockRemainder

/-! # Rounded scheduled endpoint ratios and injectivity -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrScheduledLogLower_twice_le_upper {p q : ℝ}
    (hq : 1 ≤ q) (hpq : 2 * p ≤ q) {j : ℕ} (hj : 1 ≤ j) :
    2 * mrLogScheduleLower p q j ≤ mrLogScheduleUpper q j := by
  have hh := mrLogScheduleLower_le_upper hq hpq hj
  unfold mrLogScheduleLower at hh ⊢
  nlinarith

theorem mrScheduledPrimeInterval_valid {p q : ℝ} (hp : 2 ≤ p)
    (hq : 1 ≤ q) (hpq : 2 * p ≤ q) {j : ℕ} (hj : 1 ≤ j) :
    3 ≤ (mrScheduledPrimeInterval p q j).1 ∧
      (mrScheduledPrimeInterval p q j).1 ≤ (mrScheduledPrimeInterval p q j).2 := by
  have hlow := hp.trans (mrLogScheduleLower_ge (by linarith) hq hj)
  have hh := mrLogPrimeInterval_endpoint_bounds hlow (mrScheduledLogLower_twice_le_upper hq hpq hj)
  exact ⟨hh.1, hh.2.1⟩

theorem mrScheduledPrimeInterval_strict_separated
    {eta p q : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    (mrScheduledPrimeInterval p q i).2 < (mrScheduledPrimeInterval p q j).1 := by
  have hgap := mrLogSchedule_separated_of_lt heta hp hq hpq hlogq hbudget hi hij
  have hreal : ((mrScheduledPrimeInterval p q i).2 : ℝ) <
      (mrScheduledPrimeInterval p q j).1 := by
    calc
      _ ≤ Real.exp (mrLogScheduleUpper q i) := Nat.floor_le (Real.exp_pos _).le
      _ < Real.exp (mrLogScheduleLower p q j) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast hreal

theorem mrScheduledPrimeInterval_injOn
    {eta p q : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : 2 * p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (J : ℕ) : Set.InjOn (mrScheduledPrimeInterval p q) (↑(Finset.Icc 1 J) : Set ℕ) := by
  intro i hi j hj heq
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hj1 := (Finset.mem_Icc.mp hj).1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hh := mrScheduledPrimeInterval_strict_separated heta hp hq (by linarith)
      hlogq hbudget hi1 hij
    rw [heq] at hh
    exact (not_lt_of_ge (mrScheduledPrimeInterval_valid hp hq hpq hj1).2) hh
  · have hh := mrScheduledPrimeInterval_strict_separated heta hp hq (by linarith)
      hlogq hbudget hj1 hji
    rw [heq] at hh
    exact (not_lt_of_ge (mrScheduledPrimeInterval_valid hp hq hpq hj1).2) hh

theorem mrScheduledPrimeInterval_logRatio_le {p q : ℝ} (hp : 2 ≤ p)
    (hq : 1 ≤ q) (hpq : 2 * p ≤ q) {j : ℕ} (hj : 1 ≤ j) :
    Real.log (((mrScheduledPrimeInterval p q j).1 - 1 : ℕ) : ℝ) /
        Real.log ((mrScheduledPrimeInterval p q j).2 : ℝ) ≤
      (2 * p / q) * ((j : ℝ) ^ 2)⁻¹ := by
  have hlow := hp.trans (mrLogScheduleLower_ge (by linarith) hq hj)
  have hh := mrAuxiliaryInterval_logRatio_le hlow (mrScheduledLogLower_twice_le_upper hq hpq hj)
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hqpos : 0 < q := by linarith
  have hw : 0 < mrLogScheduleWeight q j :=
    lt_of_lt_of_le zero_lt_one (mrLogScheduleWeight_one_le hq hj)
  have heq : mrLogScheduleUpper q j = mrLogScheduleWeight q j * (j : ℝ) ^ 2 * q := by
    unfold mrLogScheduleUpper mrLogScheduleWeight
    rw [pow_add, show q ^ j = q ^ (j - 1) * q by rw [← pow_succ, Nat.sub_add_cancel hj]]
    ring
  apply hh.trans_eq
  rw [heq, mrLogScheduleLower]
  field_simp

theorem mrScheduledBlocks_sum_logRatio_le
    {eta p q : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : 2 * p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (J : ℕ) :
    (∑ I ∈ mrScheduledBlocks p q J,
      Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)) ≤ 4 * p / q := by
  have hh := sum_indexedPrimeBlocks_logRatio_le_two_mul
    (mrScheduledPrimeInterval_injOn heta hp hq hpq hlogq hbudget J)
    (by positivity : 0 ≤ 2 * p / q)
    (fun j hj ↦ mrScheduledPrimeInterval_logRatio_le hp hq hpq (Finset.mem_Icc.mp hj).1)
  change (∑ I ∈ mrScheduledBlocks p q J,
    Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)) ≤ 2 * (2 * p / q) at hh
  convert hh using 1
  ring

end

end Erdos67b
