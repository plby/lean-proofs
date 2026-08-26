import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The exact disjoint-set correction in component second moments

At criticality the correction is at most one.  This is a finite inequality,
not an asymptotic independence assertion.
-/

open scoped BigOperators

namespace Erdos745

/-- Probability that a uniformly chosen `l`-set avoids a fixed `k`-set,
written as a product of successive sampling factors. -/
noncomputable def disjointSetRatio (n k l : ℕ) : ℝ :=
  ∏ j ∈ Finset.range l, ((n - k - j : ℕ) : ℝ) / (n - j : ℕ)

theorem disjointSetRatio_eq_choose_ratio (n k l : ℕ) :
    disjointSetRatio n k l = ((n - k).choose l : ℝ) / (n.choose l : ℝ) := by
  rw [disjointSetRatio, Finset.prod_div_distrib]
  simp only [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by positivity : (l.factorial : ℝ) ≠ 0)

theorem disjointSetRatio_nonneg (n k l : ℕ) :
    0 ≤ disjointSetRatio n k l := by
  unfold disjointSetRatio
  positivity

theorem disjointSetRatio_le_power {n k l : ℕ}
    (hn : 0 < n) (hkl : k + l ≤ n) :
    disjointSetRatio n k l ≤ (1 - (k : ℝ) / n) ^ l := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : k ≤ n := by omega
  have hbase : 0 ≤ 1 - (k : ℝ) / n := by
    rw [sub_nonneg, div_le_one hnR]
    exact_mod_cast hk
  calc
    disjointSetRatio n k l ≤
        ∏ _j ∈ Finset.range l, (1 - (k : ℝ) / n) := by
      apply Finset.prod_le_prod
      · intro j _
        positivity
      · intro j hj
        have hjl : j < l := Finset.mem_range.mp hj
        have hjnk : j ≤ n - k := by omega
        have hjn : j ≤ n := by omega
        have hden : (0 : ℝ) < (n : ℝ) - j := by
          have hjnR : (j : ℝ) < n := by exact_mod_cast (show j < n by omega)
          linarith
        rw [Nat.cast_sub hjnk, Nat.cast_sub hk, Nat.cast_sub hjn]
        have hdiv : (k : ℝ) / n ≤ (k : ℝ) / ((n : ℝ) - j) := by
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg k) hden
          linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
        calc
          ((n : ℝ) - k - j) / ((n : ℝ) - j) =
              1 - (k : ℝ) / ((n : ℝ) - j) := by field_simp; ring
          _ ≤ 1 - (k : ℝ) / n := sub_le_sub_left hdiv 1
    _ = (1 - (k : ℝ) / n) ^ l := by simp

theorem one_sub_div_le_critical_power {n : ℕ} (hn : 0 < n) (k : ℕ) :
    1 - (k : ℝ) / n ≤ (1 - 1 / (n : ℝ)) ^ k := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiv : (1 : ℝ) / n ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hnR
  have h := one_add_mul_le_pow (a := -(1 / (n : ℝ))) (by linarith) k
  simpa [sub_eq_add_neg, div_eq_mul_inv] using h

/-- The loss from choosing disjoint vertex sets cancels at least all of the
positive dependence from the common absent cut edges at `p = 1/n`. -/
theorem disjointSetRatio_le_critical_power {n k l : ℕ}
    (hn : 0 < n) (hkl : k + l ≤ n) :
    disjointSetRatio n k l ≤ (1 - 1 / (n : ℝ)) ^ (k * l) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (k : ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
  have hbase : 0 ≤ 1 - (k : ℝ) / n := by
    rw [sub_nonneg, div_le_one hnR]
    exact hk
  calc
    disjointSetRatio n k l ≤ (1 - (k : ℝ) / n) ^ l :=
      disjointSetRatio_le_power hn hkl
    _ ≤ ((1 - 1 / (n : ℝ)) ^ k) ^ l :=
      pow_le_pow_left₀ hbase (one_sub_div_le_critical_power hn k) l
    _ = _ := (pow_mul _ _ _).symm

/-- The exact mixed factorial-moment multiplier for tree components at
criticality. -/
noncomputable def criticalPairRatio (n k l : ℕ) : ℝ :=
  disjointSetRatio n k l / (1 - 1 / (n : ℝ)) ^ (k * l)

theorem criticalPairRatio_le_one {n k l : ℕ}
    (hn : 2 ≤ n) (hkl : k + l ≤ n) :
    criticalPairRatio n k l ≤ 1 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact hnR
  rw [criticalPairRatio, div_le_one (pow_pos hbase _)]
  exact disjointSetRatio_le_critical_power (by omega) hkl

/-- The critical correction in a form that also covers impossible disjoint sizes. -/
theorem critical_choose_pair_bound {n k l : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    ((n - k).choose l : ℝ) ≤ (n.choose l : ℝ) * (1 - 1 / (n : ℝ)) ^ (k * l) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hnR.le
  by_cases hkl : k + l ≤ n
  · have hl : l ≤ n := by omega
    have hchoose : (0 : ℝ) < n.choose l := by exact_mod_cast Nat.choose_pos hl
    have h := disjointSetRatio_le_critical_power (by omega : 0 < n) hkl
    rw [disjointSetRatio_eq_choose_ratio, div_le_iff₀ hchoose] at h
    simpa only [mul_comm] using h
  · have hlt : n - k < l := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)

end Erdos745
