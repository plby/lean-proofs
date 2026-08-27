import Arxiv.Arxiv2411_18291.FiniteColourTrials

/-! # Amplifying a fixed colour success probability over all root embeddings -/

noncomputable section

namespace Arxiv2411_18291

def logarithmicColourTrialCount (n f : ℕ) : ℕ :=
  ⌈9 * ((f : ℝ) + 2) * Real.log n⌉₊

theorem logarithmicColourTrialCount_pos {n : ℕ} (hn : 1 < n) (f : ℕ) :
    0 < logarithmicColourTrialCount n f := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  unfold logarithmicColourTrialCount
  exact Nat.ceil_pos.mpr (by positivity)

theorem logarithmicColourTrialCount_lt {n : ℕ} (hn : 1 ≤ n) (f : ℕ) :
    (logarithmicColourTrialCount n f : ℝ) < 9 * ((f : ℝ) + 2) * Real.log n + 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hnR
  exact Nat.ceil_lt_add_one (by positivity)

theorem logarithmic_colour_trial_union_bound {n : ℕ} (hn : 0 < n) (f : ℕ) :
    (n : ℝ) ^ f * (8 / 9 : ℝ) ^ logarithmicColourTrialCount n f ≤
      (n : ℝ) ^ (-2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (8 / 9 : ℝ) ≤ Real.exp (-(1 / 9 : ℝ)) := by
    have hh := Real.add_one_le_exp (-(1 / 9 : ℝ))
    linarith only [hh]
  have hL : 9 * ((f : ℝ) + 2) * Real.log n ≤ logarithmicColourTrialCount n f :=
    Nat.le_ceil _
  have hp : (8 / 9 : ℝ) ^ logarithmicColourTrialCount n f ≤
      (n : ℝ) ^ (-((f : ℝ) + 2)) := by
    calc
      _ ≤ (Real.exp (-(1 / 9 : ℝ))) ^ logarithmicColourTrialCount n f :=
        pow_le_pow_left₀ (by norm_num) hbase _
      _ = Real.exp (-((logarithmicColourTrialCount n f : ℝ) / 9)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (Real.log n * (-((f : ℝ) + 2))) :=
        Real.exp_le_exp.mpr (by nlinarith only [hL])
      _ = _ := (Real.rpow_def_of_pos hn0 _).symm
  calc
    _ ≤ (n : ℝ) ^ f * (n : ℝ) ^ (-((f : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (n : ℝ) f, ← Real.rpow_add hn0]
      congr 1
      ring

end Arxiv2411_18291
