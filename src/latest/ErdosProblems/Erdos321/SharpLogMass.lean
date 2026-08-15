import ErdosProblems.Erdos321.LogMass

namespace Erdos321

private theorem log_succ_difference_bounds {t : ℕ} (ht : 3 ≤ t) :
    1 / ((t : ℝ) + 1) ≤ Real.log (t + 1) - Real.log t ∧
      Real.log (t + 1) - Real.log t ≤ 1 / (t : ℝ) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htp1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have harg : 0 < 1 + 1 / (t : ℝ) := by positivity
  have hdiff : Real.log (t + 1) - Real.log t =
      Real.log (1 + 1 / (t : ℝ)) := by
    rw [← Real.log_div (ne_of_gt htp1) (ne_of_gt htpos)]
    congr 1
    field_simp
  rw [hdiff]
  constructor
  · have hlow := Real.le_log_one_add_of_nonneg
      (show 0 ≤ 1 / (t : ℝ) by positivity)
    have hrat : 1 / ((t : ℝ) + 1) ≤
        2 * (1 / (t : ℝ)) / (1 / (t : ℝ) + 2) := by
      field_simp
      nlinarith
    exact hrat.trans hlow
  · have hu := Real.log_le_sub_one_of_pos harg
    convert hu using 1 <;> ring

/-- A logarithmic operator weight differs from its telescoping `log log`
increment by at most `1/(t(t+1))`. -/
theorem weight_sub_logLogIncrement_abs_bound {t : ℕ} (ht : 3 ≤ t) :
    |1 / (((t : ℝ) + 1) * Real.log t) - logLogIncrement t| ≤
      1 / ((t : ℝ) * (t + 1)) := by
  let l := Real.log (t : ℝ)
  let lp := Real.log ((t : ℝ) + 1)
  let d := lp - l
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htone : (1 : ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have hlpos : 0 < l := Real.log_pos htone
  have htp1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hlppos : 0 < lp := Real.log_pos (by linarith)
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    have h := Real.strictMonoOn_log
      (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) < 3)
      Real.exp_one_lt_three
    simpa using h
  have hlone : 1 ≤ l := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) htpos (by exact_mod_cast ht)
    dsimp [l]
    linarith
  have hlpone : 1 ≤ lp := by
    have hllp : l ≤ lp := Real.strictMonoOn_log.monotoneOn htpos htp1 (by linarith)
    exact hlone.trans hllp
  have hdBounds := log_succ_difference_bounds ht
  change 1 / ((t : ℝ) + 1) ≤ d ∧ d ≤ 1 / (t : ℝ) at hdBounds
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hdBounds.1
  have hlpEq : lp = l + d := by dsimp [d]; ring
  have hratio : lp / l = 1 + d / l := by
    rw [hlpEq]
    field_simp
  have hdelta : logLogIncrement t = Real.log (lp / l) := by
    dsimp [logLogIncrement, lp, l]
    rw [Real.log_div (ne_of_gt hlppos) (ne_of_gt hlpos)]
  have hdeltaUpper : logLogIncrement t ≤ d / l := by
    rw [hdelta, hratio]
    have harg : 0 < 1 + d / l := by positivity
    have h := Real.log_le_sub_one_of_pos harg
    nlinarith
  have hdeltaLower : d / lp ≤ logLogIncrement t := by
    rw [hdelta, hratio]
    have hbase := Real.le_log_one_add_of_nonneg
      (show 0 ≤ d / l by positivity)
    have hcomp : d / lp ≤ 2 * (d / l) / (d / l + 2) := by
      rw [hlpEq]
      field_simp
      nlinarith
    exact hcomp.trans hbase
  have htd : (t : ℝ) * d ≤ 1 := by
    calc
      (t : ℝ) * d ≤ t * (1 / (t : ℝ)) :=
        mul_le_mul_of_nonneg_left hdBounds.2 htpos.le
      _ = 1 := by field_simp
  have hllp : 1 ≤ l * lp := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlone) (sub_nonneg.mpr hlpone)]
  have hupper : logLogIncrement t - 1 / (((t : ℝ) + 1) * l) ≤
      1 / ((t : ℝ) * (t + 1)) := by
    calc
      logLogIncrement t - 1 / (((t : ℝ) + 1) * l)
          ≤ d / l - 1 / (((t : ℝ) + 1) * l) := by linarith
      _ ≤ (1 / (t : ℝ)) / l - 1 / (((t : ℝ) + 1) * l) := by
        exact sub_le_sub_right
          (div_le_div_of_nonneg_right hdBounds.2 hlpos.le) _
      _ = 1 / ((t : ℝ) * l) - 1 / (((t : ℝ) + 1) * l) := by ring
      _ ≤ 1 / ((t : ℝ) * (t + 1)) := by
        field_simp
        nlinarith
  have hlower : 1 / (((t : ℝ) + 1) * l) - logLogIncrement t ≤
      1 / ((t : ℝ) * (t + 1)) := by
    calc
      1 / (((t : ℝ) + 1) * l) - logLogIncrement t
          ≤ 1 / (((t : ℝ) + 1) * l) - d / lp := by linarith
      _ ≤ 1 / (((t : ℝ) + 1) * l) -
          (1 / ((t : ℝ) + 1)) / lp := by
        have := div_le_div_of_nonneg_right hdBounds.1 hlppos.le
        linarith
      _ ≤ 1 / ((t : ℝ) * (t + 1)) := by
        field_simp
        nlinarith [htd, hllp]
  rw [abs_le]
  constructor <;> linarith

/-- The total logarithmic mass differs from the exact telescoping `log log`
difference by at most `1/A`, uniformly in the upper endpoint. -/
theorem truncatedLogMass_sharp
    {A T : ℕ} (hA : 3 ≤ A) (hAT : A ≤ T + 1) :
    |truncatedLogOperator A (fun _ => 1) T -
      (Real.log (Real.log (T + 1)) - Real.log (Real.log A))| ≤ 1 / (A : ℝ) := by
  have hset : Finset.Icc A T = Finset.Ico A (T + 1) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have htel : (∑ t ∈ Finset.Icc A T, logLogIncrement t) =
      Real.log (Real.log (T + 1)) - Real.log (Real.log A) := by
    rw [hset]
    simpa [logLogIncrement, Nat.cast_add, Nat.cast_one] using
      Finset.sum_Ico_sub (fun t => Real.log (Real.log t)) hAT
  have herr : |∑ t ∈ Finset.Icc A T,
      (1 / (((t : ℝ) + 1) * Real.log t) - logLogIncrement t)| ≤
      ∑ t ∈ Finset.Icc A T, 1 / ((t : ℝ) * (t + 1)) := by
    calc
      |∑ t ∈ Finset.Icc A T,
          (1 / (((t : ℝ) + 1) * Real.log t) - logLogIncrement t)|
          ≤ ∑ t ∈ Finset.Icc A T,
              |1 / (((t : ℝ) + 1) * Real.log t) - logLogIncrement t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.Icc A T, 1 / ((t : ℝ) * (t + 1)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact weight_sub_logLogIncrement_abs_bound
          (hA.trans (Finset.mem_Icc.mp ht).1)
  have hrat : (∑ t ∈ Finset.Icc A T, 1 / ((t : ℝ) * (t + 1))) ≤
      1 / (A : ℝ) := by
    rw [hset]
    have heq : (∑ t ∈ Finset.Ico A (T + 1), 1 / ((t : ℝ) * (t + 1))) =
        1 / (A : ℝ) - 1 / ((T + 1 : ℕ) : ℝ) := by
      have hterm : ∀ t ∈ Finset.Ico A (T + 1),
          1 / ((t : ℝ) * (t + 1)) = 1 / (t : ℝ) - 1 / ((t + 1 : ℕ) : ℝ) := by
        intro t ht
        have htpos : 0 < t := lt_of_lt_of_le (by omega : 0 < A)
          (Finset.mem_Ico.mp ht).1
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
      have hs := Finset.sum_Ico_sub (fun t : ℕ => 1 / (t : ℝ)) hAT
      rw [Finset.sum_sub_distrib] at hs
      norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
      linarith
    rw [heq]
    have hnonneg : 0 ≤ 1 / ((T + 1 : ℕ) : ℝ) := by positivity
    linarith
  dsimp [truncatedLogOperator]
  rw [← htel]
  have hsumsub :
      (∑ t ∈ Finset.Icc A T, 1 / (((t : ℝ) + 1) * Real.log t)) -
          ∑ t ∈ Finset.Icc A T, logLogIncrement t =
        ∑ t ∈ Finset.Icc A T,
          (1 / (((t : ℝ) + 1) * Real.log t) - logLogIncrement t) := by
    rw [Finset.sum_sub_distrib]
  rw [hsumsub]
  exact herr.trans hrat

end Erdos321
