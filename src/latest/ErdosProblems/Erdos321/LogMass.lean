import ErdosProblems.Erdos321.NeumannModel

namespace Erdos321

noncomputable def logLogIncrement (t : ℕ) : ℝ :=
  Real.log (Real.log (t + 1)) - Real.log (Real.log t)

private theorem log_succ_sub_log_bounds {t : ℕ} (ht : 3 ≤ t) :
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
  constructor
  · rw [hdiff]
    have hlow := Real.le_log_one_add_of_nonneg
      (show 0 ≤ 1 / (t : ℝ) by positivity)
    have hrat : 1 / ((t : ℝ) + 1) ≤
        2 * (1 / (t : ℝ)) / (1 / (t : ℝ) + 2) := by
      field_simp
      nlinarith
    exact hrat.trans hlow
  · rw [hdiff]
    have hu := Real.log_le_sub_one_of_pos harg
    convert hu using 1
    all_goals ring

/-- One discrete logarithmic weight is within a factor two of the corresponding
increment of `log log`. -/
theorem weight_comparable_logLogIncrement {t : ℕ} (ht : 3 ≤ t) :
    logLogIncrement t / 2 ≤ 1 / (((t : ℝ) + 1) * Real.log t) ∧
      1 / (((t : ℝ) + 1) * Real.log t) ≤ 2 * logLogIncrement t := by
  let l := Real.log (t : ℝ)
  let lp := Real.log ((t : ℝ) + 1)
  let d := lp - l
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htone : (1 : ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have hlpos : 0 < l := Real.log_pos htone
  have htp1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hlppos : 0 < lp := Real.log_pos (by linarith)
  have hdBounds := log_succ_sub_log_bounds ht
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
  have hlpLe : lp ≤ 2 * l := by
    have hnat : t + 1 ≤ t * t := by nlinarith
    have hcast : (t : ℝ) + 1 ≤ (t : ℝ) * t := by exact_mod_cast hnat
    have hmono := Real.strictMonoOn_log.monotoneOn htp1
      (mul_pos htpos htpos) hcast
    rw [Real.log_mul (ne_of_gt htpos) (ne_of_gt htpos)] at hmono
    simpa [lp, l, two_mul] using hmono
  have hweight0 : 0 < 1 / (((t : ℝ) + 1) * l) := by positivity
  constructor
  · change logLogIncrement t / 2 ≤ 1 / (((t : ℝ) + 1) * l)
    have haux : logLogIncrement t ≤ 2 / (((t : ℝ) + 1) * l) := by
      calc
        logLogIncrement t ≤ d / l := hdeltaUpper
        _ ≤ (1 / (t : ℝ)) / l :=
          div_le_div_of_nonneg_right hdBounds.2 hlpos.le
        _ ≤ 2 / (((t : ℝ) + 1) * l) := by
          field_simp
          nlinarith
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      logLogIncrement t ≤ 2 / (((t : ℝ) + 1) * l) := haux
      _ = 1 / (((t : ℝ) + 1) * l) * 2 := by ring
  · change 1 / (((t : ℝ) + 1) * l) ≤ 2 * logLogIncrement t
    have haux : 1 / (((t : ℝ) + 1) * l) ≤ 2 * (d / lp) := by
      have hdScaled : 1 / ((t : ℝ) + 1) / lp ≤ d / lp :=
        div_le_div_of_nonneg_right hdBounds.1 hlppos.le
      have hlogScaled : 1 / (((t : ℝ) + 1) * l) ≤
          2 * (1 / ((t : ℝ) + 1) / lp) := by
        field_simp
        nlinarith
      linarith
    exact haux.trans (mul_le_mul_of_nonneg_left hdeltaLower (by norm_num))

/-- The total discrete logarithmic mass telescopes, up to a factor two, to a
`log log` difference. -/
theorem truncatedLogMass_bounds
    {A T : ℕ} (hA : 3 ≤ A) (hAT : A ≤ T + 1) :
    (Real.log (Real.log (T + 1)) - Real.log (Real.log A)) / 2 ≤
        truncatedLogOperator A (fun _ => 1) T ∧
      truncatedLogOperator A (fun _ => 1) T ≤
        2 * (Real.log (Real.log (T + 1)) - Real.log (Real.log A)) := by
  have hpoint : ∀ t ∈ Finset.Icc A T,
      logLogIncrement t / 2 ≤ 1 / (((t : ℝ) + 1) * Real.log t) ∧
        1 / (((t : ℝ) + 1) * Real.log t) ≤ 2 * logLogIncrement t := by
    intro t ht
    exact weight_comparable_logLogIncrement (hA.trans (Finset.mem_Icc.mp ht).1)
  have htel : (∑ t ∈ Finset.Icc A T, logLogIncrement t) =
      Real.log (Real.log (T + 1)) - Real.log (Real.log A) := by
    have hset : Finset.Icc A T = Finset.Ico A (T + 1) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset]
    simpa [logLogIncrement, Nat.cast_add, Nat.cast_one] using
      Finset.sum_Ico_sub (fun t => Real.log (Real.log t)) hAT
  dsimp [truncatedLogOperator]
  constructor
  · rw [← htel, Finset.sum_div]
    apply Finset.sum_le_sum
    intro t ht
    exact (hpoint t ht).1
  · rw [← htel, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    exact (hpoint t ht).2

end Erdos321
