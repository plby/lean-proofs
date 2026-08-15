import ErdosProblems.Erdos321.IterationCoordinates

namespace Erdos321

/-- Lower endpoint whose `log log` coordinate is a prescribed fraction of the
upper endpoint coordinate. -/
noncomputable def fractionalLogBlockStart (b : ℝ) (T : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp
    (b * Real.log (Real.log (T + 1))))⌉₊

/-- Uniform geometry of fractional logarithmic blocks. -/
theorem fractionalLogBlockStart_properties
    {b : ℝ} {T : ℕ} (hb0 : 0 < b) (hbhalf : b ≤ 1 / 2)
    (hT : 3 ≤ T) (hU : 16 ≤ Real.log (Real.log (T + 1))) :
    3 ≤ fractionalLogBlockStart b T ∧
      fractionalLogBlockStart b T ≤ T ∧
      b * Real.log (Real.log (T + 1)) ≤
        Real.log (Real.log (fractionalLogBlockStart b T)) ∧
      Real.log (Real.log (fractionalLogBlockStart b T)) ≤
        b * Real.log (Real.log (T + 1)) + 1 := by
  let U := Real.log (Real.log ((T : ℝ) + 1))
  let y := Real.exp (b * U)
  let X := Real.exp y
  let L := fractionalLogBlockStart b T
  have hTp1 : (1 : ℝ) < T + 1 := by exact_mod_cast (show 1 < T + 1 by omega)
  have hlogTp1 : 0 < Real.log ((T : ℝ) + 1) := Real.log_pos hTp1
  have hUexp : Real.exp U = Real.log ((T : ℝ) + 1) := by
    dsimp [U]
    exact Real.exp_log hlogTp1
  have hUpos : 0 < U := by
    change 16 ≤ U at hU
    linarith
  have hbUpos : 0 < b * U := mul_pos hb0 hUpos
  have hyone : 1 < y := by
    dsimp [y]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hbUpos
  have hypos : 0 < y := lt_trans (by norm_num : (0 : ℝ) < 1) hyone
  have hXpos : 0 < X := Real.exp_pos _
  have hXtwo : (2 : ℝ) < X := by
    dsimp [X]
    exact Real.exp_one_gt_two.trans_le (Real.exp_monotone hyone.le)
  have hspos : 0 < Real.exp (U / 2) := Real.exp_pos _
  have hs2 : 2 ≤ Real.exp (U / 2) := by
    have hhalf : (2 : ℝ) ≤ U / 2 := by linarith
    have hmono := Real.exp_monotone hhalf
    have he2 : (2 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two]
    linarith
  have hyLe : y ≤ Real.exp (U / 2) := by
    apply Real.exp_monotone
    nlinarith
  have hsSq : (Real.exp (U / 2)) ^ 2 = Real.exp U := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hyExp : y ≤ Real.exp U - Real.log 2 := by
    nlinarith [sq_nonneg (Real.exp (U / 2) - 2)]
  have hExpExpU : Real.exp (Real.exp U) = (T : ℝ) + 1 := by
    rw [hUexp, Real.exp_log (by positivity : (0 : ℝ) < (T : ℝ) + 1)]
  have hXhalf : X ≤ ((T : ℝ) + 1) / 2 := by
    have hm := Real.exp_monotone hyExp
    have hcalc : Real.exp (Real.exp U - Real.log 2) = ((T : ℝ) + 1) / 2 := by
      rw [Real.exp_sub, hExpExpU,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    dsimp [X]
    exact hm.trans_eq hcalc
  have hLceil : X ≤ (L : ℝ) := by
    dsimp [L, fractionalLogBlockStart, X, y, U]
    exact Nat.le_ceil _
  have hLlt : (L : ℝ) < X + 1 := by
    dsimp [L, fractionalLogBlockStart, X, y, U]
    exact Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos _))
  have hLTreal : (L : ℝ) ≤ T := by
    have hTr : (3 : ℝ) ≤ T := by exact_mod_cast hT
    have hhalf : ((T : ℝ) + 1) / 2 + 1 ≤ T := by linarith
    exact le_of_lt (hLlt.trans_le (by linarith [hXhalf, hhalf]))
  have hLT : L ≤ T := by exact_mod_cast hLTreal
  have hL3 : 3 ≤ L := by
    have : 2 < L := by exact_mod_cast (hXtwo.trans_le hLceil)
    omega
  have hlogX : Real.log X = y := by dsimp [X]; rw [Real.log_exp]
  have hlogy : Real.log y = b * U := by dsimp [y]; rw [Real.log_exp]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlogLower : y ≤ Real.log (L : ℝ) := by
    have hm := Real.strictMonoOn_log.monotoneOn hXpos hLpos hLceil
    simpa [hlogX] using hm
  have hlogLogLower : b * U ≤ Real.log (Real.log (L : ℝ)) := by
    have hm := Real.strictMonoOn_log.monotoneOn hypos
      (lt_of_lt_of_le hypos hlogLower) hlogLower
    simpa [hlogy] using hm
  have hXone : 1 ≤ X := by
    dsimp [X]
    simpa using Real.exp_monotone (le_of_lt hypos)
  have hLtwoX : (L : ℝ) ≤ 2 * X := by nlinarith
  have hlogLUpper : Real.log (L : ℝ) ≤ 2 * y := by
    have hm := Real.strictMonoOn_log.monotoneOn hLpos
      (show (0 : ℝ) < 2 * X by positivity) hLtwoX
    have heq : Real.log (2 * X) = Real.log 2 + y := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hXpos), hlogX]
    rw [heq] at hm
    nlinarith
  have hlogLogUpper : Real.log (Real.log (L : ℝ)) ≤ b * U + 1 := by
    have hm := Real.strictMonoOn_log.monotoneOn
      (lt_of_lt_of_le hypos hlogLower)
      (show (0 : ℝ) < 2 * y by positivity) hlogLUpper
    have heq : Real.log (2 * y) = Real.log 2 + b * U := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hypos), hlogy]
    rw [heq] at hm
    linarith
  change 3 ≤ L ∧ L ≤ T ∧ b * U ≤ Real.log (Real.log L) ∧
    Real.log (Real.log L) ≤ b * U + 1
  exact ⟨hL3, hLT, hlogLogLower, hlogLogUpper⟩

/-- Sharp mass of a fractional block, including ceiling and discrete errors. -/
theorem fractionalLogBlock_mass_lower
    {b : ℝ} {T : ℕ} (hb0 : 0 < b) (hbhalf : b ≤ 1 / 2)
    (hT : 3 ≤ T) (hU : 16 ≤ Real.log (Real.log (T + 1))) :
    (1 - b) * Real.log (Real.log (T + 1)) - 2 ≤
      truncatedLogOperator (fractionalLogBlockStart b T) (fun _ => 1) T := by
  have hp := fractionalLogBlockStart_properties hb0 hbhalf hT hU
  let L := fractionalLogBlockStart b T
  have hm := truncatedLogMass_sharp hp.1 (show L ≤ T + 1 by omega)
  have habs := (abs_le.mp hm).1
  have hrecip : 1 / (L : ℝ) ≤ 1 := by
    have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    exact (div_le_one (by positivity)).2 hLone
  dsimp [L] at hm habs hrecip ⊢
  nlinarith [hp.2.2.2]

end Erdos321
