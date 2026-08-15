import ErdosProblems.Erdos321.FirstModelFactor

namespace Erdos321

noncomputable def fourthIteratedLog (N : ℕ) : ℝ :=
  Real.log (thirdIteratedLog N)

/-- The beginning of the upper half of the interval in the `log log`
coordinate. -/
noncomputable def midLogBlockStart (T : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp (Real.log (Real.log (T + 1)) / 2))⌉₊

/-- For large enough `T`, `midLogBlockStart T` lies below `T` and its
`log log` coordinate lies between one half and three quarters of the terminal
coordinate. -/
theorem midLogBlockStart_properties
    {T : ℕ} (hT : 3 ≤ T)
    (hU : 4 * Real.log 2 ≤ Real.log (Real.log (T + 1)))
    (hy2 : 2 ≤ Real.exp (Real.log (Real.log (T + 1)) / 2)) :
    3 ≤ midLogBlockStart T ∧ midLogBlockStart T ≤ T ∧
      Real.log (Real.log (T + 1)) / 2 ≤
        Real.log (Real.log (midLogBlockStart T)) ∧
      Real.log (Real.log (midLogBlockStart T)) ≤
        3 * Real.log (Real.log (T + 1)) / 4 := by
  let U := Real.log (Real.log ((T : ℝ) + 1))
  let y := Real.exp (U / 2)
  let X := Real.exp y
  let L := midLogBlockStart T
  have hTp1 : (1 : ℝ) < T + 1 := by exact_mod_cast (show 1 < T + 1 by omega)
  have hlogTp1 : 0 < Real.log ((T : ℝ) + 1) := Real.log_pos hTp1
  have hUexp : Real.exp U = Real.log ((T : ℝ) + 1) := by
    dsimp [U]
    exact Real.exp_log hlogTp1
  have hypos : 0 < y := Real.exp_pos _
  have hXpos : 0 < X := Real.exp_pos _
  have hySq : y ^ 2 = Real.exp U := by
    dsimp [y]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hyExp : y ≤ Real.exp U - Real.log 2 := by
    rw [← hySq]
    nlinarith [sq_nonneg (y - 2)]
  have hExpSq : Real.exp (Real.exp U) = (T : ℝ) + 1 := by
    calc
      Real.exp (Real.exp U) = Real.exp (Real.log ((T : ℝ) + 1)) := by rw [hUexp]
      _ = (T : ℝ) + 1 := Real.exp_log (by positivity)
  have hXhalf : X ≤ ((T : ℝ) + 1) / 2 := by
    have hexp := Real.exp_monotone hyExp
    have hcalc : Real.exp (Real.exp U - Real.log 2) = ((T : ℝ) + 1) / 2 := by
      rw [Real.exp_sub, hExpSq, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    dsimp [X]
    exact hexp.trans_eq hcalc
  have hLceil : X ≤ (L : ℝ) := by
    dsimp [L, midLogBlockStart, X, y, U]
    exact Nat.le_ceil _
  have hLlt : (L : ℝ) < X + 1 := by
    dsimp [L, midLogBlockStart, X, y, U]
    exact Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos _))
  have hLTreal : (L : ℝ) ≤ T := by
    have hhalf : ((T : ℝ) + 1) / 2 + 1 ≤ T := by
      have hTr : (3 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    exact le_of_lt (hLlt.trans_le (by linarith [hXhalf, hhalf]))
  have hLT : L ≤ T := by exact_mod_cast hLTreal
  have hL3 : 3 ≤ L := by
    have he2 : (4 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two]
    have hX4 : (4 : ℝ) < X := by
      dsimp [X]
      exact he2.trans_le (Real.exp_monotone hy2)
    have : 3 < L := by exact_mod_cast (show (3 : ℝ) < L by linarith)
    omega
  have hlogX : Real.log X = y := by dsimp [X]; rw [Real.log_exp]
  have hlogy : Real.log y = U / 2 := by dsimp [y]; rw [Real.log_exp]
  have hlogLLower : y ≤ Real.log (L : ℝ) := by
    have hmono := Real.strictMonoOn_log.monotoneOn hXpos
      (show (0 : ℝ) < L by exact_mod_cast (show 0 < L by omega)) hLceil
    simpa [hlogX] using hmono
  have hlogLogLower : U / 2 ≤ Real.log (Real.log (L : ℝ)) := by
    have hmono := Real.strictMonoOn_log.monotoneOn hypos
      (lt_of_lt_of_le hypos hlogLLower) hlogLLower
    simpa [hlogy] using hmono
  have hXone : 1 ≤ X := by
    dsimp [X]
    simpa using Real.exp_monotone (le_of_lt hypos)
  have hLtwoX : (L : ℝ) ≤ 2 * X := by nlinarith
  have hlogLUpper : Real.log (L : ℝ) ≤ 2 * y := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < L by exact_mod_cast (show 0 < L by omega))
      (show (0 : ℝ) < 2 * X by positivity) hLtwoX
    have hlog2X : Real.log (2 * X) = Real.log 2 + y := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hXpos), hlogX]
    rw [hlog2X] at hmono
    nlinarith
  have hlogLogUpper : Real.log (Real.log (L : ℝ)) ≤ 3 * U / 4 := by
    have h2ypos : 0 < 2 * y := by positivity
    have hmono := Real.strictMonoOn_log.monotoneOn
      (lt_of_lt_of_le hypos hlogLLower) h2ypos hlogLUpper
    have hlog2y : Real.log (2 * y) = Real.log 2 + U / 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hypos), hlogy]
    rw [hlog2y] at hmono
    change 4 * Real.log 2 ≤ U at hU
    nlinarith
  change 3 ≤ L ∧ L ≤ T ∧ U / 2 ≤ Real.log (Real.log L) ∧
    Real.log (Real.log L) ≤ 3 * U / 4
  exact ⟨hL3, hLT, hlogLogLower, hlogLogUpper⟩

end Erdos321
