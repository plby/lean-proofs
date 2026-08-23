import ErdosProblems.Erdos1166.Erdos1166KilledGreen
import ErdosProblems.Erdos1166.Erdos1166HLOZGreen

namespace Erdos1166.KilledGreen

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem abs_directionStep_fst_le_one (d : Direction) :
    |(directionStep d).1| ≤ 1 := by
  fin_cases d <;> norm_num [directionStep]

theorem abs_directionStep_snd_le_one (d : Direction) :
    |(directionStep d).2| ≤ 1 := by
  fin_cases d <;> norm_num [directionStep]

theorem abs_simpleRandomWalk_fst_le_time (ω : ℕ → Direction) (n : ℕ) :
    |(simpleRandomWalk ω n).1| ≤ (n : ℤ) := by
  rw [simpleRandomWalk, Prod.fst_sum]
  calc
    |∑ j ∈ Finset.range n, (directionStep (ω j)).1| ≤
        ∑ j ∈ Finset.range n, |(directionStep (ω j)).1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range n, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_directionStep_fst_le_one (ω j)
    _ = (n : ℤ) := by simp

theorem abs_simpleRandomWalk_snd_le_time (ω : ℕ → Direction) (n : ℕ) :
    |(simpleRandomWalk ω n).2| ≤ (n : ℤ) := by
  rw [simpleRandomWalk, Prod.snd_sum]
  calc
    |∑ j ∈ Finset.range n, (directionStep (ω j)).2| ≤
        ∑ j ∈ Finset.range n, |(directionStep (ω j)).2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range n, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_directionStep_snd_le_one (ω j)
    _ = (n : ℤ) := by simp

theorem simpleRandomWalk_mem_squareDisk_of_time_le
    (ω : ℕ → Direction) {n R : ℕ} (hnR : n ≤ R) :
    simpleRandomWalk ω n ∈ squareDisk R := by
  unfold squareDisk
  apply Finset.mem_product.mpr
  constructor <;> rw [Finset.mem_Icc]
  · have h := abs_simpleRandomWalk_fst_le_time ω n
    have hnRz : (n : ℤ) ≤ (R : ℤ) := by exact_mod_cast hnR
    rw [abs_le] at h
    omega
  · have h := abs_simpleRandomWalk_snd_le_time ω n
    have hnRz : (n : ℤ) ≤ (R : ℤ) := by exact_mod_cast hnR
    rw [abs_le] at h
    omega

theorem killedEndpointEvent_zero_zero_eq_returnEvent
    {R n : ℕ} (hnR : n ≤ R) :
    killedEndpointEvent (squareDisk R : Set Site) 0 0 n =
      {ω | simpleRandomWalk ω n = 0} := by
  ext ω
  simp only [killedEndpointEvent, Set.mem_setOf_eq]
  constructor
  · intro h
    simpa [walkFrom] using h.2
  · intro h
    constructor
    · intro r hr
      simpa [walkFrom] using
        simpleRandomWalk_mem_squareDisk_of_time_le ω (hr.trans hnR)
    · simpa [walkFrom] using h

theorem killedWeight_zero_zero_toReal_eq_returnProb
    {R n : ℕ} (hnR : n ≤ R) :
    (killedWeight (squareDisk R : Set Site) 0 0 n).toReal = returnProb n := by
  rw [killedWeight, killedEndpointEvent_zero_zero_eq_returnEvent hnR]
  rfl

/-- Before deterministic time `N ≤ R`, every path is still inside the square,
so the free origin Green sum is a lower bound for the killed diagonal Green
function. -/
theorem freeFiniteGreen_le_diskGreen_zero_toReal
    {N R : ℕ} (hNR : N ≤ R) :
    freeFiniteGreen N ≤ (diskGreen R 0 0).toReal := by
  have hsumTop :
      (∑ n ∈ Finset.range (N + 1),
        killedWeight (squareDisk R : Set Site) 0 0 n) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro n hn
    unfold killedWeight
    exact measure_ne_top incrementLaw _
  calc
    freeFiniteGreen N =
        ∑ n ∈ Finset.range (N + 1),
          (killedWeight (squareDisk R : Set Site) 0 0 n).toReal := by
      apply Finset.sum_congr rfl
      intro n hn
      symm
      apply killedWeight_zero_zero_toReal_eq_returnProb
      have hnN : n ≤ N :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      exact hnN.trans hNR
    _ = (∑ n ∈ Finset.range (N + 1),
          killedWeight (squareDisk R : Set Site) 0 0 n).toReal := by
      symm
      apply ENNReal.toReal_sum
      intro n hn
      unfold killedWeight
      exact measure_ne_top incrementLaw _
    _ ≤ (diskGreen R 0 0).toReal := by
      rw [ENNReal.toReal_le_toReal hsumTop (diskGreen_ne_top R 0 0)]
      unfold diskGreen killedGreen
      exact ENNReal.sum_le_tsum (Finset.range (N + 1))

/-- Explicit logarithmic lower bound for the diagonal killed Green function.
The half-radius in the logarithm comes only from fitting an even return-time
horizon inside the square. -/
theorem quarter_log_half_le_diskGreen_zero_toReal
    {R : ℕ} (hR : 2 ≤ R) :
    (1 / 4 : ℝ) * Real.log ((R / 2 + 1 : ℕ) : ℝ) ≤
      (diskGreen R 0 0).toReal := by
  let k := R / 2 - 1
  have hhalf : 1 ≤ R / 2 := by omega
  have hk : k + 1 = R / 2 := by
    dsimp only [k]
    omega
  have htime : 2 * (k + 1) ≤ R := by
    rw [hk]
    exact Nat.mul_div_le R 2
  have hlog : Real.log ((R / 2 + 1 : ℕ) : ℝ) ≤
      (harmonic (k + 1) : ℝ) := by
    have h := log_add_one_le_harmonic (k + 1)
    have harg : k + 1 + 1 = R / 2 + 1 :=
      congrArg (fun n : ℕ ↦ n + 1) hk
    rw [harg] at h
    exact h
  calc
    (1 / 4 : ℝ) * Real.log ((R / 2 + 1 : ℕ) : ℝ) ≤
        (1 / 4 : ℝ) * (harmonic (k + 1) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ ≤ freeFiniteGreen (2 * (k + 1)) :=
      (freeFiniteGreen_even_two_sided k).1
    _ ≤ (diskGreen R 0 0).toReal :=
      freeFiniteGreen_le_diskGreen_zero_toReal htime

theorem half_log_le_log_half_add_one {R : ℕ} (hR : 2 ≤ R) :
    (1 / 2 : ℝ) * Real.log (R : ℝ) ≤
      Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
  have hsquare : R ≤ (R / 2 + 1) ^ 2 := by
    have hdiv : R ≤ 2 * (R / 2) + 1 := by omega
    nlinarith [sq_nonneg (R / 2 : ℝ)]
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  have hsquareReal : (R : ℝ) ≤ (((R / 2 + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hsquare
  have hlog : Real.log (R : ℝ) ≤
      Real.log ((((R / 2 + 1) ^ 2 : ℕ) : ℝ)) :=
    Real.log_le_log hRpos hsquareReal
  rw [Nat.cast_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  linarith

theorem eighth_log_le_diskGreen_zero_toReal
    {R : ℕ} (hR : 2 ≤ R) :
    (1 / 8 : ℝ) * Real.log (R : ℝ) ≤
      (diskGreen R 0 0).toReal := by
  calc
    (1 / 8 : ℝ) * Real.log (R : ℝ) =
        (1 / 4 : ℝ) * ((1 / 2 : ℝ) * Real.log (R : ℝ)) := by ring
    _ ≤ (1 / 4 : ℝ) * Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left (half_log_le_log_half_add_one hR)
        (by norm_num)
    _ ≤ (diskGreen R 0 0).toReal :=
      quarter_log_half_le_diskGreen_zero_toReal hR

/-- Source-form escape estimate: the walk exits the square before its first
positive return to the origin with probability at most `4 / log(R/2+1)`. -/
theorem exitBeforeReturn_zero_real_le_four_div_log_half
    {R : ℕ} (hR : 2 ≤ R) :
    incrementLaw.real
        (exitBeforeReturnEvent (squareDisk R : Set Site) 0) ≤
      4 / Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
  have hzero : (0 : Site) ∈ squareDisk R := by
    simp [squareDisk]
  rw [measureReal_def,
    measure_exitBeforeReturnEvent_eq_inv_green hzero, ENNReal.toReal_inv]
  have hG := quarter_log_half_le_diskGreen_zero_toReal hR
  have hlog : 0 < Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R / 2 + 1 by omega)
  calc
    (diskGreen R 0 0).toReal⁻¹ ≤
        ((1 / 4 : ℝ) * Real.log ((R / 2 + 1 : ℕ) : ℝ))⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (mul_pos (by norm_num) hlog) hG
    _ = 4 / Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
      field_simp

theorem measure_exitBeforeReturn_zero_le_ofReal_four_div_log_half
    {R : ℕ} (hR : 2 ≤ R) :
    incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) 0) ≤
      ENNReal.ofReal (4 / Real.log ((R / 2 + 1 : ℕ) : ℝ)) := by
  have hlog : 0 ≤ Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
    exact (Real.log_pos (by exact_mod_cast (show 1 < R / 2 + 1 by omega))).le
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top incrementLaw _)
    (div_nonneg (by norm_num) hlog)]
  exact exitBeforeReturn_zero_real_le_four_div_log_half hR

/-- Literal `C / log R` form, with the safe explicit constant `C = 8`. -/
theorem exitBeforeReturn_zero_real_le_eight_div_log
    {R : ℕ} (hR : 2 ≤ R) :
    incrementLaw.real
        (exitBeforeReturnEvent (squareDisk R : Set Site) 0) ≤
      8 / Real.log (R : ℝ) := by
  have hzero : (0 : Site) ∈ squareDisk R := by
    simp [squareDisk]
  rw [measureReal_def,
    measure_exitBeforeReturnEvent_eq_inv_green hzero, ENNReal.toReal_inv]
  have hG := eighth_log_le_diskGreen_zero_toReal hR
  have hlog : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R by omega)
  calc
    (diskGreen R 0 0).toReal⁻¹ ≤
        ((1 / 8 : ℝ) * Real.log (R : ℝ))⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (mul_pos (by norm_num) hlog) hG
    _ = 8 / Real.log (R : ℝ) := by
      field_simp

theorem measure_exitBeforeReturn_zero_le_ofReal_eight_div_log
    {R : ℕ} (hR : 2 ≤ R) :
    incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) 0) ≤
      ENNReal.ofReal (8 / Real.log (R : ℝ)) := by
  have hlog : 0 ≤ Real.log (R : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < R by omega))).le
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top incrementLaw _)
    (div_nonneg (by norm_num) hlog)]
  exact exitBeforeReturn_zero_real_le_eight_div_log hR

/-- Reduction of the off-diagonal hitting estimate to an upper bound on the
off-diagonal killed Green numerator. -/
theorem hitZeroBeforeExit_real_le_four_mul_green_div_log_half
    {R : ℕ} (hR : 2 ≤ R) (y : Site) :
    incrementLaw.real
        (hitBeforeExitEvent (squareDisk R : Set Site) y 0) ≤
      4 * (diskGreen R y 0).toReal /
        Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
  have hzero : (0 : Site) ∈ squareDisk R := by
    simp [squareDisk]
  rw [measureReal_def, measure_hitBeforeExitEvent_eq_green_div hzero,
    ENNReal.toReal_div]
  have hG := quarter_log_half_le_diskGreen_zero_toReal hR
  have hlog : 0 < Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R / 2 + 1 by omega)
  calc
    (diskGreen R y 0).toReal / (diskGreen R 0 0).toReal ≤
        (diskGreen R y 0).toReal /
          ((1 / 4 : ℝ) * Real.log ((R / 2 + 1 : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg
        (mul_pos (by norm_num) hlog) hG
    _ = 4 * (diskGreen R y 0).toReal /
        Real.log ((R / 2 + 1 : ℕ) : ℝ) := by
      field_simp

/-- Literal-log reduction for the second HLOZ bound.  What remains is the
spatial numerator estimate `G_D(y,0) = O(log(R / |y|))`. -/
theorem hitZeroBeforeExit_real_le_eight_mul_green_div_log
    {R : ℕ} (hR : 2 ≤ R) (y : Site) :
    incrementLaw.real
        (hitBeforeExitEvent (squareDisk R : Set Site) y 0) ≤
      8 * (diskGreen R y 0).toReal / Real.log (R : ℝ) := by
  have hzero : (0 : Site) ∈ squareDisk R := by
    simp [squareDisk]
  rw [measureReal_def, measure_hitBeforeExitEvent_eq_green_div hzero,
    ENNReal.toReal_div]
  have hG := eighth_log_le_diskGreen_zero_toReal hR
  have hlog : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R by omega)
  calc
    (diskGreen R y 0).toReal / (diskGreen R 0 0).toReal ≤
        (diskGreen R y 0).toReal /
          ((1 / 8 : ℝ) * Real.log (R : ℝ)) := by
      exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg
        (mul_pos (by norm_num) hlog) hG
    _ = 8 * (diskGreen R y 0).toReal / Real.log (R : ℝ) := by
      field_simp

/-- Interface for the remaining spatial estimate: any upper bound `B` on the
off-diagonal killed Green numerator immediately gives `8 B / log R` for the
hitting probability. -/
theorem hitZeroBeforeExit_real_le_of_diskGreen_le
    {R : ℕ} (hR : 2 ≤ R) (y : Site) {B : ℝ}
    (hB : (diskGreen R y 0).toReal ≤ B) :
    incrementLaw.real
        (hitBeforeExitEvent (squareDisk R : Set Site) y 0) ≤
      8 * B / Real.log (R : ℝ) := by
  refine (hitZeroBeforeExit_real_le_eight_mul_green_div_log hR y).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hB (by norm_num))
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ R by omega)))

end Erdos1166.KilledGreen
