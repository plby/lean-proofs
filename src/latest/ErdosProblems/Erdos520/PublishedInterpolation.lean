import ErdosProblems.Erdos520.AlignedGlobalTestAssembly
import Mathlib.Analysis.MeanInequalitiesPow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# The exact Lau--Tenenbaum--Wu interpolation input

Caich invokes Lau--Tenenbaum--Wu, Lemma 2.3, only for the squarefree
Rademacher multiplicative function and only on the root-exponential test
mesh

`x_i = floor (exp (i^(1/350)))`.

The published result is not reproduced here as an axiom.  Instead this file
defines its precise specialization, proves the endpoint/index normalization
bridge to `AEIntervalIncrementBound`, and wires that one proposition to the
critical upper-bound endpoint.
-/

/-- The value `c₀ = 1/350` explicitly recorded by Caich for the choice
`A = 1` in the Lau--Tenenbaum--Wu interpolation lemma. -/
def ltwRootExpDenominator : ℕ := 350

theorem ltwRootExpDenominator_pos : 0 < ltwRootExpDenominator := by
  norm_num [ltwRootExpDenominator]

/-- The exact test sequence used in the Rademacher specialization. -/
noncomputable def ltwRademacherTestPoint (i : ℕ) : ℕ :=
  alignedRootExpTestPoint ltwRootExpDenominator i

theorem ltwRademacherTestPoint_eq (i : ℕ) :
    ltwRademacherTestPoint i =
      Nat.floor (Real.exp ((i : ℝ) ^ (1 / (350 : ℝ)))) := by
  rfl

theorem ltwRademacherTestPoint_mono : Monotone ltwRademacherTestPoint :=
  alignedRootExpTestPoint_mono ltwRootExpDenominator

theorem tendsto_ltwRademacherTestPoint_atTop :
    Tendsto ltwRademacherTestPoint atTop atTop :=
  tendsto_alignedRootExpTestPoint_atTop ltwRootExpDenominator_pos

/-- The `A = 1` upper-endpoint normalization in LTW Lemma 2.3. -/
noncomputable def ltwInterpolationScale (N : ℕ) : ℝ :=
  Real.sqrt N / Real.log (N : ℝ)

/-- Exact Rademacher/root-exponential specialization of LTW Lemma 2.3.

The source writes the interval as `x_(i-1) < x ≤ x_i`; the index shift
below writes the same assertion as `x_i < N ≤ x_(i+1)`.  The implicit
constant may depend on the sample, exactly as expressed by `≪_A` in the
almost-sure statement. -/
def LauTenenbaumWuRademacherInterpolation : Prop :=
  ∀ᵐ omega ∂μ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ i : ℕ in atTop, ∀ N : ℕ,
      ltwRademacherTestPoint i < N →
      N ≤ ltwRademacherTestPoint (i + 1) →
        |partialSum omega N - partialSum omega (ltwRademacherTestPoint i)| ≤
          C * ltwInterpolationScale (ltwRademacherTestPoint (i + 1))

theorem eventually_ltwInterpolationScale_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ ltwInterpolationScale N := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (0 : ℝ))] with N hN
  exact div_nonneg (Real.sqrt_nonneg _) hN

/-- Adding the left endpoint (where the increment is zero) converts the
strict source interval exactly into `AEIntervalIncrementBound`. -/
theorem aeIntervalIncrementBound_ltwScale_of_LauTenenbaumWu
    (hLTW : LauTenenbaumWuRademacherInterpolation) :
    AEIntervalIncrementBound μ partialSum ltwInterpolationScale
      ltwRademacherTestPoint := by
  filter_upwards [hLTW] with omega homega
  obtain ⟨C, hC, hbound⟩ := homega
  refine ⟨C, hC, ?_⟩
  have hscaleNonneg : ∀ᶠ i : ℕ in atTop,
      0 ≤ ltwInterpolationScale (ltwRademacherTestPoint (i + 1)) :=
    (tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      eventually_ltwInterpolationScale_nonneg
  filter_upwards [hbound, hscaleNonneg] with i hi hscalei
  intro N hiN hNi
  by_cases hleft : N = ltwRademacherTestPoint i
  · subst N
    simpa using! mul_nonneg hC hscalei
  · exact hi N (lt_of_le_of_ne hiN (Ne.symm hleft)) hNi

/-- Conversely, the `AEIntervalIncrementBound` spelling contains the strict
source statement as an immediate restriction. -/
theorem LauTenenbaumWu_of_aeIntervalIncrementBound_ltwScale
    (hLTW : AEIntervalIncrementBound μ partialSum ltwInterpolationScale
      ltwRademacherTestPoint) :
    LauTenenbaumWuRademacherInterpolation := by
  filter_upwards [hLTW] with omega homega
  obtain ⟨C, hC, hbound⟩ := homega
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with i hi
  intro N hiN hNi
  exact hi N hiN.le hNi

theorem LauTenenbaumWu_iff_aeIntervalIncrementBound_ltwScale :
    LauTenenbaumWuRademacherInterpolation ↔
      AEIntervalIncrementBound μ partialSum ltwInterpolationScale
        ltwRademacherTestPoint := by
  constructor
  · exact aeIntervalIncrementBound_ltwScale_of_LauTenenbaumWu
  · exact LauTenenbaumWu_of_aeIntervalIncrementBound_ltwScale

/-- The LTW logarithmic saving is eventually much smaller than every repaired
critical scale. -/
theorem eventually_ltwInterpolationScale_le_criticalScale
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ltwInterpolationScale N ≤ criticalScale η N := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      tendsto_log₂_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with N hlogOne hlog₂One
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hcriticalFactor : 1 ≤ log₂ N ^ (1 / 4 + η) :=
    Real.one_le_rpow hlog₂One (by linarith)
  calc
    ltwInterpolationScale N =
        Real.sqrt (N : ℝ) / Real.log (N : ℝ) := rfl
    _ ≤ Real.sqrt (N : ℝ) := div_le_self hsqrt hlogOne
    _ ≤ Real.sqrt (N : ℝ) * log₂ N ^ (1 / 4 + η) := by
      simpa only [mul_one] using!
        (mul_le_mul_of_nonneg_left hcriticalFactor hsqrt)
    _ = criticalScale η N := rfl

/-! ## Deterministic adjacent-scale comparison on the LTW mesh -/

/-- Consecutive LTW test points differ by at most a fixed factor.  The very
coarse factor `6` absorbs both the exponential increment and the floor. -/
theorem ltwRademacherTestPoint_succ_le_six_mul (i : ℕ) :
    ltwRademacherTestPoint (i + 1) ≤
      6 * ltwRademacherTestPoint i := by
  let p : ℝ := 1 / (350 : ℝ)
  let y : ℝ := Real.exp ((i : ℝ) ^ p)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by norm_num [p]
  have hroot : ((i + 1 : ℕ) : ℝ) ^ p ≤ (i : ℝ) ^ p + 1 := by
    have h := Real.rpow_add_le_add_rpow
      (show (0 : ℝ) ≤ i by positivity) (show (0 : ℝ) ≤ 1 by norm_num)
      hp0 hp1
    simpa only [Nat.cast_add, Nat.cast_one, Real.one_rpow] using! h
  have hreal : Real.exp (((i + 1 : ℕ) : ℝ) ^ p) ≤
      Real.exp 1 * y := by
    calc
      Real.exp (((i + 1 : ℕ) : ℝ) ^ p) ≤
          Real.exp ((i : ℝ) ^ p + 1) := Real.exp_le_exp.mpr hroot
      _ = Real.exp 1 * y := by rw [Real.exp_add]; ring
  have hyOne : 1 ≤ Nat.floor y := by
    apply Nat.le_floor
    dsimp [y]
    simpa only [Nat.cast_one] using! Real.one_le_exp
      (Real.rpow_nonneg (show (0 : ℝ) ≤ i by positivity) p)
  have hyFloor : y ≤ 2 * (Nat.floor y : ℝ) := by
    have hylt : y < (Nat.floor y : ℝ) + 1 := Nat.lt_floor_add_one y
    have hyOneR : (1 : ℝ) ≤ Nat.floor y := by exact_mod_cast hyOne
    linarith
  have hcast : (ltwRademacherTestPoint (i + 1) : ℝ) ≤
      6 * (ltwRademacherTestPoint i : ℝ) := by
    rw [ltwRademacherTestPoint_eq, ltwRademacherTestPoint_eq]
    change (Nat.floor (Real.exp (((i + 1 : ℕ) : ℝ) ^ p)) : ℝ) ≤
      6 * (Nat.floor y : ℝ)
    calc
      (Nat.floor (Real.exp (((i + 1 : ℕ) : ℝ) ^ p)) : ℝ) ≤
          Real.exp (((i + 1 : ℕ) : ℝ) ^ p) :=
        Nat.floor_le (Real.exp_pos _).le
      _ ≤ Real.exp 1 * y := hreal
      _ ≤ 3 * y :=
        mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by positivity)
      _ ≤ 3 * (2 * (Nat.floor y : ℝ)) :=
        mul_le_mul_of_nonneg_left hyFloor (by norm_num)
      _ = 6 * (Nat.floor y : ℝ) := by ring
  exact_mod_cast hcast

/-- The repaired critical scale is monotone after an absolute initial
segment. -/
theorem eventually_criticalScale_mono_from
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m →
      criticalScale η n ≤ criticalScale η m := by
  filter_upwards [eventually_gt_atTop (1 : ℕ), eventually_log₂_pos]
      with n hn hlogn
  intro m hnm
  have hm : 1 < m := hn.trans_le hnm
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hnm)
  have hlog : log₂ n ≤ log₂ m := by
    unfold log₂
    apply Real.strictMonoOn_log.monotoneOn
    · exact Real.log_pos (by exact_mod_cast hn)
    · exact Real.log_pos (by exact_mod_cast hm)
    · apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < n
        positivity
      · change (0 : ℝ) < m
        exact_mod_cast (show 0 < m by omega)
      · exact_mod_cast hnm
  have hexponent : 0 ≤ 1 / 4 + η := by linarith
  have hpow : log₂ n ^ (1 / 4 + η) ≤
      log₂ m ^ (1 / 4 + η) :=
    Real.rpow_le_rpow hlogn.le hlog hexponent
  unfold criticalScale
  exact mul_le_mul hsqrt hpow (Real.rpow_nonneg hlogn.le _)
    (Real.sqrt_nonneg _)

/-- Explicit comparison constant for adjacent LTW test intervals. -/
noncomputable def ltwCriticalAdjacentConstant (η : ℝ) : ℝ :=
  3 * (2 : ℝ) ^ (1 / 4 + η)

theorem ltwCriticalAdjacentConstant_nonneg (η : ℝ) :
    0 ≤ ltwCriticalAdjacentConstant η := by
  unfold ltwCriticalAdjacentConstant
  positivity

theorem one_le_ltwCriticalAdjacentConstant
    {η : ℝ} (hη : 0 < η) :
    1 ≤ ltwCriticalAdjacentConstant η := by
  unfold ltwCriticalAdjacentConstant
  have hpow : 1 ≤ (2 : ℝ) ^ (1 / 4 + η) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  nlinarith

private theorem log₂_le_two_mul_log₂_of_le_six_mul
    {n m : ℕ} (hn : 6 ≤ n) (hnm : n ≤ m) (hmn : m ≤ 6 * n)
    (hlarge : Real.log 2 ≤ log₂ n) :
    log₂ m ≤ 2 * log₂ n := by
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := hnpos.trans_le hnm
  have hmnSq : m ≤ n * n := by
    calc
      m ≤ 6 * n := hmn
      _ ≤ n * n := by nlinarith
  have hlogn : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hlogm : 0 < Real.log (m : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < m by omega)
  have hlogsq : 0 < Real.log ((n * n : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n * n by nlinarith)
  have hinner : Real.log (m : ℝ) ≤
      Real.log ((n * n : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · change (0 : ℝ) < m
      positivity
    · change (0 : ℝ) < ((n * n : ℕ) : ℝ)
      exact_mod_cast Nat.mul_pos hnpos hnpos
    · exact_mod_cast hmnSq
  have houter : Real.log (Real.log (m : ℝ)) ≤
      Real.log (Real.log ((n * n : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hlogm hlogsq hinner
  calc
    log₂ m = Real.log (Real.log (m : ℝ)) := rfl
    _ ≤ Real.log (Real.log ((n * n : ℕ) : ℝ)) := houter
    _ = Real.log (2 * Real.log (n : ℝ)) := by
      congr 1
      rw [Nat.cast_mul, Real.log_mul]
      · ring
      · positivity
      · positivity
    _ = Real.log 2 + Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_mul (by norm_num) hlogn.ne']
    _ ≤ log₂ n + log₂ n := by
      simpa only [log₂, add_comm] using!
        add_le_add_right hlarge (log₂ n)
    _ = 2 * log₂ n := by ring

private theorem criticalScale_le_ltwCriticalAdjacentConstant_mul
    {η : ℝ} (hη : 0 < η) {n m : ℕ}
    (hn : 6 ≤ n) (hnm : n ≤ m) (hmn : m ≤ 6 * n)
    (hlarge : Real.log 2 ≤ log₂ n) :
    criticalScale η m ≤
      ltwCriticalAdjacentConstant η * criticalScale η n := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 < log₂ n := hlogTwo.trans_le hlarge
  have hlognm : log₂ n ≤ log₂ m := by
    unfold log₂
    apply Real.strictMonoOn_log.monotoneOn
    · exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    · exact Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    · apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < n
        positivity
      · change (0 : ℝ) < m
        exact_mod_cast (show 0 < m by omega)
      · exact_mod_cast hnm
  have hlogm : 0 < log₂ m := hlogn.trans_le hlognm
  have hlogUpper : log₂ m ≤ 2 * log₂ n :=
    log₂_le_two_mul_log₂_of_le_six_mul hn hnm hmn hlarge
  have hexponent : 0 ≤ 1 / 4 + η := by linarith
  have hpower : log₂ m ^ (1 / 4 + η) ≤
      (2 : ℝ) ^ (1 / 4 + η) * log₂ n ^ (1 / 4 + η) := by
    calc
      log₂ m ^ (1 / 4 + η) ≤
          (2 * log₂ n) ^ (1 / 4 + η) :=
        Real.rpow_le_rpow hlogm.le hlogUpper hexponent
      _ = (2 : ℝ) ^ (1 / 4 + η) *
          log₂ n ^ (1 / 4 + η) := by
        rw [Real.mul_rpow (by norm_num) hlogn.le]
  have hsqrtSix : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sqrt_nonneg 6]
  have hcast : (m : ℝ) ≤ 6 * (n : ℝ) := by exact_mod_cast hmn
  have hsqrt : Real.sqrt (m : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (m : ℝ) ≤ Real.sqrt (6 * (n : ℝ)) :=
        Real.sqrt_le_sqrt hcast
      _ = Real.sqrt 6 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      _ ≤ 3 * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrtSix (Real.sqrt_nonneg _)
  unfold criticalScale ltwCriticalAdjacentConstant
  calc
    Real.sqrt (m : ℝ) * log₂ m ^ (1 / 4 + η) ≤
        (3 * Real.sqrt (n : ℝ)) *
          ((2 : ℝ) ^ (1 / 4 + η) *
            log₂ n ^ (1 / 4 + η)) :=
      mul_le_mul hsqrt hpower (Real.rpow_nonneg hlogm.le _)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = (3 * (2 : ℝ) ^ (1 / 4 + η)) *
        (Real.sqrt (n : ℝ) * log₂ n ^ (1 / 4 + η)) := by ring

/-- The exact root-exponential LTW mesh supplies its own deterministic scale
comparison.  No scale-comparability hypothesis is needed by the endpoint. -/
theorem adjacentScaleComparable_criticalScale_ltwRademacherTestPoint
    {η : ℝ} (hη : 0 < η) :
    AdjacentScaleComparable (criticalScale η)
      ltwRademacherTestPoint (ltwCriticalAdjacentConstant η) := by
  refine ⟨ltwCriticalAdjacentConstant_nonneg η, ?_⟩
  have htestSix : ∀ᶠ i : ℕ in atTop,
      6 ≤ ltwRademacherTestPoint i :=
    tendsto_ltwRademacherTestPoint_atTop.eventually
      (eventually_ge_atTop 6)
  have htestLog : ∀ᶠ i : ℕ in atTop,
      Real.log 2 ≤ log₂ (ltwRademacherTestPoint i) :=
    (tendsto_log₂_atTop.comp
      tendsto_ltwRademacherTestPoint_atTop).eventually
        (eventually_ge_atTop (Real.log 2))
  have hscaleMono : ∀ᶠ i : ℕ in atTop, ∀ N : ℕ,
      ltwRademacherTestPoint i ≤ N →
        criticalScale η (ltwRademacherTestPoint i) ≤
          criticalScale η N :=
    tendsto_ltwRademacherTestPoint_atTop.eventually
      (eventually_criticalScale_mono_from hη)
  filter_upwards [htestSix, htestLog, hscaleMono]
      with i hiSix hiLog hiScaleMono
  intro N hiN _hNupper
  have hiSucc : ltwRademacherTestPoint i ≤
      ltwRademacherTestPoint (i + 1) :=
    ltwRademacherTestPoint_mono (Nat.le_add_right i 1)
  have hendpoint : criticalScale η (ltwRademacherTestPoint (i + 1)) ≤
      ltwCriticalAdjacentConstant η *
        criticalScale η (ltwRademacherTestPoint i) :=
    criticalScale_le_ltwCriticalAdjacentConstant_mul hη hiSix hiSucc
      (ltwRademacherTestPoint_succ_le_six_mul i) hiLog
  have hlogTest : 0 < log₂ (ltwRademacherTestPoint i) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hiLog
  have hscaleTestNonneg :
      0 ≤ criticalScale η (ltwRademacherTestPoint i) := by
    unfold criticalScale
    exact mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hlogTest.le _)
  have htestToN := hiScaleMono N hiN
  have hscaleNNonneg : 0 ≤ criticalScale η N :=
    hscaleTestNonneg.trans htestToN
  constructor
  · exact htestToN.trans (by
      calc
        criticalScale η N = 1 * criticalScale η N := by ring
        _ ≤ ltwCriticalAdjacentConstant η * criticalScale η N :=
          mul_le_mul_of_nonneg_right
            (one_le_ltwCriticalAdjacentConstant hη) hscaleNNonneg)
  · exact hendpoint.trans
      (mul_le_mul_of_nonneg_left htestToN
        (ltwCriticalAdjacentConstant_nonneg η))

/-- Exact normalization bridge from LTW Lemma 2.3 to the increment input at
the repaired critical scale. -/
theorem aeIntervalIncrementBound_critical_of_LauTenenbaumWu
    {η : ℝ} (hη : 0 < η)
    (hLTW : LauTenenbaumWuRademacherInterpolation) :
    AEIntervalIncrementBound μ partialSum (criticalScale η)
      ltwRademacherTestPoint := by
  have hfast := aeIntervalIncrementBound_ltwScale_of_LauTenenbaumWu hLTW
  have hscale : ∀ᶠ i : ℕ in atTop,
      ltwInterpolationScale (ltwRademacherTestPoint (i + 1)) ≤
        criticalScale η (ltwRademacherTestPoint (i + 1)) :=
    (tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_ltwInterpolationScale_le_criticalScale hη)
  filter_upwards [hfast] with omega homega
  obtain ⟨C, hC, hbound⟩ := homega
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hscale] with i hi hscalei
  intro N hiN hNi
  exact (hi N hiN hNi).trans
    (mul_le_mul_of_nonneg_left hscalei hC)

/-- Paper-facing endpoint with no generic "published interpolation" hook:
the only external proposition is the exact Rademacher, `A=1`, `c₀=1/350`
specialization stated above. -/
theorem criticalUpperBound_of_ltwRademacherTestPoints
    (hpoints : ∀ η : ℝ, 0 < η →
      AETestPointBound μ partialSum (criticalScale η)
        ltwRademacherTestPoint)
    (hLTW : LauTenenbaumWuRademacherInterpolation) :
    CriticalUpperBound μ partialSum := by
  apply criticalUpperBound_of_ae_testPoints_and_increments
    (fun _η => ltwRademacherTestPoint) ltwCriticalAdjacentConstant
  · intro η hη
    exact ltwRademacherTestPoint_mono
  · intro η hη
    exact tendsto_ltwRademacherTestPoint_atTop
  · intro η hη
    exact adjacentScaleComparable_criticalScale_ltwRademacherTestPoint hη
  · exact hpoints
  · intro η hη
    exact aeIntervalIncrementBound_critical_of_LauTenenbaumWu hη hLTW

end Problem520
end Erdos
