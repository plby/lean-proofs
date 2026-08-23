import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAShapeBridge

/-!
The source large-gap error in Proposition 4.7.  On a canonical nearest-
neighbour path, the Euclidean distance between two creation sites is at most
the elapsed time between their creation.  Thus a gap larger than `exp m`
forces the later threshold beyond the near-critical horizon; Proposition 1.3
then supplies an exponentially small probability.
-/

namespace Erdos1166.HLOZProp47FarGap

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZNearCriticalBridge HLOZProp13FromAppendix
open HLOZAppendixAShapeBridge HLOZScreeningAssembly
open HLOZPairing.ScreeningBridge
open HLOZProp47Parameters HLOZProp47SourceObjects HLOZProp47SourceAssembly

/-- Manhattan distance on the planar integer lattice. -/
def siteManhattanDistance (x y : Site) : ℕ :=
  (x.1 - y.1).natAbs + (x.2 - y.2).natAbs

theorem siteDistance_le_manhattan (x y : Site) :
    siteDistance x y ≤ siteManhattanDistance x y := by
  rw [siteDistance, Real.sqrt_le_iff]
  constructor
  · positivity
  · unfold siteSquaredDistance siteManhattanDistance
    push_cast
    have h₁ : 0 ≤ ((x.1 - y.1).natAbs : ℝ) := by positivity
    have h₂ : 0 ≤ ((x.2 - y.2).natAbs : ℝ) := by positivity
    nlinarith

theorem siteManhattanDistance_triangle (x y z : Site) :
    siteManhattanDistance x z ≤
      siteManhattanDistance x y + siteManhattanDistance y z := by
  unfold siteManhattanDistance
  have h₁ : (x.1 - z.1).natAbs ≤
      (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
    rw [show x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) by ring]
    exact Int.natAbs_add_le _ _
  have h₂ : (x.2 - z.2).natAbs ≤
      (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
    rw [show x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) by ring]
    exact Int.natAbs_add_le _ _
  omega

theorem siteManhattanDistance_directionStep (x : Site) (d : Direction) :
    siteManhattanDistance x (x + directionStep d) = 1 := by
  fin_cases d <;> norm_num [siteManhattanDistance, directionStep]

theorem simpleRandomWalk_succ (ω : ℕ → Direction) (n : ℕ) :
    simpleRandomWalk ω (n + 1) =
      simpleRandomWalk ω n + directionStep (ω n) := by
  simp [simpleRandomWalk, Finset.sum_range_succ]

/-- A nearest-neighbour walk travels at most one unit of Euclidean distance
per elapsed integer time. -/
theorem siteDistance_simpleRandomWalk_le_elapsed
    (ω : ℕ → Direction) {a b : ℕ} (hab : a ≤ b) :
    siteDistance (simpleRandomWalk ω a) (simpleRandomWalk ω b) ≤
      ((b - a : ℕ) : ℝ) := by
  have hman : siteManhattanDistance (simpleRandomWalk ω a)
      (simpleRandomWalk ω b) ≤ b - a := by
    induction b with
    | zero =>
        have : a = 0 := by omega
        subst a
        simp [siteManhattanDistance]
    | succ b ih =>
        by_cases ha : a = b + 1
        · subst a
          simp [siteManhattanDistance]
        · have hab' : a ≤ b := by omega
          calc
            siteManhattanDistance (simpleRandomWalk ω a)
                (simpleRandomWalk ω (b + 1)) ≤
                siteManhattanDistance (simpleRandomWalk ω a)
                    (simpleRandomWalk ω b) +
                  siteManhattanDistance (simpleRandomWalk ω b)
                    (simpleRandomWalk ω (b + 1)) :=
              siteManhattanDistance_triangle _ _ _
            _ ≤ (b - a) + 1 := by
              rw [simpleRandomWalk_succ,
                siteManhattanDistance_directionStep]
              omega
            _ = b + 1 - a := by omega
  exact (siteDistance_le_manhattan _ _).trans (by exact_mod_cast hman)

/-- The rounded near-critical horizon is eventually much smaller than the
distance cutoff `exp m` used by the Proposition 4.7 mesh. -/
theorem eventually_nearCriticalHorizon_lt_exp_level :
    ∀ᶠ m : ℕ in atTop,
      (nearCriticalHorizon m : ℝ) < Real.exp (m : ℝ) := by
  have hsublinear :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := (4 / 3 : ℝ) * Real.sqrt Real.pi) (d := (1 / 2 : ℝ))
      (p := (1 / 2 : ℝ)) (q := 1)
      (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_log_horizon_le_four_thirds_leading,
    hsublinear, eventually_ge_atTop 1] with m hlog hsub hm
  have hsub' : (4 / 3 : ℝ) *
      (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ≤ (m : ℝ) / 2 := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [Real.sqrt_eq_rpow] at hsub
    calc
      (4 / 3 : ℝ) *
          (Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ)) =
          (4 / 3 : ℝ) * Real.pi ^ (1 / 2 : ℝ) *
            (m : ℝ) ^ (1 / 2 : ℝ) := by ring
      _ ≤ (1 / 2 : ℝ) * (m : ℝ) ^ (1 : ℝ) := hsub
      _ = (m : ℝ) / 2 := by rw [Real.rpow_one]; ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply (Real.log_lt_iff_lt_exp (by
    exact_mod_cast nearCriticalHorizon_pos m)).mp
  exact hlog.trans_lt (by linarith)

/-- On canonical nearest-neighbour paths, a source far gap forces the later
creation threshold past the near-critical cutoff. -/
theorem simpleRandomWalk_preimage_farGapEvent_subset_lateOnThresholdEvent
    {m : ℕ} (hm : (nearCriticalHorizon m : ℝ) < Real.exp (m : ℝ))
    (i : Fin 6) (r : StageIndex) :
    simpleRandomWalk ⁻¹' farGapEvent m i r ⊆
      simpleRandomWalk ⁻¹'
        lateOnThresholdEvent nearCriticalHorizon m (stageNumber r + 1) := by
  intro ω hfar
  rcases hfar with ⟨hprefix, hfarDistance⟩
  have hM : simpleRandomWalk ω ∈
      thresholdTimeEventK m (stageNumber r + 1) := by
    exact hprefix.1
  refine ⟨?_, hM⟩
  change (nearCriticalHorizon m : WithTop ℕ) <
    firstKSitesReachLevel m (stageNumber r + 1) (simpleRandomWalk ω)
  by_contra hnotLate
  have hthresholdLe :
      firstKSitesReachLevel m (stageNumber r + 1) (simpleRandomWalk ω) ≤
        (nearCriticalHorizon m : WithTop ℕ) := le_of_not_gt hnotLate
  have hfinite :
      firstKSitesReachLevel m (stageNumber r + 1) (simpleRandomWalk ω) ≠ ⊤ :=
    ne_top_of_lt hM
  have htimes :
      (firstKSitesReachLevel m (stageNumber r) (simpleRandomWalk ω)).untopA ≤
        (firstKSitesReachLevel m (stageNumber r + 1)
          (simpleRandomWalk ω)).untopA := by
    exact WithTop.untopA_mono hfinite
      (firstKSitesReachLevel_mono_k (simpleRandomWalk ω) m (by omega))
  have hlaterLe :
      (firstKSitesReachLevel m (stageNumber r + 1)
        (simpleRandomWalk ω)).untopA ≤ nearCriticalHorizon m :=
    WithTop.untopA_le hthresholdLe
  have hdistance := siteDistance_simpleRandomWalk_le_elapsed ω htimes
  have helapsed :
      (firstKSitesReachLevel m (stageNumber r + 1)
          (simpleRandomWalk ω)).untopA -
        (firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk ω)).untopA ≤ nearCriticalHorizon m :=
    (Nat.sub_le _ _).trans hlaterLe
  have hdistance' :
      siteDistance
          (levelCreationSite (simpleRandomWalk ω) m (stageNumber r))
          (levelCreationSite (simpleRandomWalk ω) m (stageNumber r + 1)) ≤
        (nearCriticalHorizon m : ℝ) := by
    rw [levelCreationSite, levelCreationSite]
    exact hdistance.trans (by exact_mod_cast helapsed)
  exact (not_lt_of_ge hdistance')
    (hm.trans hfarDistance)

theorem measurableSet_lateOnThresholdEvent
    (ψ : ℕ → ℕ) (m k : ℕ) :
    MeasurableSet (lateOnThresholdEvent ψ m k) := by
  apply (HLOZNearCriticalBridge.measurableSet_lateThresholdEvent ψ m k).inter
  exact measurableSet_lt
    (isStoppingTime_firstKSitesReachLevel m k).measurable'
    (isStoppingTime_firstKSitesReachLevel (m + 1) 1).measurable'

/-- Before analytic simplification, the large-gap probability is bounded by
the exact Proposition-1.3 lower-tail event at the near-critical horizon. -/
theorem farGapEvent_measure_le_proposition13LowerTailEvent
    {m : ℕ} (hm : (nearCriticalHorizon m : ℝ) < Real.exp (m : ℝ))
    (hthreshold : (m : ℝ) <
      proposition13Threshold (nearCriticalHorizon m))
    (i : Fin 6) (r : StageIndex) :
    simpleRandomWalkLaw (farGapEvent m i r) ≤
      simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m)) := by
  calc
    simpleRandomWalkLaw (farGapEvent m i r) ≤
        simpleRandomWalkLaw
          (lateOnThresholdEvent nearCriticalHorizon m
            (stageNumber r + 1)) := by
      rw [simpleRandomWalkLaw,
        Measure.map_apply measurable_simpleRandomWalk
          (measurableSet_farGapEvent m i r),
        Measure.map_apply measurable_simpleRandomWalk
          (measurableSet_lateOnThresholdEvent nearCriticalHorizon m
            (stageNumber r + 1))]
      exact measure_mono
        (simpleRandomWalk_preimage_farGapEvent_subset_lateOnThresholdEvent
          hm i r)
    _ ≤ simpleRandomWalkLaw (lowerMaxEvent nearCriticalHorizon m) :=
      measure_lateOnThresholdEvent_le_lowerMaxEvent
        simpleRandomWalkLaw nearCriticalHorizon m (stageNumber r + 1)
    _ ≤ simpleRandomWalkLaw
          (proposition13LowerTailEvent (nearCriticalHorizon m)) :=
      measure_mono
        (lowerMaxEvent_subset_proposition13LowerTailEvent
          nearCriticalHorizon m hthreshold)

/-- The exponentially small Proposition-1.3 error is eventually below the
exact prefactored cubic source rate, already with coefficient one. -/
theorem eventually_exp_neg_level_le_sourceExceptionalRate :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(m : ℝ))) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hpoly := (Filter.tendsto_add_atTop_nat 1).eventually
    (eventually_exponential_error_absorbed (by norm_num : (0 : ℝ) < 1))
  have hlog := (Filter.tendsto_add_atTop_nat 1).eventually
    (eventually_log_rpow_le_rpow
      (p := (2 : ℝ)) (ε := (1 / 2 : ℝ)) (by norm_num))
  filter_upwards [hpoly, hlog, eventually_ge_atTop 2] with m hpoly hlog hm
  have hsqrt : Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · exact_mod_cast (show m + 1 ≤ m ^ 2 by nlinarith)
  have hlogSq : Real.log ((m : ℝ) + 1) ^ 2 ≤ (m : ℝ) := by
    have hsqrt' : (((m + 1 : ℕ) : ℝ)) ^ (1 / 2 : ℝ) ≤ (m : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one, ← Real.sqrt_eq_rpow] using hsqrt
    have := hlog.trans hsqrt'
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using this
  have hexpLog : Real.exp (-(m : ℝ)) ≤
      Real.exp (-1 * Real.log ((m : ℝ) + 1) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hreal : Real.exp (-(m : ℝ)) ≤
      ((m : ℝ) + 1) ^ (-(3 * kappa)) :=
    hexpLog.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hpoly)
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  have hrate : ENNReal.ofReal
      (((m : ℝ) + 1) ^ (-(3 * kappa))) =
        sourceExceptionalRateWithPrefactor m 1 kappa := by
    rw [← ENNReal.ofReal_rpow_of_pos (by positivity), hbase]
    simp [sourceExceptionalRateWithPrefactor, sourceExceptionalRate]
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq hrate

/-- The square-exit Appendix-A input discharges the named Proposition 4.7
far-gap estimate, with source prefactor one. -/
theorem prop47FarGapEstimate_of_appendixDiskEstimate
    (hdisk : AppendixDiskEstimate) :
    Prop47FarGapEstimate 1 := by
  filter_upwards [eventually_nearCriticalHorizon_lt_exp_level,
    eventually_level_lt_proposition13Threshold_nearCriticalHorizon,
    eventually_nearCritical_prop13_bound hdisk,
    eventually_exp_neg_level_le_sourceExceptionalRate] with
      m hhorizon hthreshold hprop13 hrate
  intro i r
  exact (farGapEvent_measure_le_proposition13LowerTailEvent
      hhorizon hthreshold i r).trans (hprop13.trans hrate)

/-- Published Euclidean-disk form of the same source input.  The checked
shape bridge supplies the square-exit estimate used above. -/
theorem prop47FarGapEstimate_of_euclideanAppendixDiskEstimate
    (hsource : EuclideanAppendixDiskEstimate) :
    Prop47FarGapEstimate 1 :=
  prop47FarGapEstimate_of_appendixDiskEstimate
    (appendixDiskEstimate_of_euclidean hsource)

end Erdos1166.HLOZProp47FarGap
