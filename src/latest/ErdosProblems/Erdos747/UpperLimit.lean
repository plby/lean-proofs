import ErdosProblems.Erdos747.SummedStructuralErrors

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def standardDeletionBase (a : ℝ) (n t : ℕ) (e : DeletionHistory (allEdges n) t) : Prop :=
  StandardAggregateLayerRegular n ((allEdges n).card - t) a (historyState e t le_rfl)

def standardDeletionStructural (epsilon a : ℝ) (n t : ℕ) (e : DeletionHistory (allEdges n) t) : Prop :=
  t ≤ (allEdges n).card - upperEdgeCount epsilon n ∧
    KahnLayerInput n (coordinateDegreeFloor n ((allEdges n).card - t) a)
      (coordinateDegreeCeil n ((allEdges n).card - t)) (standardCodegreeCap n ((allEdges n).card - t))
      (coordinatePairCutoff n a) (coordinateTailFloor n ((allEdges n).card - t) a)
      (coordinateResidualAllowance n (coordinateExceptionFraction a)) (coordinateVertexAllowance n)
      (deletionCountError n (thresholdControlledWeightFactor a))
      (thresholdUpperSpreadFactor a) (coordinateExceptionFraction a) (thresholdTransferFactor a)
      (historyState e t le_rfl)

lemma eventually_standard_deletion_valid (epsilon a : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᶠ n in atTop,
      upperEdgeCount epsilon n ≤ (allEdges n).card ∧
      (∀ t (e : DeletionHistory (allEdges n) t),
        DeletionHistoryGood (thresholdControlledWeightFactor a) t e →
        stoppedCenteredSum (thresholdControlledWeightFactor a) t e ≤ deletionDeviationScale n →
        standardDeletionBase a n t e → standardDeletionStructural epsilon a n t e →
          DeletionStepGood (thresholdControlledWeightFactor a) e) ∧
      (∀ t, t ≤ (allEdges n).card - upperEdgeCount epsilon n →
        finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ deletionDeviationScale n < stoppedCenteredSum (thresholdControlledWeightFactor a) t e) +
          finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ standardDeletionBase a n t e ∧ ¬ standardDeletionStructural epsilon a n t e) ≤
          levelFailureBound n) := by
  let C := thresholdControlledWeightFactor a
  have hC : 0 < C := thresholdControlledWeightFactor_pos a ha
  have hcount0 : ∀ᶠ n in atTop, 0 ≤ deletionCountError n C := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact deletionCountError_nonneg n C hn
  have hstruct := eventually_standard_structural_failure_probability_le epsilon a
    (fun n ↦ deletionCountError n C) hepsilon0 ha ha1 (deletionCountError_tendsto_zero C) hcount0
  have hstop := eventually_stoppedCenteredSum_probability_le epsilon C hepsilon0 hepsilon1 hC
  have hexceptions := eventually_coordinate_exception_budgets a ha ha1
  have hcollision := eventually_upperEdgeCount_collision_condition epsilon hepsilon0 hepsilon1
  have hlarge := (log_vertexCount_tendsto_atTop.const_mul_atTop ha).eventually_ge_atTop 8
  filter_upwards [hstruct, hstop, hexceptions, hcollision, hlarge,
    log_vertexCount_tendsto_atTop.eventually_ge_atTop (2 * C),
    log_vertexCount_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop 200]
    with n hstructn hstopn hexn hcolln hlargen hlogC hlog hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMmean := upperEdgeCount_mean_ge epsilon hepsilon0 n (by omega)
  have hMpos : 0 < upperEdgeCount epsilon n := by
    have hmean1 := hlog.trans hMmean
    have hMposR : (0 : ℝ) < upperEdgeCount epsilon n :=
      (div_pos_iff.mp (lt_of_lt_of_le zero_lt_one hmean1)).elim
        (fun h ↦ h.1) (fun h ↦ False.elim (not_lt_of_ge hnR.le h.2))
    exact_mod_cast hMposR
  have hMvalid : upperEdgeCount epsilon n ≤ (allEdges n).card := by
    nlinarith only [hcolln, hMpos]
  refine ⟨hMvalid, ?_, ?_⟩
  · intro t e hgood hstopped hbase hStructural
    rcases hStructural with ⟨ht, hinput⟩
    have htK : t < (allEdges n).card := by omega
    have hremaining : upperEdgeCount epsilon n ≤ (allEdges n).card - t := by omega
    have hmean := supercritical_mean_lower epsilon hepsilon0 n ((allEdges n).card - t) (by omega) hremaining
    have hlargeM := hlargen.trans (mul_le_mul_of_nonneg_left hmean ha.le)
    have hround := coordinate_degree_rounding_bounds n ((allEdges n).card - t) a ha hlargeM
    have hCb : ∀ i < t, C * deletionGamma n (allEdges n) i ≤ 1 / 2 := by
      intro i hi
      have hgam := deletionGamma_le_inv_log epsilon hepsilon0 n (upperEdgeCount epsilon n) i
        (by omega) le_rfl hMvalid (by omega)
      have hlogpos : 0 < Real.log ((3 * n : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hlog
      calc
        _ ≤ C * (1 / Real.log ((3 * n : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hgam hC.le
        _ = C / Real.log ((3 * n : ℕ) : ℝ) := by ring
        _ ≤ 1 / 2 := (div_le_iff₀ hlogpos).mpr (by linarith only [hlogC])
    have hbudget := deletionCountError_budget epsilon C hepsilon0 hC.le n (upperEdgeCount epsilon n) t
      (by omega) le_rfl hMvalid ht
    exact deletionStepGood_of_kahnLayerInput_sharp_initial
      (q := 1 / 1000) (c := (thresholdTransferFactor a)^3) (bStop := 1 / 2)
      (e₀ := coordinateVertexAllowance n) (by omega) htK
      (thresholdUpperSpreadFactor_pos a).le (pow_pos (thresholdTransferFactor_pos a ha) 3)
      (coordinateExceptionFraction_lt a ha ha1) (thresholdTransferFactor_pos a ha).le
      (thresholdTransferFactor_le_one a ha ha1) hround.1 hexn.1 hexn.2.1 hexn.2.2 le_rfl
      e hgood hCb (by norm_num) hstopped hbudget hinput
  · intro t ht
    let M := (allEdges n).card - t
    have htK : t ≤ (allEdges n).card := ht.trans (Nat.sub_le _ _)
    have hMlower : upperEdgeCount epsilon n ≤ M := by dsimp only [M]; omega
    let P : Finset (Edge n) → Prop := fun H ↦ StandardAggregateLayerRegular n M a H ∧
      ¬ KahnLayerInput n (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M)
        (standardCodegreeCap n M) (coordinatePairCutoff n a) (coordinateTailFloor n M a)
        (coordinateResidualAllowance n (coordinateExceptionFraction a)) (coordinateVertexAllowance n)
        (deletionCountError n C) (thresholdUpperSpreadFactor a) (coordinateExceptionFraction a)
        (thresholdTransferFactor a) H
    have heq : finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
        (fun e ↦ standardDeletionBase a n t e ∧ ¬ standardDeletionStructural epsilon a n t e) =
        finsetProbability (sample n M) P := by
      calc
        _ = finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
            (fun e ↦ P (historyState e t le_rfl)) := by
          apply finsetProbability_congr_event
          intro e he
          simp only [standardDeletionBase, standardDeletionStructural, ht, true_and, P, M, C]
        _ = _ := (finsetProbability_decidable_irrel _ _ _ _).trans
          ((historyState_probability_eq_sample_at_time htK P).trans
            (finsetProbability_decidable_irrel _ _ _ _))
    rw [heq]
    exact add_le_add (hstopn t ht) (hstructn M hMlower (Nat.sub_le _ _))

lemma upper_pmProbability_tendsto_one_of_le_one (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    Tendsto (fun n ↦ pmProbability n (upperEdgeCount epsilon n)) atTop (𝓝 1) := by
  obtain ⟨a, ha, ha1, hpath⟩ :=
    exists_upper_standardAggregateLayer_path_factor_tendsto_zero epsilon hepsilon0 hepsilon1
  apply pmProbability_tendsto_one_of_eventually_split_bootstrap_level_bound
    (fun n ↦ upperEdgeCount epsilon n) (fun _ ↦ thresholdControlledWeightFactor a)
    deletionDeviationScale levelFailureBound (standardDeletionBase a) (standardDeletionStructural epsilon a)
    (eventually_standard_deletion_valid epsilon a hepsilon0.le hepsilon1 ha ha1)
  · exact hpath
  · exact deletion_levels_failure_bound_tendsto_zero (fun n ↦ upperEdgeCount epsilon n)

end

end Erdos747
