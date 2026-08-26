import ErdosProblems.Erdos747.StandardStructuralConstants

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The three structural errors are now controlled for the actual
supercritical parameters, uniformly over every remaining-edge layer. -/
lemma eventually_standard_structural_failure_probability_le
    (epsilon a : ℝ) (C : ℕ → ℝ)
    (hepsilon : 0 ≤ epsilon) (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ n in atTop, 0 ≤ C n) :
    ∀ᶠ n in atTop, ∀ M : ℕ, upperEdgeCount epsilon n ≤ M → M ≤ (allEdges n).card →
      finsetProbability (sample n M)
          (fun H ↦ StandardAggregateLayerRegular n M a H ∧
            ¬ KahnLayerInput n (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M)
              (standardCodegreeCap n M) (coordinatePairCutoff n a) (coordinateTailFloor n M a)
              (coordinateResidualAllowance n (coordinateExceptionFraction a)) (coordinateVertexAllowance n)
              (C n) (thresholdUpperSpreadFactor a) (coordinateExceptionFraction a) (thresholdTransferFactor a) H) ≤
        structuralFailureBound n := by
  let c := thresholdTransferFactor a
  let zeta := coordinateExceptionFraction a
  have hc : 0 < c := thresholdTransferFactor_pos a ha
  have hc1 : c ≤ 1 := thresholdTransferFactor_le_one a ha ha1
  have hzeta : 0 < zeta := coordinateExceptionFraction_pos a ha
  have hinherit := eventually_standardAggregateLayer_insertion_and_residual epsilon a c C hepsilon ha hc hC
  have hupper := eventually_standard_upper_spreading_failure_le epsilon zeta 41 C
    hepsilon hzeta (by norm_num) hC hC0
  have hresidual := eventually_standard_highResidual_spreading_failure_le epsilon a c zeta 41 C
    hepsilon hc hc1 hzeta (by norm_num) hC hC0
  have hlarge := (log_vertexCount_tendsto_atTop.const_mul_atTop ha).eventually_ge_atTop 8
  filter_upwards [hinherit, hupper, hresidual, hlarge,
    log_vertexCount_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop 200]
    with n hinheritn huppern hresidualn hlargen hlog hn
  intro M hM hMtop
  have hmean := supercritical_mean_lower epsilon hepsilon n M (by omega) hM
  have hmean1 := hlog.trans hmean
  have hlargeM : 8 ≤ a * ((M : ℝ) / n) := hlargen.trans (mul_le_mul_of_nonneg_left hmean ha.le)
  have hM0 : 0 < M := by
    by_contra hbad
    have hz : M = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div] at hmean1
    norm_num at hmean1
  have hround := coordinate_degree_rounding_bounds n M a ha hlargeM
  have hJpos := (coordinate_residual_layer_mean_lower n M (M - 3 * coordinateDegreeCeil n M)
    hn hmean1 le_rfl).1
  let P₁ : Finset (Edge n) → Prop := fun H ↦
    KahnAggregateInsertionGood n M (standardCodegreeCap n M) (C n)
      (aggregateDegreeTolerance n) (aggregateDegreeTolerance n) 32 H ∧
      ¬ GlobalUpperWeightSpread n H (thresholdUpperSpreadFactor a) zeta
  let P₂ : Finset (Edge n) → Prop := fun H ↦
    ResidualAggregateInheritanceGood n M (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M)
      (standardCodegreeCap n M) c (C n) (residualCountError n (C n) c)
      (standardResidualDegreeTolerance n) (2 * aggregateDegreeTolerance n) 64 H ∧
      ¬ HighResidualLowerSpread n H c (thresholdResidualSpreadFactor a) zeta
  let P₃ := SomeAdaptiveCoordinateTailFailure n c (coordinateDegreeFloor n M a)
    (coordinateDegreeCeil n M) (coordinatePairCutoff n a) (coordinateTailFloor n M a) (coordinateVertexAllowance n)
  have hprob1 : finsetProbability (sample n M) P₁ ≤ 4 * Real.exp (-41 * Real.log ((3 * n : ℕ) : ℝ)) :=
    huppern M hM
  have hprob2 : finsetProbability (sample n M) P₂ ≤
      (allEdges n).card * (4 * Real.exp (-41 * Real.log ((3 * (n - 1) : ℕ) : ℝ))) :=
    hresidualn M hM hMtop
  have hprob3 : finsetProbability (sample n M) P₃ ≤
      (3 : ℝ) * (allEdges n).card * ((3 * n : ℕ) : ℝ) *
        Real.exp (-32 * Real.log ((3 * n : ℕ) : ℝ)) := by
    apply (coordinate_parameter_failure_probability_le n M a c (by omega) ha ha1 hMtop hmean1 hlargeM).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith only [hmean]
  have hevent : ∀ H ∈ sample n M, StandardAggregateLayerRegular n M a H →
      ¬ KahnLayerInput n (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M)
        (standardCodegreeCap n M) (coordinatePairCutoff n a) (coordinateTailFloor n M a)
        (coordinateResidualAllowance n zeta) (coordinateVertexAllowance n)
        (C n) (thresholdUpperSpreadFactor a) zeta c H → P₁ H ∨ P₂ H ∨ P₃ H := by
    intro H hHs hbase hnot
    unfold KahnLayerInput at hnot
    push Not at hnot
    rcases hnot with ⟨hcount, hnot⟩
    obtain ⟨hgood, hres⟩ := hinheritn M hM H hHs hbase hcount
    by_cases hUp : GlobalUpperWeightSpread n H (thresholdUpperSpreadFactor a) zeta
    · by_cases hRes : HighResidualLowerSpread n H c (thresholdResidualSpreadFactor a) zeta
      · by_cases hTail : P₃ H
        · exact Or.inr (Or.inr hTail)
        · have hcoord : CoordinateTransferRegularAwayAboveMax n H c
              (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M) (standardCodegreeCap n M)
              (coordinatePairCutoff n a) (coordinateTailFloor n M a)
              (coordinateResidualAllowance n zeta) (coordinateVertexAllowance n) := by
            apply coordinateTransferRegularAwayAboveMax_of_residualAggregate
              (by omega : 2 ≤ n) hM0 hHs hres hround.1 hJpos hRes
            · intro Z hZ
              have hJle : (reindexGraphAway H Z hZ).card ≤ M :=
                (card_reindexGraphAway_le_card H hZ).trans_eq (mem_sample.mp hHs).2
              exact coordinate_transfer_cutoff_budget n M _ a (thresholdResidualSpreadFactor a)
                (by omega) ha (thresholdResidualSpreadFactor_pos a).le hJle hlargeM
            · exact Nat.le_ceil (zeta * (allEdges (n - 1)).card)
            · exact coordinate_tail_bounds_of_not_failure hTail
          exact False.elim (hnot hUp hcoord)
      · exact Or.inr (Or.inl ⟨hres, hRes⟩)
    · exact Or.inl ⟨hgood, hUp⟩
  calc
    _ ≤ finsetProbability (sample n M) (fun H ↦ P₁ H ∨ P₂ H ∨ P₃ H) := by
      apply finsetProbability_mono_event
      intro H hHs hbad
      exact hevent H hHs hbad.1 hbad.2
    _ ≤ finsetProbability (sample n M) P₁ +
        (finsetProbability (sample n M) P₂ + finsetProbability (sample n M) P₃) :=
      (finsetProbability_or_le_add _ _ _).trans
        (add_le_add le_rfl (finsetProbability_or_le_add _ _ _))
    _ ≤ structuralFailureBound n := add_le_add hprob1 (add_le_add hprob2 hprob3)

end

end Erdos747
