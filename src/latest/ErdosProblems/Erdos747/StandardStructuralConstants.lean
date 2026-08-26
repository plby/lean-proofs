import ErdosProblems.Erdos747.StandardSpreadingBounds
import ErdosProblems.Erdos747.CoordinateTailBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

def thresholdUpperSpreadFactor (a : ℝ) : ℝ :=
  coarseUpperFactor (spreadThinningMultiplier (coordinateExceptionFraction a) 41)

def thresholdResidualSpreadFactor (a : ℝ) : ℝ :=
  coarseLowerFactor (spreadThinningMultiplier (coordinateExceptionFraction a) 41)

def thresholdTransferFactor (a : ℝ) : ℝ := a * thresholdResidualSpreadFactor a / 32

def thresholdControlledWeightFactor (a : ℝ) : ℝ :=
  thresholdUpperSpreadFactor a / (thresholdTransferFactor a)^3

def structuralFailureBound (n : ℕ) : ℝ :=
  4 * Real.exp (-41 * Real.log ((3 * n : ℕ) : ℝ)) +
    ((allEdges n).card * (4 * Real.exp (-41 * Real.log ((3 * (n - 1) : ℕ) : ℝ))) +
      (3 : ℝ) * (allEdges n).card * ((3 * n : ℕ) : ℝ) *
        Real.exp (-32 * Real.log ((3 * n : ℕ) : ℝ)))

lemma thresholdResidualSpreadFactor_pos (a : ℝ) : 0 < thresholdResidualSpreadFactor a := by
  unfold thresholdResidualSpreadFactor coarseLowerFactor
  exact half_pos (coarseSurvivalFraction_pos _)

lemma thresholdUpperSpreadFactor_pos (a : ℝ) : 0 < thresholdUpperSpreadFactor a := by
  unfold thresholdUpperSpreadFactor coarseUpperFactor
  exact div_pos (by norm_num) (coarseSurvivalFraction_pos _)

lemma thresholdTransferFactor_pos (a : ℝ) (ha : 0 < a) : 0 < thresholdTransferFactor a :=
  div_pos (mul_pos ha (thresholdResidualSpreadFactor_pos a)) (by norm_num)

lemma thresholdTransferFactor_le_one (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    thresholdTransferFactor a ≤ 1 := by
  have hz := coordinateExceptionFraction_pos a ha
  have hT := spreadThinningMultiplier_pos (coordinateExceptionFraction a) 41 hz (by norm_num)
  have hr := coarseSurvivalFraction_le_one _ hT.le
  have hLR : thresholdResidualSpreadFactor a ≤ 1 / 2 := by
    unfold thresholdResidualSpreadFactor coarseLowerFactor
    linarith only [hr]
  have hprod := mul_le_mul ha1 hLR (thresholdResidualSpreadFactor_pos a).le (by norm_num : (0 : ℝ) ≤ 1)
  unfold thresholdTransferFactor
  linarith only [hprod]

lemma thresholdControlledWeightFactor_pos (a : ℝ) (ha : 0 < a) :
    0 < thresholdControlledWeightFactor a :=
  div_pos (thresholdUpperSpreadFactor_pos a) (pow_pos (thresholdTransferFactor_pos a ha) 3)

lemma structuralFailureBound_nonneg (n : ℕ) : 0 ≤ structuralFailureBound n := by
  unfold structuralFailureBound
  positivity

lemma coordinate_tail_bounds_of_not_failure
    {n d D Q b e : ℕ} {c : ℝ} {H : Finset (Edge n)}
    (hnot : ¬ SomeAdaptiveCoordinateTailFailure n c d D Q b e H) :
    ∀ Z ∈ allEdges n, ∀ x ∈ Z,
      (coordinateLinkTailVertices Z x (residualTransferCutoff Z c d b (inducedAway H Z))
        d D Q (b + 1) H).card ≤ e := by
  intro Z hZ x hx
  by_contra hbad
  apply hnot
  refine ⟨⟨x, Z⟩, ?_, ?_⟩
  · rw [matchingIncidentPairs, Finset.mem_sigma]
    exact ⟨Finset.mem_univ x, Finset.mem_filter.mpr ⟨hZ, hx⟩⟩
  · rw [adaptiveCoordinateLinkTailVertices_eq]
    exact_mod_cast (show e + 1 ≤ (coordinateLinkTailVertices Z x
      (residualTransferCutoff Z c d b (inducedAway H Z)) d D Q (b + 1) H).card by omega)

end

end Erdos747
