/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZFiniteSourceRowMeshLowTransition

/-!
# Finite Proposition 4.9 rows with row-dependent pasts

Checker-opposite source rows are naturally expressed after one-step
recentering.  Their literal past is therefore not definitionally the same as
the physical structural past, although its probability is no larger.  This
module records exactly that harmless variation and derives the same finite
row estimate.  No probability estimate is stored for a next event.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZVariablePastFiniteSourceRowMeshLowTransition

open HLOZFiniteSourceRowMeshLowTransition
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPathEvents HLOZProposition48Candidates

noncomputable section

/-- A finite family of low-coordinate rows whose literal previous events may
differ, but whose masses are all bounded by one common physical past. -/
structure VariablePastFiniteSourceRowMeshLowCoordinateData
    (Row : Type) [Fintype Row]
    (C : ℝ) (m rank : ℕ) (a : GapScale)
    (commonPrevious next : Set WalkPath) where
  rowPrevious : Row → Set WalkPath
  rowPrevious_measurable : ∀ row, MeasurableSet (rowPrevious row)
  rowPrevious_measure_le : ∀ row,
    simpleRandomWalk (rowPrevious row) ≤ simpleRandomWalk commonPrevious
  rowNext : Row → Set WalkPath
  rowNext_measurable : ∀ row, MeasurableSet (rowNext row)
  next_subset : next ⊆ ⋃ row, rowNext row
  rowConstant : Row → ℝ
  row : ∀ source,
    FirstStripMeshLowCoordinateData (rowConstant source) m rank a
      (rowPrevious source) (rowNext source)
  ratio_sum_le :
    ∑ source, (row source).candidateRatio ≤
      prop49CandidateRatioEnvelope C m a

namespace VariablePastFiniteSourceRowMeshLowCoordinateData

/-- Summing the rowwise stopped-product estimates and then comparing every
row past with the common physical past gives the usual polynomial bound. -/
theorem measure_next_le
    {Row : Type} [Fintype Row]
    {C : ℝ} {m rank : ℕ} {a : GapScale}
    {commonPrevious next : Set WalkPath}
    (data : VariablePastFiniteSourceRowMeshLowCoordinateData
      Row C m rank a commonPrevious next)
    (hm : 1 ≤ m)
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope C m a * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk next ≤
      UpperCanonical.hlozTransitionCost 1 m *
        simpleRandomWalk commonPrevious := by
  calc
    simpleRandomWalk next ≤
        simpleRandomWalk (⋃ row, data.rowNext row) :=
      measure_mono data.next_subset
    _ ≤ ∑' row, simpleRandomWalk (data.rowNext row) := measure_iUnion_le _
    _ ≤ ∑' row,
        ((initialBudget48 m : ℝ≥0∞) *
          (data.row row).candidateRatio * meshEscapeCost m a) *
            simpleRandomWalk (data.rowPrevious row) := by
      apply ENNReal.tsum_le_tsum
      intro row
      let rowData := data.row row
      let := rowData.history_countable
      let := rowData.index_countable
      exact (FirstStripLowTransitionData.ofMeshCreation hm rowData.candidate
        rowData.creation le_rfl).factor.measure_next_le
          (data.rowPrevious_measurable row) (data.rowNext_measurable row)
    _ ≤ ∑' row,
        ((initialBudget48 m : ℝ≥0∞) *
          (data.row row).candidateRatio * meshEscapeCost m a) *
            simpleRandomWalk commonPrevious := by
      apply ENNReal.tsum_le_tsum
      intro row
      exact mul_le_mul_of_nonneg_left (data.rowPrevious_measure_le row) bot_le
    _ = ((initialBudget48 m : ℝ≥0∞) *
          (∑ row, (data.row row).candidateRatio) * meshEscapeCost m a) *
            simpleRandomWalk commonPrevious := by
      simp only [tsum_fintype]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    _ ≤ ((initialBudget48 m : ℝ≥0∞) *
          prop49CandidateRatioEnvelope C m a * meshEscapeCost m a) *
            simpleRandomWalk commonPrevious := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left data.ratio_sum_le bot_le) bot_le) bot_le
    _ ≤ UpperCanonical.hlozTransitionCost 1 m *
          simpleRandomWalk commonPrevious := by
      exact mul_le_mul_of_nonneg_right hnumeric bot_le

end VariablePastFiniteSourceRowMeshLowCoordinateData

end

end Erdos1165.HLOZVariablePastFiniteSourceRowMeshLowTransition
