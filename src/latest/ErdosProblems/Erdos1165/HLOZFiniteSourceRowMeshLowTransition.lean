/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFiniteSourceRowTransitionFactors
import ErdosProblems.Erdos1165.HLOZNoLazyInitialBudgetMixedTransitionFactors

/-!
# Finite source-row Proposition 4.9 mesh factors

This module applies the finite-row union construction to literal
fixed-first-strip mesh data.  Each row retains its own candidate family and
mesh-boundary future factor.  The only aggregate quantitative datum is the
sum of the conditional candidate ratios.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZFiniteSourceRowMeshLowTransition

open HLOZFiniteSourceRowTransitionFactors
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPathEvents HLOZProposition48Candidates

noncomputable section

/-- Literal Proposition 4.9 data for a finite family of possibly overlapping
source rows.

The row events cover `next`, but are not required to be disjoint.  Each row
may use its own local-CLT constant; `ratio_sum_le` is the deterministic finite
union bookkeeping against one final polynomial envelope. -/
structure FiniteSourceRowMeshLowCoordinateData
    (Row : Type) [Fintype Row]
    (C : ℝ) (m rank : ℕ) (a : GapScale)
    (previous next : Set WalkPath) where
  rowNext : Row → Set WalkPath
  rowNext_measurable : ∀ row, MeasurableSet (rowNext row)
  next_subset : next ⊆ ⋃ row, rowNext row
  rowConstant : Row → ℝ
  row : ∀ source,
    FirstStripMeshLowCoordinateData (rowConstant source) m rank a
      previous (rowNext source)
  ratio_sum_le :
    ∑ source, (row source).candidateRatio ≤
      prop49CandidateRatioEnvelope C m a

namespace FiniteSourceRowMeshLowCoordinateData

/-- Before polynomial absorption, one row has exactly its literal product
cost. -/
noncomputable def rowTransitionData
    {Row : Type} [Fintype Row]
    {C : ℝ} {m rank : ℕ} {a : GapScale}
    {previous next : Set WalkPath}
    (data : FiniteSourceRowMeshLowCoordinateData
      Row C m rank a previous next)
    (hm : 1 ≤ m) (source : Row) :
    FirstStripLowTransitionData m previous (data.rowNext source)
      ((initialBudget48 m : ℝ≥0∞) *
        (data.row source).candidateRatio * meshEscapeCost m a) := by
  let row := data.row source
  letI := row.history_countable
  letI := row.index_countable
  exact FirstStripLowTransitionData.ofMeshCreation hm row.candidate
    row.creation le_rfl

/-- Apply the common polynomial envelope after summing the literal row
ratios.  This is the honest low factor for overlapping canonical/opposite
source histories. -/
noncomputable def transitionFactor
    {Row : Type} [Fintype Row]
    {C : ℝ} {m rank : ℕ} {a : GapScale}
    {previous next : Set WalkPath}
    (data : FiniteSourceRowMeshLowCoordinateData
      Row C m rank a previous next)
    (hm : 1 ≤ m)
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope C m a * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    HeterogeneousFiniteSourceRowTransitionFactor previous next
      (UpperCanonical.hlozTransitionCost 1 m) :=
  .ofRows
    { rowNext := data.rowNext
      rowCost := fun source ↦
        (initialBudget48 m : ℝ≥0∞) *
          (data.row source).candidateRatio * meshEscapeCost m a
      rowNext_measurable := data.rowNext_measurable
      next_subset := data.next_subset
      rowFactor := fun source ↦ (data.rowTransitionData hm source).factor
      cost_sum_le := by
        calc
          ∑ source, (initialBudget48 m : ℝ≥0∞) *
              (data.row source).candidateRatio * meshEscapeCost m a =
              (initialBudget48 m : ℝ≥0∞) *
                (∑ source, (data.row source).candidateRatio) *
                  meshEscapeCost m a := by
            rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ (initialBudget48 m : ℝ≥0∞) *
                prop49CandidateRatioEnvelope C m a *
                  meshEscapeCost m a := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left data.ratio_sum_le bot_le) bot_le
          _ ≤ UpperCanonical.hlozTransitionCost 1 m := hnumeric }

end FiniteSourceRowMeshLowCoordinateData

end

end Erdos1165.HLOZFiniteSourceRowMeshLowTransition
