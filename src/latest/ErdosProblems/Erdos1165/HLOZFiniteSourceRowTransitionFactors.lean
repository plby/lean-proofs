/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyHeterogeneousTransitionFactors

/-!
# Finite source-row transition factors

The canonical and transported opposite-source rows in HLOZ Proposition 4.9
need not be disjoint as stopped histories.  The source argument uses a finite
union bound over those rows, not a joint candidate atom.  This module packages
that literal construction.

Every row contains a source-correct stopped-coordinate/strong-Markov factor.
The aggregate stores only a finite event cover and a deterministic sum-of-costs
comparison.  In particular, no transition probability inequality is a field.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZFiniteSourceRowTransitionFactors

open HLOZNoLazyHeterogeneousTransitionFactors HLOZPathEvents

noncomputable section

/-- A finite, possibly overlapping family of source-row transition factors.

All rows start from the same `previous` event.  Their stopped histories may
overlap; only their next-event union is used. -/
structure FiniteSourceRowTransitionFactor
    (Row : Type) [Fintype Row]
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  rowNext : Row → Set WalkPath
  rowCost : Row → ℝ≥0∞
  rowNext_measurable : ∀ row, MeasurableSet (rowNext row)
  next_subset : next ⊆ ⋃ row, rowNext row
  rowFactor : ∀ row,
    HeterogeneousSourceCorrectTransitionFactor
      previous (rowNext row) (rowCost row)
  cost_sum_le : ∑ row, rowCost row ≤ q

namespace FiniteSourceRowTransitionFactor

/-- Finite subadditivity and the rowwise source-correct factors derive the
aggregate relative transition estimate. -/
theorem measure_next_le
    {Row : Type} [Fintype Row]
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (factor : FiniteSourceRowTransitionFactor Row previous next q)
    (hprevious : MeasurableSet previous) :
    simpleRandomWalk next ≤ q * simpleRandomWalk previous := by
  calc
    simpleRandomWalk next ≤
        simpleRandomWalk (⋃ row, factor.rowNext row) :=
      measure_mono factor.next_subset
    _ ≤ ∑' row, simpleRandomWalk (factor.rowNext row) :=
      measure_iUnion_le _
    _ ≤ ∑' row, factor.rowCost row * simpleRandomWalk previous := by
      exact ENNReal.tsum_le_tsum fun row ↦
        (factor.rowFactor row).measure_next_le hprevious
          (factor.rowNext_measurable row)
    _ = (∑' row, factor.rowCost row) * simpleRandomWalk previous := by
      rw [ENNReal.tsum_mul_right]
    _ = (∑ row, factor.rowCost row) * simpleRandomWalk previous := by
      simp
    _ ≤ q * simpleRandomWalk previous := by
      calc
        (∑ row, factor.rowCost row) * simpleRandomWalk previous =
            simpleRandomWalk previous * ∑ row, factor.rowCost row :=
          mul_comm _ _
        _ ≤ simpleRandomWalk previous * q :=
          mul_le_mul_right factor.cost_sum_le _
        _ = q * simpleRandomWalk previous := mul_comm _ _

/-- A single source-correct factor is the one-row special case. -/
noncomputable def singleton
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (hnext : MeasurableSet next)
    (factor : HeterogeneousSourceCorrectTransitionFactor previous next q) :
    FiniteSourceRowTransitionFactor (Fin 1) previous next q where
  rowNext := fun _ ↦ next
  rowCost := fun _ ↦ q
  rowNext_measurable := fun _ ↦ hnext
  next_subset := by
    intro s hs
    exact mem_iUnion_of_mem (0 : Fin 1) hs
  rowFactor := fun _ ↦ factor
  cost_sum_le := by simp

end FiniteSourceRowTransitionFactor

/-- A finite row factor with its finite source-row carrier hidden.  This is
the common target of the all-high singleton branch and the genuine
multi-source low branch. -/
structure HeterogeneousFiniteSourceRowTransitionFactor
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  Row : Type
  [row_fintype : Fintype Row]
  factor : FiniteSourceRowTransitionFactor Row previous next q

namespace HeterogeneousFiniteSourceRowTransitionFactor

/-- Hide the concrete finite source-row type. -/
def ofRows
    {Row : Type} [Fintype Row]
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (factor : FiniteSourceRowTransitionFactor Row previous next q) :
    HeterogeneousFiniteSourceRowTransitionFactor previous next q where
  Row := Row
  factor := factor

/-- Regard one high- or low-source factor as a one-row aggregate. -/
noncomputable def ofFactor
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (hnext : MeasurableSet next)
    (factor : HeterogeneousSourceCorrectTransitionFactor previous next q) :
    HeterogeneousFiniteSourceRowTransitionFactor previous next q :=
  .ofRows (.singleton hnext factor)

/-- Forget the private finite row carrier and derive the relative estimate. -/
theorem measure_next_le
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (factor : HeterogeneousFiniteSourceRowTransitionFactor previous next q)
    (hprevious : MeasurableSet previous) :
    simpleRandomWalk next ≤ q * simpleRandomWalk previous := by
  let _ := factor.row_fintype
  exact factor.factor.measure_next_le hprevious

end HeterogeneousFiniteSourceRowTransitionFactor

/-- Three successive no-lazy transition factors, each of which may be a
finite overlapping union of source rows. -/
structure FiniteSourceRowFilteredBranchPackage
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent)
    (K : ℝ≥0) (t : Tilings.Tiling) (m : ℕ)
    (a : HLOZFilteredTransitionAssembly.GapTriple) where
  stagedCandidate₁_measurable : MeasurableSet (stagedCandidate₁ t m a)
  stagedCandidate₂_measurable : MeasurableSet (stagedCandidate₂ t m a)
  stagedCandidate₃_measurable : MeasurableSet (stagedCandidate₃ t m a)
  firstPast : Set WalkPath
  firstPast_measurable : MeasurableSet firstPast
  firstFactor : HeterogeneousFiniteSourceRowTransitionFactor firstPast
    (HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
      stagedCandidate₁ t m a)
    (UpperCanonical.hlozTransitionCost K m)
  secondFactor : HeterogeneousFiniteSourceRowTransitionFactor
    (HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
      stagedCandidate₁ t m a)
    (HLOZNoLazyFilteredTransitions.filteredSecondTransitionEvent
      stagedCandidate₁ stagedCandidate₂ t m a)
    (UpperCanonical.hlozTransitionCost K m)
  thirdFactor : HeterogeneousFiniteSourceRowTransitionFactor
    (HLOZNoLazyFilteredTransitions.filteredSecondTransitionEvent
      stagedCandidate₁ stagedCandidate₂ t m a)
    (HLOZNoLazyFilteredTransitions.filteredThirdTransitionEvent
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a)
    (UpperCanonical.hlozTransitionCost K m)

namespace FiniteSourceRowFilteredBranchPackage

/-- The three transition estimates follow from the finite row certificates.
The first past has mass at most one because `simpleRandomWalk` is a
probability measure. -/
theorem measure_estimates
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ :
      HLOZFilteredTransitionAssembly.BranchEvent}
    {K : ℝ≥0} {t : Tilings.Tiling} {m : ℕ}
    {a : HLOZFilteredTransitionAssembly.GapTriple}
    (package : FiniteSourceRowFilteredBranchPackage
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a) :
    simpleRandomWalk
        (HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
          stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m ∧
      simpleRandomWalk
          (HLOZNoLazyFilteredTransitions.filteredSecondTransitionEvent
            stagedCandidate₁ stagedCandidate₂ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
                stagedCandidate₁ t m a) ∧
      simpleRandomWalk
          (HLOZNoLazyFilteredTransitions.filteredThirdTransitionEvent
            stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (HLOZNoLazyFilteredTransitions.filteredSecondTransitionEvent
                stagedCandidate₁ stagedCandidate₂ t m a) := by
  have hfirstMeas :=
    HLOZNoLazyFilteredTransitions.measurableSet_filteredFirstTransitionEvent
      stagedCandidate₁ t m a package.stagedCandidate₁_measurable
  have hsecondMeas :=
    HLOZNoLazyFilteredTransitions.measurableSet_filteredSecondTransitionEvent
      stagedCandidate₁ stagedCandidate₂ t m a
      package.stagedCandidate₁_measurable package.stagedCandidate₂_measurable
  have hfirst := package.firstFactor.measure_next_le
    package.firstPast_measurable
  have hsecond := package.secondFactor.measure_next_le hfirstMeas
  have hthird := package.thirdFactor.measure_next_le hsecondMeas
  have hfirstPastMass : simpleRandomWalk package.firstPast ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ package.firstPast)
  refine ⟨?_, hsecond, hthird⟩
  calc
    simpleRandomWalk
        (HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
          stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk package.firstPast := hfirst
    _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
      exact mul_le_mul_right hfirstPastMass _
    _ = UpperCanonical.hlozTransitionCost K m := mul_one _

end FiniteSourceRowFilteredBranchPackage

end

end Erdos1165.HLOZFiniteSourceRowTransitionFactors
