import Wikipedia.HopfProblem.SpecialPeriodsThreefoldStar
import Wikipedia.HopfProblem.ThreefoldGluingManifold

/-!
# Holomorphic transitions for star gluing

For native complex charts on all the pieces, holomorphy of the given
filling-to-regular overlaps and their inverses implies holomorphy of
every constructed transition.  The diagonal transitions are identities;
transitions between distinct filling pieces have empty source.

No piece is required to be inhabited, and no finiteness hypothesis on
the collection of filling pieces is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff

universe u

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Star.Input

variable {B I : Type u} [TopologicalSpace B] (D : Input B I)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [∀ i, ChartedSpace E (D.piece i)]
    (hhol : ∀ i, ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (D.overlap i) (D.overlap i).source)
    (hinv : ∀ i, ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (D.overlap i).symm (D.overlap i).target)

include hhol hinv

/-- Holomorphy of the supplied overlaps and their inverses implies
holomorphy of every transition in the actual star construction. -/
theorem transition_holomorphic (i j : Option I) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (D.transition i j) (D.transition i j).source := by
  cases i with
  | none =>
      cases j with
      | none =>
          rw [D.transition_none_none]
          change ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
            (id : D.piece none → D.piece none) univ
          exact contMDiffOn_id
      | some j =>
          rw [D.transition_none_some]
          simpa only [OpenPartialHomeomorph.symm_source] using hinv j
  | some i =>
      cases j with
      | none =>
          rw [D.transition_some_none]
          exact hhol i
      | some j =>
          by_cases h : i = j
          · subst j
            rw [D.transition_some_self]
            change ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
              (id : D.piece (some i) → D.piece (some i)) univ
            exact contMDiffOn_id
          · rw [D.transition_some_some_source_eq_empty h]
            exact contMDiffOn_empty

/-- The constructed gluing data satisfy the native holomorphic transition
hypothesis used by `ThreefoldGluing.Data.isManifold`. -/
theorem toData_transition_holomorphic (i j : D.toData.J) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (D.toData.transition i j) (D.toData.transition i j).source := by
  change ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
    (D.transition i j) (D.transition i j).source
  exact D.transition_holomorphic hhol hinv i j

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Star.Input
