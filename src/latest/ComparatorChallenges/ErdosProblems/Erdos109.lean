/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Function Set
open scoped ENNReal NNReal Pointwise Topology
open MeasureTheory ProbabilityTheory
open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology
open Filter Finset MeasureTheory Set
open scoped ENNReal Topology
open Filter Finset Function MeasureTheory Set
open Filter Finset Function Set
open scoped Pointwise Topology
open Filter MeasureTheory Set
open scoped ENNReal ProbabilityTheory Topology
open Filter Function MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Set

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

open scoped Classical in
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos109

open scoped Classical in
theorem erdos_109 (A : Set ℕ) (hA : A.upperDensity > 0) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  sorry

end Erdos109

end
