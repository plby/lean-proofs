import Mathlib.Order.CompletePartialOrder
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1071

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
abbrev Point := EuclideanSpace ℝ (Fin 2)
def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y
def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)
def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R
def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'
def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}
open Set

end Erdos1071

namespace Erdos1071b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
abbrev Point := EuclideanSpace ℝ (Fin 2)
def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y
def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)
def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R
def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}
open Set

open Set

open Set

open Set

open Set

open Set

open Set

open Set

def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'
end Erdos1071b

attribute [local instance] Classical.propDecidable

theorem Erdos1071.Corollary_3 :
    @Exists.{1} (Set.{0} (Set.{0} Erdos1071.Point)) fun (S : Set.{0} (Set.{0} Erdos1071.Point)) ↦
      And (Erdos1071.IsMaximalDisjointCollection S Erdos1071.UnitSquare)
        (And (@Set.Countable.{0} (Set.{0} Erdos1071.Point) S)
          (@Set.Infinite.{0} (Set.{0} Erdos1071.Point) S))
  := by
  sorry
theorem Erdos1071b.erdos_1071b :
    @Exists.{1} (Set.{0} (Set.{0} Erdos1071b.Point)) fun (S : Set.{0} (Set.{0} Erdos1071b.Point)) ↦
      And (Erdos1071b.IsMaximalDisjointCollection S Erdos1071b.UnitSquare)
        (@Set.Finite.{0} (Set.{0} Erdos1071b.Point) S)
  := by
  sorry
