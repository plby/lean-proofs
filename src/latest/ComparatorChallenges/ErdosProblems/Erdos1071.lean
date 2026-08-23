/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1071

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

set_option maxHeartbeats 50000000
open scoped Classical in
abbrev Point := EuclideanSpace ℝ (Fin 2)
open scoped Classical in
def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y
open scoped Classical in
def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)
open scoped Classical in
def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R
open scoped Classical in
def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'
open scoped Classical in
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

set_option maxHeartbeats 50000000
open scoped Classical in
abbrev Point := EuclideanSpace ℝ (Fin 2)
open scoped Classical in
def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y
open scoped Classical in
def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)
open scoped Classical in
def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R
open scoped Classical in
def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}
open Set

open Set

open Set

open Set

open Set

open Set

open Set

open Set

open scoped Classical in
def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'
end Erdos1071b

open Set

namespace Erdos1071

open scoped Classical in
theorem Corollary_3 : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Countable S ∧ Set.Infinite S := by
  sorry

end Erdos1071
namespace Erdos1071b

open scoped Classical in
theorem erdos_1071b : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Finite S := by
  sorry

end Erdos1071b
