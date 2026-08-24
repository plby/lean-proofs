/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1071

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

end Erdos1071

namespace Erdos1071b

abbrev Point := EuclideanSpace ℝ (Fin 2)
def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y
def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)
def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R
def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'
end Erdos1071b

namespace Erdos1071

theorem erdos_1071 : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Countable S ∧ Set.Infinite S := by
  sorry

end Erdos1071
namespace Erdos1071b

theorem erdos_1071_finite : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Finite S := by
  sorry

end Erdos1071b
