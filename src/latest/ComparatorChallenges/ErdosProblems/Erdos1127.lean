/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Cardinal

noncomputable section


namespace Erdos1127

open scoped Classical in
def HasDistinctOrientedPairDistances {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    x ≠ y → u ≠ v →
    dist x y = dist u v →
    x = u ∧ y = v

end Erdos1127

namespace Erdos1127

open scoped Classical in
def HasDistinctIncludingDegeneratePairs {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    dist x y = dist u v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

end Erdos1127

namespace Erdos1127

open scoped Classical in
def ContinuumHypothesis : Prop :=
  𝔠 = (ℵ_ 1 : Cardinal.{0})

end Erdos1127

namespace Erdos1127

open scoped Classical in
def HasDistinctPairDistances {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    x ≠ y → u ≠ v →
    dist x y = dist u v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

end Erdos1127

namespace Erdos1127

open scoped Classical in
def PositiveAnswer : Prop :=
  ∀ n : ℕ, ∃ color : EuclideanSpace ℝ (Fin n) → ℕ,
    HasDistinctPairDistances color

/-! ## The two algebraic obstructions

For a monochromatic set, two different nondegenerate unordered pairs with the same distance
have either three or four vertices.  The three-vertex case is an isosceles triangle (the zero
set of Schmerl's polynomial `P₃`), and the four-vertex case consists of two disjoint pairs (the
zero set of `P₄`).  The following definitions use distances rather than squared distances, which
is equivalent over `ℝ` and makes the final combinatorial reduction independent of coordinates.
-/

end Erdos1127

namespace Erdos1127

open scoped Classical in
theorem erdos_1127_oriented_pair_formulation_false :
    ¬ ∃ color : ℝ → ℕ, HasDistinctOrientedPairDistances color := by
  sorry

end Erdos1127

namespace Erdos1127

open scoped Classical in
theorem erdos_1127_degenerate_pair_formulation_false :
    ¬ ∃ color : ℝ → ℕ, HasDistinctIncludingDegeneratePairs color := by
  sorry

end Erdos1127

namespace Erdos1127

open scoped Classical in
theorem erdos_1127 : ContinuumHypothesis ↔ PositiveAnswer := by
  sorry

end Erdos1127

end
