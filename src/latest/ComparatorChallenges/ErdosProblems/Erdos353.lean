/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Erdos353.Koizumi
import Erdos353.Cyclic
import Erdos353.Polygon

open MeasureTheory

namespace Erdos353

theorem erdos_353 :
    (∀ S : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet S → volume S = ⊤ →
      (∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ Koizumi.IsoTrapArea1 A B C D) ∧
      (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ Koizumi.IsoscelesTriangleArea1 A B C) ∧
      (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ Koizumi.RightTriangleArea1 A B C) ∧
      (∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ CyclicQuad.UnitCyclicQuad A B C D)) ∧
    (∃ S : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet S ∧ volume S = ⊤ ∧
      ∀ (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)), 3 ≤ n →
        (∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
          0 < Kovac.cross (C (i + 1) - C i) (C j - C i)) →
        (∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a) →
        (∀ i : ZMod n, C i ∈ S) → volume (convexHull ℝ (Set.range C)) < 1) := by
  sorry

end Erdos353
