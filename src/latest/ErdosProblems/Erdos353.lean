/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0 and corrected geometric statements. -/
/-
Erdős Problem 353.
Informal authors: Junnosuke Koizumi, Vjekoslav Kovač, Bruno Predojević.
Formal authors: Aristotle, JoshuaB.
Original Lean/Mathlib version: 4.28.0.
Sources: https://www.erdosproblems.com/forum/thread/353#post-7085
https://www.erdosproblems.com/forum/thread/353#post-7095
https://www.erdosproblems.com/forum/thread/353#post-7098
Exact editor URLs are preserved in data/urls.yaml.
-/
import ErdosProblems.Erdos353.Koizumi
import ErdosProblems.Erdos353.Cyclic
import ErdosProblems.Erdos353.Polygon

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
  refine ⟨?_, Kovac.thm_congruent⟩
  intro S hS hvol
  have hpos : 0 < volume S := by rw [hvol]; exact ENNReal.zero_lt_top
  have hunb : ¬ Bornology.IsBounded S := by
    intro h
    have hfinite := h.measure_lt_top (μ := volume)
    rw [hvol] at hfinite
    exact (lt_irrefl ⊤) hfinite
  obtain ⟨hiso, hright⟩ := Koizumi.thm_iso_right S hS hpos hunb
  exact ⟨Koizumi.thm_trapezoid S hS hvol, hiso, hright,
    CyclicQuad.exists_unitCyclicQuad_of_volume_infinite S hS hvol⟩

#print axioms erdos_353
-- 'Erdos353.erdos_353' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos353
