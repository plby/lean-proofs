import Wikipedia.SmoothSixDPoincare.NativeWhitneyCancellation

/-!
# Three/three Whitney cancellation fixes every surviving intersection germ

The actual compatible chart contains precisely the two chosen crossings.
The compact support of its constructed ambient isotopy is therefore disjoint
from every other original intersection. Both original whole sheets remain
the sheets used in the exact intersection-removal formula.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}

theorem exists_three_sheet_relative_cancellation
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) S k.map)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ tube.chart.target ∧
      Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧ ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
        (∀ y, A (0, y) = y) ∧
        (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
        (∀ t y, y ∉ K → A (t, y) = y) ∧
        ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_compatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKt, A, hA⟩ := c.exists_cancellation
  refine ⟨K, hK, hKt.trans c.target_subset, ?_, A, hA⟩
  apply Set.disjoint_left.mpr
  intro y hyK hy
  have hc : y ∈ (S ∩ T) ∩ c.chart.target := ⟨hy.1, hKt hyK⟩
  rw [c.intersection_in_target_eq] at hc
  exact hy.2 hc

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
