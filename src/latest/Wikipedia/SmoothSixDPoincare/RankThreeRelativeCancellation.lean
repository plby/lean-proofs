import Wikipedia.SmoothSixDPoincare.RankThreeNativeCancellation

/-!
# Whitney cancellation supported away from every surviving intersection

The compatible chart contains exactly the two selected original crossings.
The constructed isotopy has compact support inside that chart, so its support
is disjoint from every unselected intersection. This retains the information
needed to preserve their full germs and repeat the move.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open RankThreeWhitneyModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h 3}

/-- The compact support in the compatible chart misses every other original crossing. -/
theorem RankThreeCompatibleChart.exists_relative_cancellation
    (c : RankThreeCompatibleChart tube) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ c.chart.target ∧
      Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧ ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
        (∀ y, A (0, y) = y) ∧
        (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
        (∀ t y, y ∉ K → A (t, y) = y) ∧
        ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKt, A, hA⟩ := c.exists_cancellation
  refine ⟨K, hK, hKt, ?_, A, hA⟩
  apply Set.disjoint_left.mpr
  intro y hyK hy
  have hc : y ∈ (S ∩ T) ∩ c.chart.target := ⟨hy.1, hKt hyK⟩
  rw [c.intersection_in_target_eq] at hc
  exact hy.2 hc

/-- Constructed cancellation retains support disjointness from the entire remaining crossing set. -/
theorem exists_rankThree_relative_cancellation
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ tube.chart.target ∧
      Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧ ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
        (∀ y, A (0, y) = y) ∧
        (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
        (∀ t y, y ∉ K → A (t, y) = y) ∧
        ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKt, hd, A, hA⟩ := c.exists_relative_cancellation
  exact ⟨K, hK, hKt.trans c.target_subset, hd, A, hA⟩

end Wikipedia.SmoothSixDPoincare.TubularBigon
